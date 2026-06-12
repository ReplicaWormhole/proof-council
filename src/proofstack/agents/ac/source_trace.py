"""Source-trace auditor for pre-accepted Author/Critic drafts."""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, ClassVar

from pydantic import BaseModel, Field

from proofstack.context import ModelSpec, model_api_name
from proofstack.kinds.api_call import APICallAgent
from proofstack.latex_contract import DEFAULT_FIRSTPROOF_PAGE_LIMIT


PASS_STATUSES = {"cited", "proved", "definition"}
FAIL_STATUSES = {"missing", "unsupported", "ambiguous"}
ALLOWED_STATUSES = PASS_STATUSES | FAIL_STATUSES


SOURCE_TRACE_SYSTEM = """\
You are a source-trace auditor for a mathematical proof workflow.

The Author and mathematical Critic may already agree that the proof is
mathematically pre-accepted. Your stricter job is source traceability:
every atomic logical step in answer.tex must be checkable against exact
published/stable locators or proved directly in answer.tex.

Pass only if every step has status cited, proved, or definition.
Reject broad citations such as "standard", "see Kadison--Ringrose", or
"by a theorem in the literature" unless the answer records an exact
theorem/proposition/lemma/equation/section/page locator. Internet and
lecture-note sources are allowed only when the locator is stable and
specific. If no exact source exists for a step, require an internal
proof and audit that proof recursively.
For status cited, the exact locator must be inline at the logical step
it supports, not collected only in a final "Source trace",
"Justification map", "Source comparison", or "open checks" section.

Return exactly:

<source_trace_json>
{
  "steps": [
    {
      "step_id": "S1",
      "location": "answer.tex, Section 2, paragraph 1",
      "claim": "short claim",
      "depends_on": [],
      "status": "cited",
      "sources": [
        {
          "bibkey": "SourceKey",
          "locator": "Theorem 1.2, p. 34",
          "supports": "what this source supports"
        }
      ],
      "source_placement": "inline",
      "auditor_verdict": "pass"
    }
  ]
}
</source_trace_json>

<source_trace_report>
Human-readable report. List every unsupported, ambiguous, missing, or
broadly cited step with the concrete obligation the Author must fix.
</source_trace_report>

<source_ready>true</source_ready>
or
<source_ready>false</source_ready>
"""


SOURCE_TRACE_SYSTEM_CODEX = SOURCE_TRACE_SYSTEM + """\

You are running through Codex CLI. Use local files, shell, Python,
LaTeX, and any available network/local literature lookup only when it
materially improves the audit. If lookup is unavailable, mark the step
ambiguous or missing rather than inventing a locator.
"""


SOURCE_TRACE_USER = """\
# Problem statement

{problem}

# Round

{round} of {n_rounds}

# Page limit

{page_limit}

# Critic review that triggered the source gate

{critic_review}

# answer.tex

```latex
{answer_tex}
```

# references.bib

```bibtex
{references_bib}
```

# research_notes.tex

Background only. Do not treat this as part of the submitted proof
unless answer.tex cites or imports the relevant material.

```latex
{research_notes_tex}
```
"""


_SOURCE_READY_RE = re.compile(
    r"<source_ready>\s*(true|false)\s*</source_ready>",
    re.IGNORECASE,
)
_TRACE_JSON_RE = re.compile(
    r"<source_trace_json>\s*(?P<body>.*?)\s*</source_trace_json>",
    re.IGNORECASE | re.DOTALL,
)
_TRACE_REPORT_RE = re.compile(
    r"<source_trace_report>\s*(?P<body>.*?)\s*</source_trace_report>",
    re.IGNORECASE | re.DOTALL,
)
_JSON_FENCE_RE = re.compile(r"```(?:json)?\s*(?P<body>[\s\S]*?)```", re.IGNORECASE)
_CITE_RE = re.compile(r"\\[A-Za-z]*cite[A-Za-z*]*\s*(?:\[[^\]]*\]\s*)*\{", re.IGNORECASE)
_LOCATOR_RE = re.compile(
    r"\b(Theorem|Thm\.?|Proposition|Prop\.?|Lemma|Corollary|"
    r"Equation|Eq\.?|Section|Sec\.?|Chapter|Ch\.?|page|p\.)\b",
    re.IGNORECASE,
)
_APPENDIX_SOURCE_SECTION_RE = re.compile(
    r"\\section\*?\{[^}]*?(Source trace|Justification map|Source comparison|open checks)[^}]*?\}"
    r"|\b(Source trace|Justification map|Source comparison and open checks)\b",
    re.IGNORECASE,
)


class SourceTraceParse(BaseModel):
    source_ready: bool = False
    parse_failed: bool = False
    trace: dict[str, Any] = Field(default_factory=dict)
    report_md: str = ""
    failures: list[str] = Field(default_factory=list)


class ACSourceTrace(APICallAgent):
    """Audit exact source/proof support for a candidate final answer."""

    description: ClassVar[str] = (
        "Fail-closed source trace audit requiring every logical step to "
        "be cited with exact locators, proved, or definitional."
    )
    MODEL: ClassVar[ModelSpec] = "models/openai/gpt-55-pro"
    MAX_TOOL_CALLS: ClassVar[int] = 12

    class Inputs(BaseModel):
        problem: str
        round: int = 0
        n_rounds: int = 0
        page_limit: int = DEFAULT_FIRSTPROOF_PAGE_LIMIT
        answer_tex: str = ""
        research_notes_tex: str = ""
        references_bib: str = ""
        critic_review: str = ""

    class Outputs(BaseModel):
        source_ready: bool = False
        parse_failed: bool = False
        trace: dict[str, Any] = Field(default_factory=dict)
        report_md: str = ""
        missing_obligations: str = ""
        raw_text: str = ""

    def extra_client_kwargs(self) -> dict[str, Any]:
        if self._uses_codex_cli():
            return {}
        return {
            "tools": [
                (None, {"type": "web_search_preview"}),
            ],
            "max_tool_calls": self.MAX_TOOL_CALLS,
        }

    def render_messages(self, inp: Inputs) -> list[dict[str, Any]]:
        fields = inp.model_dump(mode="json")
        for key in ("answer_tex", "research_notes_tex", "references_bib", "critic_review"):
            if not fields.get(key):
                fields[key] = "(empty)"
        system = SOURCE_TRACE_SYSTEM_CODEX if self._uses_codex_cli() else SOURCE_TRACE_SYSTEM
        return [
            {"role": "developer", "content": system},
            {"role": "user", "content": SOURCE_TRACE_USER.format(**fields)},
        ]

    def parse_output(self, raw_text: str, inp: Inputs) -> Outputs:
        parsed = parse_source_trace_output(raw_text)
        return self.Outputs(
            source_ready=parsed.source_ready,
            parse_failed=parsed.parse_failed,
            trace=parsed.trace,
            report_md=parsed.report_md,
            missing_obligations=source_trace_obligations(parsed),
            raw_text=raw_text,
        )

    def _uses_codex_cli(self) -> bool:
        if not hasattr(self, "ctx"):
            return False
        spec = self.ctx.model_for(self, self.MODEL)
        return model_api_name(spec) == "codex_cli"


def parse_source_trace_output(raw_text: str) -> SourceTraceParse:
    source_ready, missing_ready_tag = _parse_source_ready(raw_text)
    trace, trace_failures = _parse_trace_json(raw_text)
    report = _parse_report(raw_text)
    failures = list(trace_failures)
    failures.extend(_validate_trace(trace))
    parse_failed = missing_ready_tag or bool(trace_failures)
    return SourceTraceParse(
        source_ready=source_ready and not failures,
        parse_failed=parse_failed,
        trace=trace,
        report_md=report,
        failures=failures,
    )


def source_trace_preflight_reasons(answer_tex: str, references_bib: str) -> list[str]:
    reasons: list[str] = []
    if not answer_tex.strip():
        return ["answer_empty"]
    has_cite = bool(_CITE_RE.search(answer_tex))
    has_locator = bool(_LOCATOR_RE.search(answer_tex))
    if _APPENDIX_SOURCE_SECTION_RE.search(answer_tex):
        reasons.append("appendix_or_final_source_section_present")
    if not (has_cite or has_locator):
        reasons.append("no_source_trace_or_locator_markers")
    if has_cite and not references_bib.strip():
        reasons.append("citations_present_but_references_bib_empty")
    return reasons


def source_trace_obligations(parsed: SourceTraceParse) -> str:
    lines: list[str] = []
    if parsed.parse_failed:
        lines.append(
            "Source trace output was not machine-parseable; rerun the audit or "
            "make the answer include clearer inline exact source locators."
        )
    lines.extend(f"- {failure}" for failure in parsed.failures)
    for step in _trace_steps(parsed.trace):
        status = str(step.get("status") or "").strip().lower()
        if status not in PASS_STATUSES:
            step_id = str(step.get("step_id") or "(unnamed step)")
            claim = str(step.get("claim") or "").strip()
            location = str(step.get("location") or "").strip()
            detail = f"- {step_id}"
            if location:
                detail += f" at {location}"
            if claim:
                detail += f": {claim}"
            detail += f" [{status or 'missing status'}]"
            lines.append(detail)
    return "\n".join(lines)


def render_preflight_source_trace_report(reasons: list[str]) -> str:
    body = ["# Source Trace Gate", "", "The source-trace gate failed before the model audit."]
    body.append("")
    body.append("Reasons:")
    body.extend(f"- {reason}" for reason in reasons)
    body.append("")
    body.append(
        "Add exact theorem/proposition/lemma/equation/section/page locators "
        "inline at the logical steps they support, or prove the steps directly "
        "in answer.tex."
    )
    return "\n".join(body)


def preflight_source_trace(reasons: list[str]) -> ACSourceTrace.Outputs:
    trace = {
        "steps": [],
        "preflight_failures": list(reasons),
    }
    report = render_preflight_source_trace_report(reasons)
    parsed = SourceTraceParse(
        source_ready=False,
        parse_failed=False,
        trace=trace,
        report_md=report,
        failures=list(reasons),
    )
    return ACSourceTrace.Outputs(
        source_ready=False,
        parse_failed=False,
        trace=trace,
        report_md=report,
        missing_obligations=source_trace_obligations(parsed),
        raw_text="",
    )


def write_source_trace_artifacts(
    workspace: Path, out: ACSourceTrace.Outputs, *, round: int
) -> None:
    ac_dir = workspace / ".ac"
    ac_dir.mkdir(parents=True, exist_ok=True)
    artifact = {
        **(out.trace if isinstance(out.trace, dict) else {"steps": []}),
        "source_ready": out.source_ready,
        "parse_failed": out.parse_failed,
        "missing_obligations": out.missing_obligations,
    }
    (ac_dir / "source_trace.json").write_text(
        json.dumps(artifact, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    (ac_dir / "source_trace_report.md").write_text(
        out.report_md or "", encoding="utf-8"
    )
    (ac_dir / f"source-trace-round-{round}.json").write_text(
        out.model_dump_json(indent=2), encoding="utf-8"
    )
    (ac_dir / f"source-trace-round-{round}.md").write_text(
        out.report_md or "", encoding="utf-8"
    )


def _parse_source_ready(raw_text: str) -> tuple[bool, bool]:
    matches = _SOURCE_READY_RE.findall(raw_text)
    if not matches:
        return False, True
    return matches[-1].strip().lower() == "true", False


def _parse_trace_json(raw_text: str) -> tuple[dict[str, Any], list[str]]:
    candidates: list[str] = []
    tagged = _TRACE_JSON_RE.findall(raw_text)
    candidates.extend(tagged)
    candidates.extend(match.group("body") for match in _JSON_FENCE_RE.finditer(raw_text))
    stripped = raw_text.strip()
    if stripped.startswith("{") or stripped.startswith("["):
        candidates.append(stripped)
    if not candidates:
        return {}, ["source_trace_json_missing"]
    failures: list[str] = []
    for candidate in candidates:
        try:
            raw = json.loads(candidate)
        except json.JSONDecodeError as e:
            failures.append(f"source_trace_json_invalid:{e.msg}")
            continue
        if isinstance(raw, list):
            return {"steps": raw}, []
        if isinstance(raw, dict):
            if isinstance(raw.get("steps"), list):
                return raw, []
            return {}, ["source_trace_json_missing_steps"]
        return {}, ["source_trace_json_not_object_or_list"]
    return {}, failures or ["source_trace_json_invalid"]


def _parse_report(raw_text: str) -> str:
    matches = _TRACE_REPORT_RE.findall(raw_text)
    if matches:
        return matches[-1].strip()
    without_json = _TRACE_JSON_RE.sub("", raw_text)
    without_ready = _SOURCE_READY_RE.sub("", without_json)
    return without_ready.strip()


def _validate_trace(trace: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    steps = _trace_steps(trace)
    if not steps:
        failures.append("source_trace_steps_empty")
    for idx, step in enumerate(steps, start=1):
        prefix = str(step.get("step_id") or f"step_{idx}")
        status = str(step.get("status") or "").strip().lower()
        if status not in ALLOWED_STATUSES:
            failures.append(f"{prefix}:invalid_status:{status or '(empty)'}")
            continue
        if status == "cited":
            sources = step.get("sources")
            if not isinstance(sources, list) or not sources:
                failures.append(f"{prefix}:cited_without_sources")
                continue
            placement = str(step.get("source_placement") or "").strip().lower()
            if placement != "inline":
                failures.append(f"{prefix}:source_placement_not_inline")
            for source_idx, source in enumerate(sources, start=1):
                if not isinstance(source, dict):
                    failures.append(f"{prefix}:source_{source_idx}_not_object")
                    continue
                locator = str(source.get("locator") or "").strip()
                if not locator:
                    failures.append(f"{prefix}:source_{source_idx}_empty_locator")
    return failures


def _trace_steps(trace: dict[str, Any]) -> list[dict[str, Any]]:
    steps = trace.get("steps") if isinstance(trace, dict) else None
    if not isinstance(steps, list):
        return []
    return [step for step in steps if isinstance(step, dict)]


__all__ = [
    "ACSourceTrace",
    "ALLOWED_STATUSES",
    "PASS_STATUSES",
    "SourceTraceParse",
    "parse_source_trace_output",
    "preflight_source_trace",
    "render_preflight_source_trace_report",
    "source_trace_obligations",
    "source_trace_preflight_reasons",
    "write_source_trace_artifacts",
]
