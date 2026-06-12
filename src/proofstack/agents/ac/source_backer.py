"""Post-acceptance source annotator for pre-accepted proofs."""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, ClassVar

from pydantic import BaseModel, Field

from proofstack.agents.ac.blocks import parse_author_output
from proofstack.context import ModelSpec, model_api_name
from proofstack.kinds.api_call import APICallAgent
from proofstack.latex_contract import DEFAULT_FIRSTPROOF_PAGE_LIMIT


SOURCE_BACKER_SYSTEM = """\
You are the source-backing stage of a mathematical proof workflow.

The Author and Critic have pre-accepted answer.tex mathematically. Your
job is not to improve the proof. Your job is to attach exact source
support to the existing proof after pre-acceptance.

Rules:
- Preserve the mathematical content, theorem statements, proof order,
  equations, hypotheses, and conclusions. Do not repair the proof here.
- Only add inline source support, citation commands, parenthetical
  exact locators, and BibTeX entries. Minor wording changes are allowed
  only when needed to attach a locator without changing the claim.
- Put source support directly next to the logical step it supports,
  e.g. "by \\cite[Theorem 1.2, p. 34]{Key}" or
  "(by Key, Theorem 1.2, p. 34)". Do not collect support in a final
  "Source trace", "Justification map", "Source comparison", or
  "open checks" section.
- Every externally sourced theorem, reduction, identification,
  equivalence, limiting argument, and algebraic claim should either
  receive an exact theorem/proposition/lemma/equation/section/page
  locator or already be proved directly in answer.tex.
- If you cannot source-back every external step, still make the best
  safe inline additions and set <source_backed>false</source_backed>.

Return only:

```file path=answer.tex
full updated answer.tex
```

```file path=references.bib
full updated references.bib
```

<source_backing_report>
Short report. List any step that could not be source-backed without
changing the proof.
</source_backing_report>

<source_backed>true</source_backed>
or
<source_backed>false</source_backed>
"""


SOURCE_BACKER_SYSTEM_CODEX = SOURCE_BACKER_SYSTEM + """\

You are running through Codex CLI. Use local files, shell, Python,
LaTeX, and any available network/local literature lookup only when it
materially improves exact locators. If lookup is unavailable, leave a
clear obligation in the report rather than inventing a locator.
"""


SOURCE_BACKER_USER = """\
# Problem statement

{problem}

# Round

{round} of {n_rounds}

# Page limit

{page_limit}

# Critic review that pre-accepted the proof mathematically

{critic_review}

# Source-trace feedback from a prior source-backing attempt

{source_feedback}

# answer.tex

```latex
{answer_tex}
```

# references.bib

```bibtex
{references_bib}
```

# research_notes.tex

Background only. You may use this to find source leads, but do not
import new proof content into answer.tex.

```latex
{research_notes_tex}
```
"""


_SOURCE_BACKED_RE = re.compile(
    r"<source_backed>\s*(true|false)\s*</source_backed>",
    re.IGNORECASE,
)
_SOURCE_BACKING_REPORT_RE = re.compile(
    r"<source_backing_report>\s*(?P<body>.*?)\s*</source_backing_report>",
    re.IGNORECASE | re.DOTALL,
)


class ACSourceBacker(APICallAgent):
    """Insert inline source locators after mathematical pre-acceptance."""

    description: ClassVar[str] = (
        "Post-acceptance source annotator that may only add inline "
        "source support and bibliography entries."
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
        source_feedback: str = ""

    class Outputs(BaseModel):
        answer_tex: str = ""
        references_bib: str = ""
        source_backed: bool = False
        parse_failed: bool = False
        report_md: str = ""
        files_changed: list[str] = Field(default_factory=list)
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
        for key in (
            "answer_tex",
            "research_notes_tex",
            "references_bib",
            "critic_review",
            "source_feedback",
        ):
            if not fields.get(key):
                fields[key] = "(empty)"
        system = SOURCE_BACKER_SYSTEM_CODEX if self._uses_codex_cli() else SOURCE_BACKER_SYSTEM
        return [
            {"role": "developer", "content": system},
            {"role": "user", "content": SOURCE_BACKER_USER.format(**fields)},
        ]

    def parse_output(self, raw_text: str, inp: Inputs) -> Outputs:
        parsed = parse_author_output(raw_text)
        answer_tex = parsed.files.get("answer.tex", inp.answer_tex)
        references_bib = parsed.files.get("references.bib", inp.references_bib)
        source_backed, missing_tag = _parse_source_backed(raw_text)
        parse_failed = missing_tag or "answer.tex" not in parsed.files
        return self.Outputs(
            answer_tex=answer_tex,
            references_bib=references_bib,
            source_backed=source_backed and not parse_failed,
            parse_failed=parse_failed,
            report_md=_parse_source_backing_report(raw_text),
            files_changed=sorted(
                name
                for name in ("answer.tex", "references.bib")
                if name in parsed.files
            ),
            raw_text=raw_text,
        )

    def _uses_codex_cli(self) -> bool:
        if not hasattr(self, "ctx"):
            return False
        spec = self.ctx.model_for(self, self.MODEL)
        return model_api_name(spec) == "codex_cli"


def _parse_source_backed(raw_text: str) -> tuple[bool, bool]:
    matches = _SOURCE_BACKED_RE.findall(raw_text)
    if not matches:
        return False, True
    return matches[-1].strip().lower() == "true", False


def _parse_source_backing_report(raw_text: str) -> str:
    matches = _SOURCE_BACKING_REPORT_RE.findall(raw_text)
    if matches:
        return matches[-1].strip()
    without_tag = _SOURCE_BACKED_RE.sub("", raw_text)
    return without_tag.strip()


def write_source_backer_artifacts(
    workspace: Path, out: ACSourceBacker.Outputs, *, round: int
) -> None:
    ac_dir = workspace / ".ac"
    ac_dir.mkdir(parents=True, exist_ok=True)
    artifact = {
        "source_backed": out.source_backed,
        "parse_failed": out.parse_failed,
        "files_changed": out.files_changed,
        "report_md": out.report_md,
    }
    (ac_dir / "source_backer.json").write_text(
        json.dumps(artifact, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    (ac_dir / "source_backer_report.md").write_text(
        out.report_md or "", encoding="utf-8"
    )
    (ac_dir / f"source-backer-round-{round}.json").write_text(
        out.model_dump_json(indent=2), encoding="utf-8"
    )
    (ac_dir / f"source-backer-round-{round}.md").write_text(
        out.report_md or "", encoding="utf-8"
    )


__all__ = [
    "ACSourceBacker",
    "SOURCE_BACKER_SYSTEM",
    "SOURCE_BACKER_SYSTEM_CODEX",
    "write_source_backer_artifacts",
]
