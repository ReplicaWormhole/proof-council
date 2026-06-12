"""Post-acceptance Lamport-style proof rewriter."""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, ClassVar

from pydantic import BaseModel, Field

from proofstack.context import ModelSpec, model_api_name
from proofstack.kinds.api_call import APICallAgent
from proofstack.latex_contract import DEFAULT_FIRSTPROOF_PAGE_LIMIT


LAMPORT_REWRITE_SYSTEM = """\
You rewrite an already accepted mathematical proof into a
Vibefeld/Lamport-style rigorous argument.

The proof has already passed the Author/Critic gate, source-backing
stage, source-trace audit, and deterministic compile/page gate. Do not
change the theorem being proved. Produce a new standalone LaTeX file
named lamport_proof.tex.

Hard requirements for lamport_proof.tex:
1. State the main claim precisely at node 1.
2. List all definitions, hypotheses, conventions, and ambient
   assumptions before the proof tree.
3. Use a hierarchical proof tree with numbered nodes: 1, 1.1, 1.1.1,
   1.2, and so on.
4. Every node must include exactly these fields:
   Claim:
   Depends on:
   Justification:
   Status: validated / needs_refinement / admitted / refuted
5. Do not use "clearly", "obviously", "standard", or "well known"
   unless the statement is proved, explicitly cited, or marked admitted.
6. Mark any unproved external theorem as:
   Status: admitted
   Taint: self_admitted
   and mark every later node depending on it as tainted.
7. Track local assumptions and discharge points explicitly for
   contradiction, induction, arbitrary choices, dense subalgebras,
   finite-volume approximations, limiting arguments, and similar moves.
8. After the proof tree, add an adversarial verifier section classifying
   objections as CRITICAL, MAJOR, MINOR, or NOTE.
9. Then add a revised proof section resolving verifier objections by
   refining weak nodes into subnodes.
10. End with a final audit listing clean nodes, tainted nodes, admitted
    facts, remaining unresolved issues, and final status of the main
    claim.

Source-comparison requirement:
- Every logical step externally justified and not proved inside
  lamport_proof.tex must include a source comparison directly in that
  node's Justification field.
- A source comparison must name the source key, exact locator
  (theorem/proposition/lemma/equation/section/page), and a short
  statement of what the source says versus what this node needs.
- Do not rely on a final bibliography, broad reference, or source list
  to justify a node. The comparison must be local to the node.
- If a needed source comparison cannot be made exactly, mark that node
  Status: admitted, add Taint: self_admitted, and propagate taint.

Return only:

```file path=lamport_proof.tex
full standalone LaTeX document
```

<lamport_report>
Short report covering any admitted facts, tainted nodes, unresolved
issues, and whether every external step has a local source comparison.
</lamport_report>

<lamport_ready>true</lamport_ready>
or
<lamport_ready>false</lamport_ready>
"""


LAMPORT_REWRITE_SYSTEM_CODEX = LAMPORT_REWRITE_SYSTEM + """\

You are running through Codex CLI. Use local files, shell, Python,
LaTeX, and available local/network literature lookup only when needed
to verify exact source comparisons. If lookup is unavailable, mark the
node admitted rather than inventing a locator.
"""


LAMPORT_REWRITE_USER = """\
# Problem statement

{problem}

# Page limit for the canonical accepted proof

{page_limit}

# Accepted answer.tex

```latex
{answer_tex}
```

# references.bib

```bibtex
{references_bib}
```

# Source-trace JSON

```json
{source_trace_json}
```

# Source-trace report

{source_trace_report}
"""


_LAMPORT_READY_RE = re.compile(
    r"<lamport_ready>\s*(true|false)\s*</lamport_ready>",
    re.IGNORECASE,
)
_LAMPORT_REPORT_RE = re.compile(
    r"<lamport_report>\s*(?P<body>.*?)\s*</lamport_report>",
    re.IGNORECASE | re.DOTALL,
)
_LAMPORT_FILE_RE = re.compile(
    r"```file\s+path=lamport_proof\.tex\s*\n(?P<body>.*?)\n```",
    re.IGNORECASE | re.DOTALL,
)


class ACLamportRewriter(APICallAgent):
    """Rewrite accepted proofs into source-comparison Lamport form."""

    description: ClassVar[str] = (
        "Post-acceptance Lamport proof rewriter with local source comparisons."
    )
    MODEL: ClassVar[ModelSpec] = "models/openai/gpt-55-pro"
    MAX_TOOL_CALLS: ClassVar[int] = 12

    class Inputs(BaseModel):
        problem: str
        page_limit: int = DEFAULT_FIRSTPROOF_PAGE_LIMIT
        answer_tex: str = ""
        references_bib: str = ""
        source_trace_json: str = ""
        source_trace_report: str = ""

    class Outputs(BaseModel):
        lamport_tex: str = ""
        lamport_ready: bool = False
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
            "references_bib",
            "source_trace_json",
            "source_trace_report",
        ):
            if not fields.get(key):
                fields[key] = "(empty)"
        system = (
            LAMPORT_REWRITE_SYSTEM_CODEX
            if self._uses_codex_cli()
            else LAMPORT_REWRITE_SYSTEM
        )
        return [
            {"role": "developer", "content": system},
            {"role": "user", "content": LAMPORT_REWRITE_USER.format(**fields)},
        ]

    def parse_output(self, raw_text: str, inp: Inputs) -> Outputs:
        lamport_tex = _parse_lamport_tex(raw_text)
        lamport_ready, missing_tag = _parse_lamport_ready(raw_text)
        parse_failed = missing_tag or not lamport_tex
        return self.Outputs(
            lamport_tex=lamport_tex,
            lamport_ready=lamport_ready and not parse_failed,
            parse_failed=parse_failed,
            report_md=_parse_lamport_report(raw_text),
            files_changed=["lamport_proof.tex"] if lamport_tex else [],
            raw_text=raw_text,
        )

    def _uses_codex_cli(self) -> bool:
        if not hasattr(self, "ctx"):
            return False
        spec = self.ctx.model_for(self, self.MODEL)
        return model_api_name(spec) == "codex_cli"


def _parse_lamport_ready(raw_text: str) -> tuple[bool, bool]:
    matches = _LAMPORT_READY_RE.findall(raw_text)
    if not matches:
        return False, True
    return matches[-1].strip().lower() == "true", False


def _parse_lamport_tex(raw_text: str) -> str:
    matches = list(_LAMPORT_FILE_RE.finditer(raw_text))
    if not matches:
        return ""
    return matches[-1].group("body")


def _parse_lamport_report(raw_text: str) -> str:
    matches = _LAMPORT_REPORT_RE.findall(raw_text)
    if matches:
        return matches[-1].strip()
    without_tag = _LAMPORT_READY_RE.sub("", raw_text)
    return without_tag.strip()


def write_lamport_artifacts(
    workspace: Path,
    out: ACLamportRewriter.Outputs,
    *,
    tex_path: Path | None = None,
    compiled: bool = False,
    pages: int = 0,
) -> None:
    ac_dir = workspace / ".ac"
    ac_dir.mkdir(parents=True, exist_ok=True)
    artifact = {
        "lamport_ready": out.lamport_ready,
        "parse_failed": out.parse_failed,
        "files_changed": out.files_changed,
        "report_md": out.report_md,
        "tex_path": str(tex_path) if tex_path is not None else None,
        "compiled": compiled,
        "pages": pages,
    }
    (ac_dir / "lamport_rewrite.json").write_text(
        json.dumps(artifact, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    (ac_dir / "lamport_rewrite_report.md").write_text(
        out.report_md or "", encoding="utf-8"
    )
    if out.lamport_tex:
        (workspace / "lamport_proof.tex").write_text(
            out.lamport_tex, encoding="utf-8"
        )


__all__ = [
    "ACLamportRewriter",
    "LAMPORT_REWRITE_SYSTEM",
    "LAMPORT_REWRITE_SYSTEM_CODEX",
    "write_lamport_artifacts",
]
