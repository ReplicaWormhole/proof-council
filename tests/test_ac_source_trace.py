from __future__ import annotations

import asyncio
import json
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from proofstack.agents.ac.ac_workflow import ACWorkflow  # noqa: E402
from proofstack.agents.ac.author import Author  # noqa: E402
from proofstack.agents.ac.critic import ACCritic  # noqa: E402
from proofstack.agents.ac.source_trace import (  # noqa: E402
    parse_source_trace_output,
    source_trace_preflight_reasons,
)
from proofstack.agents.ac.lamport import (  # noqa: E402
    ACLamportRewriter,
    write_lamport_artifacts,
)
from proofstack.agents.ac.visual_blocks import ACSourceTraceBlock  # noqa: E402
from proofstack.context import RunContext  # noqa: E402


def test_parse_source_trace_output_passes_cited_step_with_locator() -> None:
    raw = """
<source_trace_json>
{"steps":[{"step_id":"S1","location":"Sec. 1","claim":"C","depends_on":[],"status":"cited","sources":[{"bibkey":"K","locator":"Theorem 1.2, p. 3","supports":"C"}],"source_placement":"inline","auditor_verdict":"pass"}]}
</source_trace_json>
<source_trace_report>
All steps are traceable.
</source_trace_report>
<source_ready>true</source_ready>
"""

    parsed = parse_source_trace_output(raw)

    assert parsed.source_ready is True
    assert parsed.parse_failed is False
    assert parsed.failures == []
    assert parsed.trace["steps"][0]["step_id"] == "S1"


def test_parse_source_trace_output_rejects_empty_locator() -> None:
    raw = """
<source_trace_json>
{"steps":[{"step_id":"S1","status":"cited","sources":[{"bibkey":"K","locator":"","supports":"C"}],"source_placement":"inline"}]}
</source_trace_json>
<source_trace_report>Bad locator.</source_trace_report>
<source_ready>true</source_ready>
"""

    parsed = parse_source_trace_output(raw)

    assert parsed.source_ready is False
    assert parsed.parse_failed is False
    assert "S1:source_1_empty_locator" in parsed.failures


def test_source_trace_preflight_rejects_source_light_answer() -> None:
    reasons = source_trace_preflight_reasons(
        r"\documentclass{article}\begin{document}A proof.\end{document}",
        "",
    )

    assert reasons == ["no_source_trace_or_locator_markers"]


def test_source_trace_preflight_rejects_final_source_section() -> None:
    reasons = source_trace_preflight_reasons(
        r"\documentclass{article}\begin{document}Proof.\section*{Source trace}By Theorem 1.2.\end{document}",
        "",
    )

    assert reasons == ["appendix_or_final_source_section_present"]


def test_parse_source_trace_output_rejects_non_inline_placement() -> None:
    raw = """
<source_trace_json>
{"steps":[{"step_id":"S1","status":"cited","sources":[{"bibkey":"K","locator":"Theorem 1","supports":"C"}],"source_placement":"appendix"}]}
</source_trace_json>
<source_trace_report>Not inline.</source_trace_report>
<source_ready>true</source_ready>
"""

    parsed = parse_source_trace_output(raw)

    assert parsed.source_ready is False
    assert "S1:source_placement_not_inline" in parsed.failures


def test_source_trace_block_preflight_writes_artifacts_and_feedback() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        ctx = RunContext.create(run_id="run", root_workdir=root, flat=True)

        async def noop_event_write(event):
            return None

        ctx.events.sink.write = noop_event_write  # type: ignore[method-assign]
        workspace = root / "ac_workspaces" / "p"
        workspace.mkdir(parents=True)
        (workspace / "answer.tex").write_text("source-light proof", encoding="utf-8")
        (workspace / "research_notes.tex").write_text("", encoding="utf-8")
        (workspace / "references.bib").write_text("", encoding="utf-8")
        author = Author.Outputs(
            answer_tex="source-light proof",
            research_notes_tex="",
            references_bib="",
            ready=True,
        )
        review = ACCritic.Outputs(
            review_md="accepted",
            answer_ready=True,
            mode="fresh",
            messages_after=[],
        )
        state = {
            "inputs": ACWorkflow.Inputs(problem="P", problem_id="p").model_dump(mode="json"),
            "workspace": str(workspace),
            "current_round": 1,
            "current_author": author.model_dump(mode="json"),
            "round_review": review.model_dump(mode="json"),
            "review_for_gate": review.model_dump(mode="json"),
            "pending_workflow_feedback": "",
        }

        block = ACSourceTraceBlock(ctx)
        out = asyncio.run(block(state=state, ready=True))

        assert out.source_ready is False
        assert out.ready_for_gate is False
        assert "Source Trace Gate" in out.state["pending_workflow_feedback"]
        artifact = json.loads(
            (workspace / ".ac" / "source_trace.json").read_text(encoding="utf-8")
        )
        assert artifact["source_ready"] is False
        assert artifact["preflight_failures"] == ["no_source_trace_or_locator_markers"]
        assert (workspace / ".ac" / "source_trace_report.md").exists()


def test_lamport_rewriter_parses_file_and_writes_artifacts() -> None:
    raw = """
```file path=lamport_proof.tex
\\documentclass{article}
\\begin{document}
1. Claim: C. Depends on: none. Justification: internal. Status: validated.
\\end{document}
```

<lamport_report>
No tainted nodes.
</lamport_report>

<lamport_ready>true</lamport_ready>
"""
    rewriter = ACLamportRewriter.__new__(ACLamportRewriter)

    out = rewriter.parse_output(raw, ACLamportRewriter.Inputs(problem="P"))

    assert out.lamport_ready is True
    assert out.parse_failed is False
    assert "Status: validated" in out.lamport_tex
    with tempfile.TemporaryDirectory() as tmp:
        workspace = Path(tmp)
        tex_path = workspace / "solutions" / "p-lamport.tex"
        write_lamport_artifacts(
            workspace,
            out,
            tex_path=tex_path,
            compiled=True,
            pages=1,
        )
        artifact = json.loads(
            (workspace / ".ac" / "lamport_rewrite.json").read_text(encoding="utf-8")
        )
        assert artifact["lamport_ready"] is True
        assert artifact["compiled"] is True
        assert (workspace / "lamport_proof.tex").exists()
