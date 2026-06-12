from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from proofstack.agents.ac.council import CouncilMember  # noqa: E402
from proofstack.agents.ac.critic import ACCritic  # noqa: E402
from proofstack.agents.ac.source_trace import ACSourceTrace  # noqa: E402
from proofstack.context import RunContext  # noqa: E402


_CODEX_MODEL = {"api": "codex_cli", "model": "test-model"}


def _text(messages: list[dict]) -> str:
    return json.dumps(messages, ensure_ascii=False)


def test_codex_critic_prompt_and_kwargs_do_not_reference_provider_tools() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        ctx = RunContext.create(
            run_id="test",
            root_workdir=Path(tmp),
            flat=True,
            component_configs={"ACCritic": {"model": _CODEX_MODEL}},
        )
        critic = ACCritic(ctx)

        kwargs = critic.extra_client_kwargs()
        messages = critic.render_messages(
            critic.Inputs(
                problem="Prove X.",
                answer_tex="\\documentclass{article}\\begin{document}X\\end{document}",
            )
        )
        text = _text(messages)

    assert kwargs == {}
    assert "Codex" in text
    assert "code_interpreter" not in text
    assert "code-interpreter" not in text
    assert "web_search_preview" not in text


def test_provider_critic_still_declares_provider_tools() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        ctx = RunContext.create(
            run_id="test",
            root_workdir=Path(tmp),
            flat=True,
            component_configs={
                "ACCritic": {
                    "model": {"api": "openai", "model": "gpt-test"},
                }
            },
        )
        critic = ACCritic(ctx)

        kwargs = critic.extra_client_kwargs()
        messages = critic.render_messages(critic.Inputs(problem="Prove X."))
        text = _text(messages)

    assert [tool[1]["type"] for tool in kwargs["tools"]] == [
        "code_interpreter",
        "web_search_preview",
    ]
    assert "code-interpreter" in text


def test_codex_council_prompt_does_not_reference_provider_tools() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        ctx = RunContext.create(run_id="test", root_workdir=Path(tmp), flat=True)
        member = CouncilMember(ctx, model_ref=_CODEX_MODEL)

        messages = member.render_messages(
            member.Inputs(
                author_question="What approach should we try?",
                answer_tex="answer",
                research_notes_tex="notes",
                references_bib="",
            )
        )
        text = _text(messages)

    assert "Codex CLI" in text
    assert "code_interpreter" not in text
    assert "code-interpreter" not in text
    assert "web_search_preview" not in text


def test_codex_source_trace_prompt_and_kwargs_do_not_reference_provider_tools() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        ctx = RunContext.create(
            run_id="test",
            root_workdir=Path(tmp),
            flat=True,
            component_configs={"ACSourceTrace": {"model": _CODEX_MODEL}},
        )
        auditor = ACSourceTrace(ctx)

        kwargs = auditor.extra_client_kwargs()
        messages = auditor.render_messages(
            auditor.Inputs(problem="Prove X.", answer_tex="Theorem 1 proves X.")
        )
        text = _text(messages)

    assert kwargs == {}
    assert "Codex CLI" in text
    assert "code_interpreter" not in text
    assert "code-interpreter" not in text
    assert "web_search_preview" not in text
