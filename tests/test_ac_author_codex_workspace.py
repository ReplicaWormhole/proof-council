from __future__ import annotations

import asyncio
import sys
import tempfile
import types
from pathlib import Path
from unittest.mock import MagicMock

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

# --- stub external deps so project modules import cleanly ----------------

if "anthropic" not in sys.modules:
    anthropic = types.ModuleType("anthropic")
    anthropic.NOT_GIVEN = object()
    anthropic.Anthropic = object
    sys.modules["anthropic"] = anthropic

    anthropic_types = types.ModuleType("anthropic.types")
    anthropic_types.TextBlock = type("TextBlock", (), {})
    anthropic_types.ThinkingBlock = type("ThinkingBlock", (), {})
    sys.modules["anthropic.types"] = anthropic_types

    msg_params = types.ModuleType("anthropic.types.message_create_params")
    msg_params.MessageCreateParamsNonStreaming = dict
    sys.modules["anthropic.types.message_create_params"] = msg_params

    batch_params = types.ModuleType("anthropic.types.messages.batch_create_params")
    batch_params.Request = dict
    sys.modules["anthropic.types.messages.batch_create_params"] = batch_params

if "openai" not in sys.modules:
    openai = types.ModuleType("openai")
    openai.OpenAI = MagicMock(side_effect=AssertionError("OpenAI must not be used"))
    openai.RateLimitError = RuntimeError
    sys.modules["openai"] = openai

if "together" not in sys.modules:
    together = types.ModuleType("together")
    together.Together = object
    sys.modules["together"] = together

if "transformers" not in sys.modules:
    transformers = types.ModuleType("transformers")
    transformers.AutoTokenizer = object
    sys.modules["transformers"] = transformers

if "loguru" not in sys.modules:
    loguru = types.ModuleType("loguru")
    loguru.logger = MagicMock()
    sys.modules["loguru"] = loguru

from proofstack.agents.ac.author import Author  # noqa: E402
from proofstack.context import RunContext  # noqa: E402


class _WorkspaceEditingClient:
    model = "fake-codex-author"

    def __init__(self, cfg):
        self.cfg = cfg

    def run_queries(self, queries, no_tqdm=False):
        workspace = Path(self.cfg["cwd"])
        (workspace / "answer.tex").write_text(
            "\\documentclass{article}\\begin{document}Solved.\\end{document}\n",
            encoding="utf-8",
        )
        (workspace / "research_notes.tex").write_text("Notes from Codex.\n", encoding="utf-8")
        (workspace / "references.bib").write_text("@misc{x,title={X}}\n", encoding="utf-8")
        messages = list(queries[0])
        yield (
            0,
            [*messages, {"role": "assistant", "content": "Summary.\n<ready>true</ready>"}],
            {"cost": 0.0, "input_tokens": 4, "output_tokens": 2, "reasoning_tokens": 1},
        )


def test_author_codex_workspace_reads_modified_local_files_without_openai() -> None:
    captured = []
    with tempfile.TemporaryDirectory() as tmp:
        def factory(cfg):
            captured.append(cfg)
            return _WorkspaceEditingClient(cfg)

        ctx = RunContext.create(
            run_id="test_author_codex",
            root_workdir=Path(tmp),
            flat=True,
            api_client_factory=factory,
            component_configs={
                "Author": {
                    "file_io_mode": "codex_workspace",
                    "model": {
                        "api": "codex_cli",
                        "model": "test-model",
                        "codex_sandbox": "read-only",
                    },
                }
            },
        )
        author = Author(ctx)

        out = asyncio.run(author(problem="Prove X.", round=0, n_rounds=1))

        events = (Path(tmp) / "events.jsonl").read_text(encoding="utf-8")
        prompt_text = "\n".join(
            path.read_text(encoding="utf-8")
            for path in Path(tmp).rglob("messages.json")
        )

    assert len(captured) == 1
    assert captured[0]["api"] == "codex_cli"
    assert captured[0]["codex_sandbox"] == "workspace-write"
    assert Path(captured[0]["cwd"]).name == "codex_workspace"
    assert out.via == "codex_workspace"
    assert out.ready is True
    assert out.answer_tex.startswith("\\documentclass")
    assert out.research_notes_tex == "Notes from Codex.\n"
    assert out.references_bib.startswith("@misc")
    assert out.files_changed == ["answer.tex", "references.bib", "research_notes.tex"]
    assert '"via": "codex_workspace"' in events
    assert "code_interpreter" not in prompt_text
    assert "web_search_preview" not in prompt_text


def test_author_codex_workspace_rejects_non_codex_model_config() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        ctx = RunContext.create(
            run_id="test_author_codex_rejects_api",
            root_workdir=Path(tmp),
            flat=True,
            api_client_factory=lambda _cfg: _WorkspaceEditingClient(_cfg),
            component_configs={
                "Author": {
                    "file_io_mode": "codex_workspace",
                    "model": {"api": "openai", "model": "gpt-test"},
                }
            },
        )
        author = Author(ctx)

        with pytest.raises(ValueError, match="api: codex_cli"):
            asyncio.run(author(problem="Prove X.", round=0, n_rounds=1))
