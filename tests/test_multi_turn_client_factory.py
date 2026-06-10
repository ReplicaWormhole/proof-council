from __future__ import annotations

import asyncio
import stat
import sys
import tempfile
from pathlib import Path

from pydantic import BaseModel

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from proofstack.context import RunContext  # noqa: E402
from proofstack.kinds.multi_turn import MultiTurnAgent  # noqa: E402


class _FinalClient:
    model = "factory-client"

    def run_queries(self, queries, no_tqdm=False):
        messages = list(queries[0])
        yield (
            0,
            [*messages, {"role": "assistant", "content": "final via factory"}],
            {"cost": 0.0, "input_tokens": 2, "output_tokens": 3},
        )


def _echo_tool(value: str) -> str:
    """Echo a value."""
    return value


class _FactoryMultiTurn(MultiTurnAgent):
    MODEL = {"api": "codex_cli", "model": "test-model", "__source": "ignored"}
    MAX_STEPS = 5
    USER_PROMPT = "Solve {problem}"

    class Inputs(BaseModel):
        problem: str

    class Outputs(BaseModel):
        answer: str

    @property
    def tools(self):
        return [_echo_tool]

    def extra_client_kwargs(self):
        return {"timeout": 17}


def _fake_codex(path: Path) -> Path:
    bin_path = path / "codex"
    bin_path.write_text(
        """#!/bin/sh
set -eu
out=""
while [ "$#" -gt 0 ]; do
  if [ "$1" = "--output-last-message" ]; then
    shift
    out="$1"
  fi
  shift || true
done
payload="$(cat)"
printf 'multiturn codex final\\n%s\\n' "$payload" > "$out"
printf '{"type":"thread.started","thread_id":"thread-multiturn"}\\n'
printf '{"type":"turn.completed","usage":{"input_tokens":8,"cached_input_tokens":2,"output_tokens":5,"reasoning_output_tokens":1}}\\n'
""",
        encoding="utf-8",
    )
    bin_path.chmod(bin_path.stat().st_mode | stat.S_IXUSR)
    return bin_path


def test_multi_turn_agent_delegates_merged_config_to_context_factory() -> None:
    captured = []
    with tempfile.TemporaryDirectory() as tmp:
        ctx = RunContext.create(
            run_id="test",
            root_workdir=Path(tmp),
            flat=True,
            api_client_factory=lambda cfg: captured.append(cfg) or _FinalClient(),
        )
        agent = _FactoryMultiTurn(ctx, name="solver")

        out = asyncio.run(agent(problem="P"))

    assert out.answer == "final via factory"
    assert len(captured) == 1
    cfg = captured[0]
    assert cfg["api"] == "codex_cli"
    assert cfg["model"] == "test-model"
    assert "__source" not in cfg
    assert cfg["max_tool_calls"] == 5
    assert cfg["timeout"] == 17
    assert len(cfg["tools"]) == 1
    assert cfg["tools"][0][1]["function"]["name"] == "_echo_tool"
    assert callable(cfg["tools"][0][0])


def test_multi_turn_agent_can_use_codex_cli_model_config() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        fake = _fake_codex(root)

        class CodexMultiTurn(MultiTurnAgent):
            MODEL = {
                "api": "codex_cli",
                "model": "test-model",
                "codex_bin": str(fake),
                "cwd": root,
                "timeout": 5,
                "codex_sandbox": "read-only",
            }
            USER_PROMPT = "Solve {problem}"

            class Inputs(BaseModel):
                problem: str

            class Outputs(BaseModel):
                answer: str

        ctx = RunContext.create(run_id="test", root_workdir=root / "run", flat=True)
        agent = CodexMultiTurn(ctx, name="solver")

        out = asyncio.run(agent(problem="P"))

    assert "multiturn codex final" in out.answer
    assert "Solve P" in out.answer
