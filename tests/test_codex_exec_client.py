from __future__ import annotations

import json
import stat
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from proofstack.codex_exec_client import CodexExecClient  # noqa: E402
from proofstack.context import _default_api_client_factory  # noqa: E402


def _fake_codex(path: Path) -> Path:
    bin_path = path / "codex"
    bin_path.write_text(
        """#!/bin/sh
set -eu
printf '%s\\n' "$@" > args.txt
out=""
while [ "$#" -gt 0 ]; do
  if [ "$1" = "--output-last-message" ]; then
    shift
    out="$1"
  fi
  shift || true
done
payload="$(cat)"
printf 'final from fake codex\\n%s\\n' "$payload" > "$out"
printf '{"type":"thread.started","thread_id":"thread-123"}\\n'
printf '{"type":"turn.completed","usage":{"input_tokens":10,"cached_input_tokens":4,"output_tokens":3,"reasoning_output_tokens":2}}\\n'
""",
        encoding="utf-8",
    )
    bin_path.chmod(bin_path.stat().st_mode | stat.S_IXUSR)
    return bin_path


def test_codex_exec_client_adapts_final_message_and_usage() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        fake = _fake_codex(root)
        session_path = root / "session.json"
        client = CodexExecClient(
            model="test-model",
            reasoning_effort="high",
            codex_bin=str(fake),
            cwd=root,
            timeout=5,
            codex_sandbox="read-only",
            persistent_session=True,
            session_state_path=session_path,
            read_cost=2.5,
            cache_read_cost=0.25,
            write_cost=15,
        )

        idx, conversation, cost = next(iter(client.run_queries([[{"role": "user", "content": "prove x"}]])))

        args = (root / "args.txt").read_text(encoding="utf-8").splitlines()
        assert idx == 0
        assert args[:2] == ["exec", "-m"]
        assert "--json" in args
        assert "--output-last-message" in args
        assert conversation[-1]["role"] == "assistant"
        assert "prove x" in conversation[-1]["content"]
        assert cost["input_tokens"] == 10
        assert cost["cached_input_tokens"] == 4
        assert cost["output_tokens"] == 3
        assert cost["reasoning_tokens"] == 2
        assert cost["cost"] == ((6 * 2.5) + (4 * 0.25) + (3 * 15)) / 1_000_000
        assert json.loads(session_path.read_text(encoding="utf-8")) == {"thread_id": "thread-123"}


def test_codex_exec_client_resumes_recorded_thread() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        fake = _fake_codex(root)
        session_path = root / "session.json"
        session_path.write_text(json.dumps({"thread_id": "thread-existing"}), encoding="utf-8")
        client = CodexExecClient(
            model="test-model",
            codex_bin=str(fake),
            cwd=root,
            timeout=5,
            persistent_session=True,
            session_state_path=session_path,
        )

        next(iter(client.run_queries([[{"role": "user", "content": "continue"}]])))

        args = (root / "args.txt").read_text(encoding="utf-8").splitlines()
        assert args[:3] == ["exec", "resume", "thread-existing"]
        assert "--sandbox" not in args
        assert "--ask-for-approval" not in args


def test_default_factory_returns_codex_client_for_codex_cli_api() -> None:
    client = _default_api_client_factory(
        {
            "api": "codex_cli",
            "model": "test-model",
            "codex_bin": "codex",
        }
    )

    assert isinstance(client, CodexExecClient)
    assert client.model == "test-model"
