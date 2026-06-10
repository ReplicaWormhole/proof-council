"""Codex CLI backend with the small ``APIClient`` surface ProofCouncil uses.

This is intentionally not a provider SDK wrapper. It shells out to
``codex exec`` using the user's Codex CLI authentication, then adapts the
final message and JSONL usage events to the ``run_queries`` iterator shape
expected by ``APICallAgent``.
"""
from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Iterable

from proofstack.cli_usage import cost_for_codex_usage, parse_codex_jsonl


Message = dict[str, Any]


class CodexExecClient:
    """Use ``codex exec`` as a drop-in client for one-shot prompt agents."""

    def __init__(
        self,
        model: str = "gpt-5.5",
        *,
        reasoning_effort: str | None = None,
        model_reasoning_effort: str | None = None,
        codex_bin: str = "codex",
        cwd: str | Path | None = None,
        timeout: float = 3600.0,
        codex_sandbox: str = "read-only",
        approval_policy: str | None = "never",
        skip_git_repo_check: bool = True,
        json_output: bool = True,
        output_schema: str | Path | None = None,
        persistent_session: bool = False,
        session_state_path: str | Path | None = None,
        extra_args: list[str] | None = None,
        read_cost: float = 0.0,
        write_cost: float = 0.0,
        cache_read_cost: float | None = None,
        **_ignored: Any,
    ) -> None:
        self.model = model
        self.reasoning_effort = model_reasoning_effort or reasoning_effort
        self.codex_bin = codex_bin
        self.cwd = Path(cwd) if cwd is not None else None
        self.timeout = float(timeout)
        self.codex_sandbox = codex_sandbox
        self.approval_policy = approval_policy
        self.skip_git_repo_check = bool(skip_git_repo_check)
        self.json_output = bool(json_output)
        self.output_schema = Path(output_schema) if output_schema is not None else None
        self.persistent_session = bool(persistent_session)
        self.session_state_path = Path(session_state_path) if session_state_path is not None else None
        self.extra_args = list(extra_args or [])
        self.read_cost = float(read_cost or 0.0)
        self.write_cost = float(write_cost or 0.0)
        self.cache_read_cost = None if cache_read_cost is None else float(cache_read_cost)

    def run_queries(self, queries: Iterable[list[Message]], no_tqdm: bool = False):
        del no_tqdm
        for idx, messages in enumerate(queries):
            yield self._run_one(idx, list(messages))

    def _run_one(self, idx: int, messages: list[Message]) -> tuple[int, list[Message], dict[str, Any]]:
        with tempfile.TemporaryDirectory(prefix="proofstack_codex_") as td:
            out_path = Path(td) / "last-message.md"
            cmd = self._build_cmd(out_path)
            prompt = _messages_to_prompt(messages)
            proc = subprocess.run(
                cmd,
                input=prompt,
                capture_output=True,
                text=True,
                cwd=str(self.cwd) if self.cwd is not None else None,
                timeout=self.timeout,
                check=False,
            )
            if proc.returncode != 0:
                raise RuntimeError(
                    "codex exec failed with return code "
                    f"{proc.returncode}: {(proc.stderr or proc.stdout).strip()[:2000]}"
                )
            raw_text = out_path.read_text(encoding="utf-8", errors="replace") if out_path.exists() else proc.stdout
            usage = parse_codex_jsonl(proc.stdout)
            thread_id = _extract_thread_id(proc.stdout)
            if thread_id:
                self._store_thread_id(thread_id)
            cost = cost_for_codex_usage(
                usage,
                read_cost=self.read_cost,
                write_cost=self.write_cost,
                cache_read_cost=self.cache_read_cost,
            )
            detailed_cost = {
                "cost": cost,
                "input_tokens": usage.input_tokens,
                "cached_input_tokens": usage.cached_input_tokens,
                "output_tokens": usage.output_tokens,
                "reasoning_tokens": usage.reasoning_output_tokens,
                "n_turns": usage.n_turns,
                "via": "codex_exec_json",
            }
            return idx, [*messages, {"role": "assistant", "content": raw_text}], detailed_cost

    def _build_cmd(self, out_path: Path) -> list[str]:
        thread_id = self._load_thread_id() if self.persistent_session else None
        is_resume = bool(thread_id)
        if is_resume:
            cmd = [self.codex_bin, "exec", "resume", thread_id]
        else:
            cmd = [self.codex_bin, "exec"]
        if self.model:
            cmd.extend(["-m", self.model])
        if self.reasoning_effort:
            cmd.extend(["-c", f'model_reasoning_effort="{self.reasoning_effort}"'])
        if self.skip_git_repo_check:
            cmd.append("--skip-git-repo-check")
        if self.json_output:
            cmd.append("--json")
        cmd.extend(["--output-last-message", str(out_path)])
        if self.output_schema is not None:
            cmd.extend(["--output-schema", str(self.output_schema)])
        cmd.extend(_sandbox_args(self.codex_sandbox, is_resume=is_resume))
        if self.approval_policy and not is_resume:
            cmd.extend(["--ask-for-approval", self.approval_policy])
        cmd.extend(self.extra_args)
        cmd.append("-")
        return cmd

    def _load_thread_id(self) -> str | None:
        if self.session_state_path is None or not self.session_state_path.exists():
            return None
        try:
            data = json.loads(self.session_state_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return None
        thread_id = data.get("thread_id") if isinstance(data, dict) else None
        return str(thread_id) if thread_id else None

    def _store_thread_id(self, thread_id: str) -> None:
        if self.session_state_path is None:
            return
        self.session_state_path.parent.mkdir(parents=True, exist_ok=True)
        self.session_state_path.write_text(
            json.dumps({"thread_id": thread_id}, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )


def _sandbox_args(mode: str | None, *, is_resume: bool = False) -> list[str]:
    normalized = (mode or "").strip().lower().replace("_", "-")
    if not normalized or normalized == "none":
        return []
    if normalized in {"read-only", "workspace-write", "danger-full-access"}:
        if is_resume:
            return []
        return ["--sandbox", normalized]
    if normalized in {"bypass", "docker-bypass", "dangerously-bypass"}:
        return ["--dangerously-bypass-approvals-and-sandbox"]
    raise ValueError(f"unsupported codex_sandbox mode: {mode!r}")


def _messages_to_prompt(messages: list[Message]) -> str:
    chunks = [
        "You are serving as the model backend for ProofCouncil.",
        "Return only the assistant response for the conversation below.",
        "Do not edit repository files unless the conversation explicitly asks you to.",
        "",
    ]
    for msg in messages:
        role = str(msg.get("role", "user"))
        content = _content_to_text(msg.get("content", ""))
        chunks.append(f"<{role}>")
        chunks.append(content)
        chunks.append(f"</{role}>")
        chunks.append("")
    return "\n".join(chunks).rstrip() + "\n"


def _content_to_text(content: Any) -> str:
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts: list[str] = []
        for block in content:
            if isinstance(block, dict):
                if "text" in block:
                    parts.append(str(block["text"]))
                elif block.get("type") == "output_text":
                    parts.append(str(block.get("text", "")))
            elif isinstance(block, str):
                parts.append(block)
        return "\n".join(part for part in parts if part)
    return str(content)


def _extract_thread_id(stdout_text: str) -> str | None:
    for line in stdout_text.splitlines():
        line = line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            ev = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(ev, dict) or ev.get("type") != "thread.started":
            continue
        for key in ("thread_id", "threadId"):
            value = ev.get(key)
            if value:
                return str(value)
        thread = ev.get("thread")
        if isinstance(thread, dict) and thread.get("id"):
            return str(thread["id"])
    return None


__all__ = ["CodexExecClient"]
