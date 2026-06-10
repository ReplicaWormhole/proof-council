# Codex-First Handoff

## Current State

Branch: `codex-first`

The branch has three Codex-first increments:

- `190483f Add Codex CLI backend`
- `e347bdc Add Codex workspace author mode`
- `0e426a4 Use Codex-local prompts for Codex workflows`

The current system can run ordinary prompt-style model calls through
`codex exec` by selecting a model config with `api: codex_cli`. The main
adapter is `src/proofstack/codex_exec_client.py`. It implements the small
`run_queries(...)` surface expected by existing prompt agents and converts
Codex JSONL usage output into ProofCouncil cost/accounting records.

Author/Critic has a Codex-first smoke preset at:

- `configs/workflows/codex_author_critic_smoke.yaml`

In that preset:

- `Author` uses `file_io_mode: codex_workspace`.
- The Author writes `answer.tex`, `research_notes.tex`, and
  `references.bib` into a local per-call workspace.
- The Author runs through Codex CLI with `workspace-write`.
- Modified canonical files are read back from disk.
- Critic and Council use Codex-local prompt variants and do not request
  OpenAI provider tools such as `code_interpreter` or `web_search_preview`.

The legacy provider-backed paths remain available:

- `mathagents.APIClient`
- OpenAI/Anthropic/Gemini model configs
- Author `container_files` mode
- OpenAI hosted `code_interpreter` / `web_search_preview` tool descriptors

## Bottlenecks and Issues Observed

The largest architectural issue is that ProofCouncil still treats a
"model call" as an `APIClient.run_queries(...)` operation. Codex is not
really that. Codex is closer to "run an agent in a local workspace." The
current implementation works by adapting Codex into the old API-shaped
interface, but that should be considered a compatibility layer, not the
ideal long-term architecture.

Specific problems:

- `CodexExecClient` flattens structured messages into one prompt. This
  loses native conversation and tool semantics.
- `Author` is too large. It now contains inline mode, OpenAI container
  mode, and Codex local workspace mode in one class.
- Tool/capability knowledge is still partly prompt-level branching.
  Critic and Council now handle Codex correctly, but backend capability
  detection should be centralized.
- Cost accounting is semantically mismatched for Codex subscription use.
  The current cost numbers are token-price estimates, not actual API
  billing.
- Codex session persistence is minimal. The client can resume a thread,
  but there is no full per-agent/per-run session manager with locking,
  ownership, cleanup, and observability.
- Critic and Council still paste full file contents into prompts. A more
  native Codex design would materialize files into a local workspace and
  ask Codex to inspect them from disk.
- Real end-to-end Codex smoke coverage should be opt-in but explicit.
  Current tests mostly use fake clients and fake Codex binaries.

## Refactor Direction

Recommended refactors:

1. Introduce a real backend abstraction:
   - `ModelBackend`
   - `APIBackend`
   - `CodexBackend`

2. Split Author file exchange into strategy objects:
   - `InlineAuthorWorkspace`
   - `OpenAIContainerWorkspace`
   - `CodexLocalWorkspace`

3. Move capability detection out of agents and prompts. Backends should
   declare capabilities such as:
   - `local_shell`
   - `workspace_write`
   - `hosted_python`
   - `hosted_web_search`
   - `network`

4. Keep `CodexExecClient` as a compatibility adapter, but avoid building
   new code around the fiction that Codex is an API client.

5. Split budgets:
   - API dollar budget
   - estimated token usage
   - Codex wallclock budget
   - Codex turn/session budget

6. Make Codex-first workflows file-native:
   - Author already writes local files.
   - Critic and Council should eventually inspect local workspace files
     instead of receiving huge pasted TeX blocks.

7. Add an opt-in real Codex smoke test, skipped unless explicitly enabled
   by an environment variable.

## How to Run the Current Codex-First System

Prerequisites:

- `uv sync`
- `codex login status` should show a logged-in Codex CLI session.

Run the Codex-first Author/Critic smoke workflow on the bundled example:

```bash
uv run python scripts/run_workflow.py \
  --workflow codex_author_critic_smoke \
  --problem problems/example.txt \
  --run-id codex-primes-smoke
```

For a cheaper/faster initial probe, reduce the round count:

```bash
uv run python scripts/run_workflow.py \
  --workflow codex_author_critic_smoke \
  --problem problems/example.txt \
  --run-id codex-primes-smoke-1r \
  --input n_rounds=1
```

The run output is written under:

```text
outputs/<run-id>/
```

Useful files to inspect:

- `outputs/<run-id>/events.jsonl`
- `outputs/<run-id>/run-metadata.json`
- `outputs/<run-id>/ac_workspaces/`
- `outputs/<run-id>/agents/`

To run a very small prompt-only Codex workflow instead of Author/Critic:

```bash
uv run python scripts/run_workflow.py \
  --workflow codex_prescreen \
  --problem problems/example.txt \
  --run-id codex-prescreen-primes
```

The local dashboard can be started with:

```bash
uv run python app/dev.py --host 127.0.0.1 --port 5002
```

Then open:

```text
http://127.0.0.1:5002
```

Known test-suite status at this handoff:

```text
332 passed, 1 failed, 7 subtests passed
```

The one known failure is pre-existing:

```text
configs/workflows/conditional_repeat_screenshot.yaml is missing
```
