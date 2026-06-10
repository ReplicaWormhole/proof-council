# ProofCouncil — project description

This repository will be the implementation of ProofCouncil, an autonomous
math-research agent system targeting the **First Proof Foundation, Second Batch**
benchmark (June 2026). Beyond the benchmark, the same system is intended
to grow into a human-in-the-loop research assistant for mathematicians.

`configs/workflows/instructions.md` is the current source of truth for
workflow syntax and reusable YAML components.

---

## What this repo currently is

A ProofCouncil workflow framework built on the MathArena provider/tool
layer. The kept pieces are:

- `src/mathagents/api_client.py` — robust multi-provider client (OpenAI,
  Anthropic, Google, xAI, DeepSeek, GLM, Moonshot, Together, vLLM, …)
  with retries, batch processing, tool-call loops, and cost accounting.
- `src/proofstack/tools/` — local workflow tools such as code execution and
  persisted files.
- `configs/models/` — layered YAML model definitions with `base:`
  inheritance.
- `configs/workflows/` — DAG workflow presets. Read
  `configs/workflows/instructions.md` before creating or editing these.
- `app/` — Flask developer dashboard for workflow runs, presets, and traces.
- `scripts/run_workflow.py` — CLI entry point for workflow presets.

---

## Repo layout

```
src/mathagents/      # API client, config loader, and provider-side tools
src/proofstack/      # Workflow/agent runtime
configs/             # YAML configs (models/, tools/, workflows/)
app/                 # Flask developer dashboard
scripts/             # CLI entry points
problems/            # Plain-text problem files
outputs/             # Run artifacts (JSON; gitignored)
solutions/           # Plain-text final answers (gitignored)
```

The new agent layer lives at `src/proofstack/`. The supported authoring
path is YAML workflow presets using `ConfigurablePromptAgent`,
`ConfigurableCLIAgent`, `DAGWorkflow`, and small deterministic helpers.

---

## How to run things today

We use [`uv`](https://github.com/astral-sh/uv).

Set provider keys via env vars (see `README.md` for the full table —
typically `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `GOOGLE_API_KEY`, …).

Run a workflow preset:

```bash
uv run python scripts/run_workflow.py \
  --workflow author_critic \
  --problem "Prove that there are infinitely many primes."
```

Browse outputs and presets:

```bash
uv run python app/dev.py
```

---

## Conventions

- **Minimalistic code.** No premature abstraction. A bug fix is a bug
  fix; don't slip in a refactor.
- **No comments unless they explain a non-obvious *why*.** Names should
  carry the *what*.
- **Python ≥ 3.12** (matches `pyproject.toml`). Type hints welcome where
  they help; not required everywhere.
- **Configs are YAML.** Use `base:` to inherit from another config; don't
  copy-paste prompts. Place model configs under `configs/models/<provider>/`.
- **Workflow presets have their own syntax guide.** Before adding or
  editing `configs/workflows/*.yaml`, read
  `configs/workflows/instructions.md`. It covers DAG node syntax,
  `ConfigurablePromptAgent`, tool refs, repeat loops, compile nodes, and
  validation commands.
- **All API traffic goes through `mathagents.api_client.APIClient`** so
  cost / token / retry logic stays consistent. Don't spin up a raw
  `openai.OpenAI()` somewhere.
- **Cost is real.** Workflow agents should route model calls through
  `mathagents.api_client.APIClient` so token and cost accounting stays
  centralized.
- **Checkpointing matters.** Long runs should persist enough state under
  their run directory to inspect and resume them.

### When editing workflow presets

Prefer config-only workflows in `configs/workflows/*.yaml` when the
requested agent is just a DAG of prompt nodes, repeat loops, and existing
tools. Read `configs/workflows/instructions.md` first; it is the compact
reference for the workflow runtime and should prevent spelunking through
`src/proofstack/agents/dag_workflow.py` for common syntax.

---

## Reading order for a new session

1. **This file** — orientation.
2. **`configs/workflows/instructions.md`** — concrete workflow syntax and
   reusable component guidance; required before creating or editing
   workflow preset YAML.
3. **`README.md`** — how to install + run today.
