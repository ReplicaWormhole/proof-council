# Codex-First Handoff

## Current State

Branch: `source-trace-gate-handoff` (branched from `codex-first`)

The branch starts from three Codex-first increments:

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
337 passed, 1 failed
```

The one known failure is pre-existing:

```text
configs/workflows/conditional_repeat_screenshot.yaml is missing
```

## Current Status After Source-Trace Work (2026-06-11)

The source-trace gate requested below is now implemented on this branch.
The remaining work is hardening, rerunning serious proof jobs under the
new gate, and deciding the exact local-source/web-source policy.

Implemented:

- `src/proofstack/agents/ac/source_trace.py` adds `ACSourceTrace`,
  parsing for `<source_trace_json>`, `<source_trace_report>`, and
  `<source_ready>`, plus fail-closed validation.
- `src/proofstack/agents/ac/visual_blocks.py` adds
  `ACSourceTraceGateInput` and `ACSourceTraceBlock`.
- `src/proofstack/agents/ac/ac_workflow.py` runs the source-trace gate in
  the legacy early-stop path before deterministic compile/page acceptance.
- `src/proofstack/agents/ac/__init__.py` exports the new source-trace
  agent and block.
- The Author/Critic prompts now require exact source locators or internal
  proofs before `<ready>true</ready>` / `<answer_ready>true</answer_ready>`.
- These workflow presets now route through `source_trace_gate` before
  `ready_gate` / `compile_gate`:
  `author_critic.yaml`, `author_critic_smoke_mini.yaml`,
  `codex_author_critic_smoke.yaml`, `firstproof_submission.yaml`, and
  `firstproof_smoke_fast.yaml`.
- Source-trace artifacts are written as `.ac/source_trace.json` and
  `.ac/source_trace_report.md`, with round-specific copies when available.
- `scripts/__init__.py` was added so tests import the repo-local
  `scripts.run_workflow` package instead of another project's `scripts`
  package on `PYTHONPATH`.

The implemented gate accepts only source-trace steps with status
`cited`, `proved`, or `definition`. A cited step must include at least
one source entry with a nonempty exact locator. The deterministic
preflight also fails source-light answers with no citation/source-trace
markers and fails citation-heavy answers with empty `references.bib`.

Verification already run:

```text
python -m py_compile src/proofstack/agents/ac/source_trace.py \
  src/proofstack/agents/ac/visual_blocks.py \
  src/proofstack/agents/ac/ac_workflow.py \
  src/proofstack/agents/ac/author.py \
  src/proofstack/agents/ac/critic.py

uv run pytest tests/test_ac_source_trace.py \
  tests/test_codex_prompt_cleanup.py \
  tests/test_prompt_overhaul_contracts.py \
  tests/test_dev_data_mutations.py::DevDataMutationTests::test_author_critic_preset_validates_as_visual_dag_wrapper \
  tests/test_dev_data_mutations.py::DevDataMutationTests::test_firstproof_submission_preset_is_app_runnable \
  tests/test_dev_data_mutations.py::DevDataMutationTests::test_author_critic_smoke_mini_preset_is_all_mini_and_app_runnable \
  tests/test_dev_data_mutations.py::DevDataMutationTests::test_codex_author_critic_smoke_preset_is_codex_first_and_app_runnable \
  tests/test_ac_resume.py
# 35 passed

uv run pytest tests/test_dev_data_mutations.py tests/test_dag_schema_report.py \
  tests/test_workflow_graph_edges.py tests/test_run_discovery.py \
  tests/test_run_execution_graph.py
# 107 passed

uv run pytest
# 337 passed, 1 failed
```

The full-suite failure is the same known missing fixture:

```text
tests/test_workflow_presets.py::WorkflowPresetTests::test_conditional_repeat_keeps_solution_when_improver_is_skipped
configs/workflows/conditional_repeat_screenshot.yaml is missing
```

Current proof-run status:

- Run `magic-stabilizer-local-algebras-codex-1r-v3` is finished; no
  active process is attached to it.
- Output JSON:
  `outputs/magic-stabilizer-local-algebras-codex-1r-v3/agents/ACDAGWorkflow-c0-50850c/output.json`.
- Summary: `compiled=true`, `pages=5`, `rounds_completed=1`,
  `early_stopped=false`, `last_critic_accepted=false`,
  `final_critic_answer_ready=false`, `error=null`.
- Final artifacts:
  `outputs/magic-stabilizer-local-algebras-codex-1r-v3/solutions/magic_stabilizer_local_algebras.pdf`
  and
  `outputs/magic-stabilizer-local-algebras-codex-1r-v3/solutions/magic_stabilizer_local_algebras.tex`.
- The current answer is useful as a conditional note, but it is not
  accepted.

Critic blockers for the current proof:

1. Cyclic support is not proved.
2. Factoriality of `M_\Gamma` is not proved.
3. Non-type-I and finite-vs-infinite type of `M_\Gamma` are not proved.
4. The concrete toric-code/cone-region quotient `L_\Gamma`, radical, and
   boundary convention are not computed.
5. Source comparison is asserted rather than checkably derived from
   project files.
6. The Critic could not independently verify LaTeX/page count inside its
   runtime.

Open next steps:

1. Restore or replace `configs/workflows/conditional_repeat_screenshot.yaml`
   if the stale workflow-preset test should remain in the suite.
2. Harden source tracing with adversarial `SourceMapper` and
   `SourceAuditor` roles for serious research runs.
3. Decide whether source auditors may browse/download missing sources or
   must use only staged local source packets.
4. Rerun the stabilizer proof task under the new source-trace gate after
   choosing the source policy.
5. Continue the longer-term Codex architecture refactors below.

## Implemented Feature: Source Trace Gate

The workflow feature is a hard, fail-closed
"pre-formalization" or source-trace phase. The goal is that an answer is
not accepted merely because Author and Critic agree mathematically. After
the proof is otherwise accepted, every logical step in the final answer
must be traceable to an explicit source or proved in the answer itself.

### Desired Acceptance Rule

The final acceptance condition is now intended to be:

```text
Author ready
+ Critic accepted
+ deterministic compile/page gate
+ source trace gate
= accepted
```

The source trace gate passes only if every atomic logical step in
`answer.tex` is one of:

- `cited`: backed by exact published or stable reference locators, such
  as theorem/proposition/lemma/equation/section/page in a book, paper,
  lecture note, or other checkable source.
- `proved`: proved directly in `answer.tex`, with the proof's own
  substeps recursively cited, proved, or marked as definitions.
- `definition`: follows directly from a definition introduced in
  `answer.tex` or cited with an exact locator.

Generic support like "see Kadison--Ringrose" is not enough. Acceptable
support should look like "Kadison--Ringrose II, Theorem X.Y.Z, p. N" or
"Blackadar, Proposition A.B.C" whenever such a locator exists. Internet
or lecture-note sources are acceptable only if the source is stable and
the exact theorem/section/page/equation used is recorded.

If no exact theorem/source can be found for a step, the Author must add a
proof of that step. If neither a source nor a proof is present, the
source trace gate fails and feeds a concrete missing-source obligation
back to the next Author turn.

### Workflow Placement

The old DAG accepted through:

```text
author -> critic/council/compute -> review_join -> ready_gate -> compile_gate
```

The source phase is inserted after ordinary mathematical acceptance,
before the final gate:

```text
author
  -> critic/council/compute
  -> review_join
  -> source_trace_gate
  -> ready_gate
  -> compile_gate
```

The source trace phase no-ops unless `review_join.ready_for_gate` is
already true. That keeps normal early rounds cheap. Once Author and
Critic agree, source tracing runs as an additional independent auditor.

### Artifacts

The phase writes these run artifacts under the AC workspace, for example
in `.ac/`:

```text
source_trace.json
source_trace_report.md
```

`source_trace.json` is structured and machine-checkable. Record shape:

```json
{
  "step_id": "S3.2",
  "location": "answer.tex, Section 3, paragraph 2",
  "claim": "The compressed algebra is finite because the vector state restricts to a faithful normal trace.",
  "depends_on": ["S3.1"],
  "status": "cited",
  "sources": [
    {
      "bibkey": "KadisonRingroseII",
      "locator": "Theorem/section/page locator",
      "supports": "faithful normal tracial state criterion for finiteness"
    }
  ],
  "auditor_verdict": "pass"
}
```

Allowed `status` values are kept small and explicit:

```text
cited
proved
definition
missing
unsupported
ambiguous
```

Only `cited`, `proved`, and `definition` pass.

`source_trace_report.md` is human-facing and lists:

- all unsupported or weakly supported steps;
- broad citations that need exact theorem/page locators;
- steps where no source was found and an internal proof is required;
- any source that appears irrelevant or too weak for the claim it is
  supposed to support.

### Implementation Notes

The branch adds a source-trace agent:

```text
src/proofstack/agents/ac/source_trace.py
```

It defines:

```text
ACSourceTrace
ACSourceTrace.Inputs
ACSourceTrace.Outputs
parse_source_trace_output(...)
```

The prompt requires the auditor to:

1. Split `answer.tex` into atomic logical steps.
2. For each step, identify exact supporting references or mark that the
   step is proved internally.
3. Reject broad/non-locator citations.
4. Reject any "standard" step unless the theorem is cited or the step is
   proved in the text.
5. Return a structured trace plus a pass/fail tag, e.g.
   `<source_ready>true</source_ready>` or
   `<source_ready>false</source_ready>`.

The visual/workflow block lives in:

```text
src/proofstack/agents/ac/visual_blocks.py
```

Implemented block:

```text
ACSourceTraceBlock
```

Inputs:

```text
state
ready
```

Outputs:

```text
state
source_ready
ready_for_gate
source_trace_report
```

Behavior:

- if `ready` is false, return `source_ready=false` and do not run a
  model call;
- if `ready` is true, run `ACSourceTrace`;
- write `.ac/source_trace.json` and `.ac/source_trace_report.md`;
- set `state["source_ready"]`;
- set `state["source_trace"]`;
- if source tracing fails, append the missing-source obligations to
  `state["pending_workflow_feedback"]` so the next source-backing
  attempt has concrete obligations; if the obligation exposes a real
  mathematical gap, the next Author turn must fix the proof.

The workflow presets now route the ready path through:

```yaml
- id: source_backer
  kind: agent
  needs:
  - review_join
  agent: proofstack.agents.ac.ACSourceBackerBlock
  inputs:
    state: $node.review_join.state
    ready: $node.review_join.ready_for_gate

- id: source_trace_gate
  kind: agent
  needs:
  - source_backer
  agent: proofstack.agents.ac.ACSourceTraceBlock
  inputs:
    state: $node.source_backer.state
    ready: $node.source_backer.ready_for_gate

- id: ready_gate
  kind: if_else
  needs:
  - source_trace_gate
  inputs:
    ready_for_gate: $node.source_trace_gate.ready_for_gate
```

The old direct `ready_gate` edge no longer reads from
`review_join.ready_for_gate`.

### Pre-Acceptance and Source Backing

The ready path is now staged:

- `pre_accepted`: Author has set `<ready>true</ready>` and the Critic
  has set `<answer_ready>true</answer_ready>`. This means the proof is
  mathematically accepted by the Author/Critic pair, not finally
  accepted by the workflow.
- `source_backed`: `ACSourceBacker` has made a post-pre-acceptance pass
  that may only add inline source locators/citations and BibTeX entries.
  It must not change theorem statements, proof logic, equations, or
  conclusions.
- `source_ready`: `ACSourceTrace` verified that every logical step is
  inline source-backed, proved internally, or definitional.
- `accepted`: source trace passed and the deterministic compile/page
  gate passed.

Author readiness now means mathematical pre-acceptance. The Author is
explicitly told not to spend proof-search turns polishing locators
unless they are cheap and already known.

Critic readiness now means mathematical pre-acceptance. The Critic is
explicitly told not to set `<answer_ready>false</answer_ready>` solely
because exact source locators are missing; it should list those issues
for SourceBacker. It must still reject mathematically unsupported,
misquoted, inapplicable, or too-weak cited results.

Source support must be adjacent to the logical step it supports, e.g.
`by \cite[Theorem 1.2, p. 34]{Key}` or `(by Key, Theorem 1.2, p. 34)`.
The source-backed answer must not add a final "Source trace",
"Justification map", "Source comparison", or "open checks" section as a
substitute for inline support.

### Deterministic Checks Implemented

The gate is still model-driven, but a few deterministic checks now fail
fast:

- `answer.tex` has no `\cite`, `\Cite`, or explicit locator strings;
- `answer.tex` contains a final "Source trace", "Justification map",
  "Source comparison", or "open checks" section;
- `references.bib` is empty while nontrivial external theorems are used;
- `source_trace.json` is missing, malformed, or contains any step with
  `status` not in `{cited, proved, definition}`;
- any source entry has an empty `locator`.

These checks do not prove source correctness, but they prevent obvious
false positives.

### Open Design Questions

- Should source tracing be single-agent or adversarial? For serious
  research tasks, use at least two roles: `SourceMapper` and
  `SourceAuditor`.
- Should the source auditor be allowed to browse/download missing PDFs,
  or only use already staged/local sources? For the user's research
  workflow, local PDFs/books should be preferred, with web allowed when
  exact local support is absent.
- Should exact locators be enforced as PDF page numbers, theorem numbers,
  or both? Best default: require the theorem/lemma/proposition/equation
  number when available and also include page/section when discoverable.
- How should internally proved steps be represented in TeX? Recommended:
  each non-cited step gets a named lemma/proposition in `answer.tex` so
  the source trace can point to a concrete proof location.
