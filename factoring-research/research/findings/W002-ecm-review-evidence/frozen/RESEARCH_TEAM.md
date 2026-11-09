# Active factoring research team

The user explicitly authorizes ongoing iteration and as many useful T3 subagents
as needed. The coordinator is the current thread. Discover providers/models from
the live orchestrator catalog; use inherited settings unless a model choice is
authorized. Do not equate the catalog's maxBatchThreads with an independently
verified concurrent-task limit. Respect actual runtime capacity and errors.

## Ownership and task lifecycle

- All work stays in factoring-research. Sibling dlp-research work is independent.
- Use T3 delegate_task for this explicitly T3-owned work. These are child tasks,
  never new top-level threads. Retain taskId, clientRequestId, output path and role.
- Initial ideators receive independent lenses without other agents' conclusions.
  Each produces several mechanisms with a precise missing step and falsifier.
- Each child owns its assigned report and specifically named scratch files only.
  The parent owns shared harness, Lean imports/audit, protocols, STATE, and synthesis.
  Assign separate files explicitly before parallel implementation work.
- No recursive delegation in the initial ideation pass; the coordinator controls
  breadth and avoids duplicate work. Further decomposition can be authorized in
  an explicit follow-up task.
- Every new T3 review round uses a new delegate_task call with a distinct stable
  clientRequestId. Include the original brief, findings, responses and unresolved
  objections. Do not send another review to a child's backing thread ID.
- T3 async results wake the coordinator. Use task_status when a result is needed
  for active work or to resolve liveness, not a polling loop. If no independent
  work remains while children run, checkpoint and yield to the completion event.
- Preserve provider errors and rejected ideas. Do not silently replace a failed
  named model. No external publication, purchases, recurring scheduler, or commits
  are authorized by the research task itself.

## First wave W001

Task handles are in research/tasks-W001.json. Seven tasks were accepted as running
through T3 with inherited Codex / gpt-6-astra settings:

1. Relations: smoothness, norm constructions, dependencies, square relations.
2. Deterministic: product trees, multipoint evaluation, approximate divisors.
3. Lifting: p-adic/carry constraints, small roots, compact candidate sets.
4. Orders: modular exponentiation, classical period recovery, compressed sampling.
5. Algebra: zero divisors, resultants, idempotents, rank and class invariants.
6. Dynamics: nonuniform collisions, walk structure, ECM and group-order selection.
7. Baselines: primary literature and exact general/special-case complexity scope.

Each mechanism report should contain 3–4 distinct cards, not a quota of superficial
variants. The baseline report instead verifies reference bounds and identifies
bottlenecks. Output paths are exclusive W001-*.md files in research/hypotheses.
Use those results to deduplicate and rank; do not run every proposal automatically.

## Acceptance and continued iteration

Prioritize credible asymptotic changes over optimizing the lab. Every survivor
must name an executable primitive and pay for obtaining its useful inputs. Route
the strongest proposal to an independent critic and a bounded falsification
experiment. Separate general heuristic GNFS comparisons, proven expected/random
cost, deterministic worst-case bounds, special-family gains, and finite speedups.
No number of failed ideas proves factoring hard. No toy speedup proves polynomial
time. Use Lean only when a candidate needs a specific invariant or reduction.

After every disposition, revise a survivor or explore a materially different
mechanism. Maintain a short live shortlist and a durable rejected-idea register.
Stop or pause when the user instructs it; otherwise the research goal stays active
until a supported outcome satisfies the objective, not until a wave ends.
