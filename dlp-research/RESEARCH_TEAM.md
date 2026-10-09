# Research task operating instructions

**USER STOP, 2026-10-09 UTC:** no new delegated work, research, retries or
followup review rounds. Collect only already running work within its original
scope and budget, mark unchecked output as unchecked, and stop. The coordinator
must prepare [research/HANDOVER.md](research/HANDOVER.md) and pause the existing
goal. Explicit user resumption is required before the historical policies below
authorize more work. Other research threads are outside this coordinator's scope.

User authorization, 2026-10-07: run a separate research-loop task; allow
parallel subagents using GPT Astra/Sol, Claude Opus 5.5, Grok 4.7, and Factory's
Claude Fable and Opus; investigate alternatives, verify hypotheses in depth,
and commit significant findings alongside the research process.

## Main-objective priority (user steering,2026-10-08 UTC)

Algorithmic ECDLP complexity and matched end-to-end work are the primary metrics.
Verified improvement is currently NONE. The prior infrastructure-first ordering
is superseded. Do not launch or extend decoder/query/machine/tape work unless a
named promising candidate needs that exact result for a decision. Preserve parked
work and negative evidence; do not count it as an algorithmic improvement.

Each wave must rank specific mechanisms against primary prior art and credible
baselines, then run cheap falsifiers before expensive formalization. Explore
ideas in parallel and review them independently. Include all preprocessing,
memory, failed attempts, success probability and amortization. Use increasing
representative synthetic sizes and declared seeds, never third-party wallets.
Known signed BSGS/automorphism tricks are baselines, not discoveries. Special-curve
attacks require their exact hypotheses and do not transfer to ordinary targets.
Lean should prove focused candidate claims; general infrastructure needs a
candidate-specific justification. No AI-FLOPS-to-GPU-curve-work conversion.

Every wave reports best supported complexity/work, verified improvement, current
hypothesis, evidence for/against and the next conclusion-changing experiment.

## Coordinator and approved delegates

Use GPT-6 Astra as coordinator. The following exact targets were available
from `orchestrator_capabilities` at setup. Rediscover capabilities when needed;
do not guess identifiers or silently replace an explicitly selected model.

- Codex: `providerInstanceId: codex`, models `gpt-6-astra`, `gpt-6.1-sol`,
  `gpt-6-sol`.
- Claude: `providerInstanceId: claudeAgent`, model `claude-opus-5-5`.
- Grok: `providerInstanceId: grok`, model `grok-4.7`.
- Factory: `providerInstanceId: acpRegistry_factory_droid`, models
  `claude-fable-5.1`, `claude-fable-5`, `claude-opus-5-5`, `claude-opus-5`.

These are permissions, not an instruction to spend equally on every model.
Choose models for the work, diversify independent reviews where useful, and
record which provider/model actually ran. Availability is not a guarantee a
provider request will succeed. Report provider failures explicitly.

Use native child-agent tools for supported same-provider work, or T3
`delegate_task` for cross-provider work, unavailable native model IDs, or
T3-owned delegation. Never create top-level threads merely to spawn reviewers.
For each new T3 review round call `delegate_task` again with the original
brief, previous findings, responses, and unresolved objections. Record each
returned task ID and a distinct stable client request ID per round. Do not
continue a delegated review by sending a message to its backing child thread.

If an ACP agent cannot see the T3 tools, use the documented
`T3_ACP_MCP_NODE` / `acp-mcp-call` transport fallback. Do not invoke an unrelated
provider CLI or bypass model-account permissions.

## Parallel work

Respect the live runtime's concurrency limits, including the coordinator.
User explicitly confirms T3 Code can run20 concurrent delegated subagents.
Use that T3 capacity for distinct useful tasks; the four-slot limit remains on
native delegation. Do not infer this merely from maxBatchThreads, and never
substitute top-level thread creation. This user-confirmed capacity supersedes
the earlier conservative shared four-slot assumption. Track both native and T3
live handles and honor actual provider errors/limits. Latest steering requires broad initial
independent idea generation, not a fixed two-hypotheses-plus-critic pipeline.
Keep available slots occupied by distinct productive tasks using rolling waves,
while preserving current investigations. Each proposer should offer roughly3–5
genuinely different mechanisms where worthwhile; aim for roughly15–25 distinct
initial candidates across waves without padding or treating counts as success.
Diversify authorized models from the live catalogue and report actual failures.
Assign distinct lenses and withhold other initial proposals until synthesis to
reduce anchoring. Each card states mechanism, potential gain, prior-art distinction,
unsupported assumption and cheap falsifier. High-risk ideas may enter without
complete proofs. Deduplicate and rank by meaningful gain and cheap testability;
retain rejected ideas/reasons. Then assign independent skeptical cost/prior-art
review and matched synthetic experiments to survivors. No generic lower-bound
argument alone excludes coordinate-aware approaches. No slots for duplicate
opinions or parked infrastructure. Ownership rules below still apply.

Once there is a testable hypothesis, organize separate roles for proposal,
implementation, adversarial mathematical review, Lean proof review, and
reproducible experiment/cost review. These need not all run simultaneously.
Send precise deliverables, file ownership, hypotheses, and falsification tests
in every prompt. Delegates may suggest deeper investigations; the coordinator
controls expansion so grandchildren do not exceed capacity or duplicate work.

Default reviewers to read-only. Give writers disjoint files or isolated
checkouts and integrate serially. Avoid concurrent edits to `Audit.lean`,
`Research.lean`, shared specifications, or `research/STATE.md`. Only the
coordinator stages and commits integrated work in the shared checkout.

Use asynchronous completion notifications rather than busy polling. Before
launching another wave, inspect recorded live task IDs to avoid duplicate runs.

## Research records and verification

Create `research/findings/<id>.md` for each significant hypothesis or result.
Each record should contain:

- precise claim, motivation, baseline, scope, and prior primary sources;
- algorithm or formalization and its assumptions;
- what would disprove the claim;
- experiments, exact commands, seeds/parameters, and observed costs;
- Lean theorem names, proof status, and axiom audit results;
- preprocessing, memory, probability, and scaling limitations;
- reviewers and task IDs, objections, responses, and unresolved questions;
- verdict: hypothesis, verified limited result, rejected, or blocked;
- next distinct step.

Preserve useful negative results and disagreements. Do not claim a practical
or asymptotic breakthrough from an easy curve, stronger input assumption,
changed cost model, benchmark alone, or unproved refinement. Strengthen the
checking process as the significance of a claim increases.

## Commits

The user explicitly authorizes local git commits. Commit coherent verified
milestones: a substantive proof/refinement, reproduced experiment, supported
improvement, or useful negative result. Include its research record and updated
checkpoint in the same commit. Hypotheses may be recorded as hypotheses;
never label unresolved proposals as established findings.

Before committing code, run `./scripts/check.sh`, inspect the diff, and record
validation. Review all staged paths and include only task-owned project files.
Keep toolchains, build products, credentials, and bulky generated data out of
git. Do not use `git add .` indiscriminately, rewrite unrelated commits, discard
user edits, push, or publish findings externally. Publishing requires a separate
user request. The root setup commit is infrastructure, not a research result.

Use descriptive subjects such as `research: verify <limited claim>` or
`research: rule out <hypothesis under assumptions>`. Commit messages should
summarize what the evidence establishes and its remaining limits.

## Continuation

This is open-ended research with no promised discovery date. Checkpoint after
each wave and continue meaningful work under the active task. If the runtime
supports a persistent goal, use it for the user-authorized research objective.
Do not mark that objective achieved merely because the scaffold compiles.
If interrupted, provide the last commit, live task IDs, and next step. If the
same external blocker persists for three iterations, report it instead of
spinning. Honor later stop, pause, model, or budget instructions immediately.
