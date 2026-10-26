# Current twenty-outcome campaign checkpoint

Goal remains active: **20 distinct MathDB questions** with an exact claimed
outcome fully certified in Lean, a complete paper, independent review,
visual PDF QA and an extracted-archive replay. Never count multiple lemmas,
fields, normalizations or dimensions as separate outcomes. Existing-result
formalizations and literal-source corrections are allowed in the current
count but must be labeled; this is not a claim of twenty new discoveries.

## Verified: 9/20

Authoritative record: `ledger.json`. Published history is irrelevant to the
formal count: `HISTORICAL-AUDIT.md` found 0/19 full main-theorem Lean proofs
among older R023–R041. Their written-proof acceptance is not revoked.

1. 336488 premagic diagonalizability — base sibling package, commit e99b1337ab.
2. 336487 unnormalized eigenvector norm — commit 709dc9d383; elementary correction.
3. 362146 permutation-like spectrum — commit 958ef97dac; full theorem.
4. 340783 fair-discrepancy propagation — commit 5cf741da03; Patel counterexample verification.
5. 354537 scaled Tepper identity — commit 73eb170f3e; full source-corollary proof.
6. 317856 monochromatic-box PSD — commit cd5b1b00b0; known 2017 theorem verification.
7. 369281 shelf-shuffle spectrum — commit 90aeb4c22b; printed-index correction at n=4.
8. 366458 signed-set fusion — full four-property proof, conventional-loop and foundation limits explicit.
9. 373182 Matkowski equation — published Kiss counterexample formally verified.

The six newer release ZIPs and PDFs are in
`openai-proof-research/output/release/twenty-proofs/`. Their manifests and
fresh extracted-source Lean rebuilds passed. The base package has its own
release in `output/release/premagic-diagonalizability-v1.zip`.

## Active calls and pending acceptance

- functions cell **102**: full Fibonacci orbit-weight proof, MathDB371201,
  owner directory `../fibonacci-weight-lane/`. Existing proof by Shivam Patel
  must be credited. Actual recurrence/orbit/reduction bridges are required.
- functions cell **119**: full shuffle quadratic eigenvector proof,
  MathDB369280, owner `../shuffle-quadratic-lane/`. Binomial-moment route is
  in its task. This is distinct from the already-refuted printed spectrum.
- Arithmetic-ratio worker is running on MathDB375256 and375257, owner `../arithmetic-ratio-lane/`. It was launched before compaction; the exec-cell ID was lost in truncation. Delegated thread id is `thread:delegated-task:command%3Amcp%3Ab58c97f3-30ae-4e2d-a280-66f0ff79a183%3Adelegate-task%3A6a987e3c-6d16-4a8b-8d91-39f5748a60a0`. Do not duplicate or poll the running task; wait for its completion event.

Cells58,85,129,143 are completed/closed. Algebra review143 passed; minor docs fixed without changes to reviewed proofs or TeX. Both new archives passed extracted-source rebuild; receipt `build/algebra-replays.json`.

## Next tasks when a slot frees

The user requested maximum parallelism with explicit ultrafast tier. Use
T3 delegate_task with inherited Codex model and target.options
`{reasoningEffort: high, serviceTier: ultrafast}`. Cap active workers at3
plus parent. Do not spawn nested workers. New independent reviews require
new delegate_task calls. Follow any returned next instruction; do not poll
status, use timers, or silently replace a running delegate.

- `queued-sources/arithmetic-ratio-brief.md` gives a concrete route to two
  fully formal arithmetic-function inequalities, MathDB375256 and375257.
  Exact source/posted attempts are saved; credit Patel. The Dedekind-psi,
  sigma and phi bounds must be proved, not assumed as missing bridges.
- `queued-sources/371202-fibonacci-minima.json` records an existing posted
  counterexample: square-uniform initializations yield5/24 at zero instead
  of1/4. Formalizing mere5/24 !=1/4 is insufficient: prove the counting/limit
  connection to the actual recurrence. May be harder than the ratio pair.
- Other saved stochastic-matrix/Markov/game lists are candidate material,
  not outcomes. Newly discovered targets need source checking and a full
  proof before any counting.

## Tooling

`verify_outcome.py` compiles a byte-identical isolated single-module copy,
prints every local type/axiom list, enforces pinned dependencies and only
standard axioms. `build_paper.py` runs Tectonic and rejects overflow or
unresolved references. `package_outcome.py` refuses unreconciled review or
build hashes. `verify_archives.py` checks complete manifests and recompiles
from extracted ZIPs. CLI paths can be overridden for portable use.

Lean4.34.1: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`.
Mathlib packages: sibling2026-10-14/formal/.lake/packages, pinned in pins.json.
Tectonic: sibling2026-10-14/t088p133-manuscript-r2/tools/tectonic.
Shared TeX cache is this campaign's ignored build/cache.
The PDF skill's create marker was run for the batch of19 additional PDFs.
Do not redistribute full third-party source bodies or unrelated profiles.

Only own new work may be staged. The repository contains extensive unrelated
tracked and untracked user work. No external publication, posting or push
is authorized by this continuation. Keep the goal active until20 actually
qualify; do not mark complete merely to stop, or count an incomplete proof.

## Newest checkpoint (supersedes active-call details above)

Count is now11/20. Fibonacci371201 and shuffle369280 passed independent review,
visual QA and extracted ZIP rebuilds, and were committed individually as
2c81e46143 and4e16d8b21e. Review `reviews/recurrence-shuffle.md` was completed
(cell179 closed). `verify_outcome.py` now also inventories `abbrev`.

Active: cell169, discovery of two additional full MathDB results, owner
`../next-discovery-lane/`; cell196, independent review of canonical
`outcomes/graph-normalization` (MathDB349070), writes only
`reviews/graph-normalization.md`. That proof compiled8declarations; its
2-page paper was built and every page visually inspected. Do not count it
until review/package/replay. Its source uses standard diagonal majorization,
already used by Guigues2026AppendixB; no novelty/convergence claim.

The arithmetic worker remains active; see its exact thread ID above. Do not
launch a duplicate. User requires20; goal remains active. Parent is screening
new second-page inequality/polynomial source snapshots under queued-sources.
