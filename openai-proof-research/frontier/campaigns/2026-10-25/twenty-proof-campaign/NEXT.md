# Current twenty-outcome campaign checkpoint

Goal remains active: **20 distinct MathDB questions** with an exact claimed
outcome fully certified in Lean, a complete paper, independent review,
visual PDF QA and an extracted-archive replay. Never count multiple lemmas,
fields, normalizations or dimensions as separate outcomes. Existing-result
formalizations and literal-source corrections are allowed in the current
count but must be labeled; this is not a claim of twenty new discoveries.

## Verified: 7/20

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
- functions cell **143**: independent review of canonical
  `outcomes/sigma-fusion` (366458) and `outcomes/matkowski` (373182), writes
  only `reviews/algebra-two.md`.

Cells 58, 85 and 129 are COMPLETED/CLOSED; do not wait on them again. The
three original discovery lanes completed. Reviews `first-three.md` and
`second-three.md` passed and are included in accepted releases.

The two pending algebra outcomes are fully compiled (25 and12 declarations)
and their two-page PDFs have been rendered and visually inspected. On a
PASS review, seal exact reviewed hashes in outcome.json, copy review.md,
package, replay, update ledger, and commit each finding separately.
Check sigma-fusion's scope: it proves the four explicit signed-set algebra
properties; it does not construct the source's nonstandard foundational
set theory or establish a usual quasigroup loop. Matkowski is explicitly
verification of Kiss's published counterexample mechanism, not a new disproof.

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
