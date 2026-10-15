# matrix-disk-formal-glm-r1 — finite scalar bistochastic variance identity

Bounded supporting formalization component of
`../matrix-disk-discovery/analysis.md` (variance section only).

Author: Myeongjin Kang, no affiliation. Original code, MIT license.

## What is proved

In `FiniteVariance.lean` (Lean 4.34.1, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`):

1. `bistochastic_variance` — the exact finite **real scalar** variance identity:
   for any finite type `I` (`[Fintype I] [DecidableEq I]`, empty type included),
   any `K : I → I → ℝ` with row sums `∀ i, ∑ j, K i j = 1` and column sums
   `∀ j, ∑ i, K i j = 1`, and any `u : I → ℝ`,

   ```
   ∑ j, ∑ i, ∑ k, K i j * K k j * (u i - u k) ^ 2
     = 2 * ((∑ i, u i ^ 2) - (∑ j, (∑ i, K i j * u i) ^ 2))
   ```

   Both Markov normalizations are used (column sums in the per-column lemma
   `tripleSum_column`, row sums to collapse the weighted second moment).
   Positivity of `K` is **not** needed for the identity.

2. `variance_deficit_nonneg` — corollary: under the same hypotheses plus
   entrywise nonnegativity `∀ i j, 0 ≤ K i j`, the deficit
   `∑ i, u i² - ∑ j, (∑ i, K i j * u i)²` is nonnegative (each triple-summand
   is termwise nonnegative).

3. `tripleSum_column` — the per-column intermediate identity
   `∑ i ∑ k K i j K k j (u i − u k)² = 2 * (∑ i K i j u i² − (∑ i K i j u i)²)`.

**Axiom audit (from `#print axioms` in the file, exact compiler output):**

```
'tripleSum_column' depends on axioms: [propext, Classical.choice, Quot.sound]
'bistochastic_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
'variance_deficit_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`/`admit`/`sorryAx`, no custom axioms, no `native_decide`. The target
equality is proved, not assumed; no axiom restates it.

## Scope limits (do not over-claim)

This finite scalar certificate does **not** cover: Hilbert-valued integrals,
moving kernels `K_j` (the analysis.md argument uses a sequence `K_j` and an
a.e. limit), the Fatou limiting argument, positivity on curved boundary arcs,
or any part of the full Crouzeix theorem. It is only the finite algebraic
identity above plus the nonnegativity corollary. The analysis.md variance
section states the Hilbert-space triple-integral formula `2δ_j = ∫∫∫ K_j(λ,μ)
K_j(ν,μ) ‖u_j(λ)−u_j(ν)‖²_HS dτ³`; this file proves its finite scalar
algebraic core with counting measure on an arbitrary finite index set.

## Files

| file | sha256 |
|---|---|
| `FiniteVariance.lean` | `cf6d64a82946147ebb6a3797570c050ce6377c662044a0e1d563050e59ffa077` |
| `Checks.lean` (independent sanity checks, not part of the certificate) | `171b6d75b7c21d4f64c4d6881079fc4d6d53637658a867584ca2ff523e0e6571` |
| `output/FiniteVariance.olean` (built artifact) | `e9b28036b1474c253448bd396693c0a039e1643d3bcefa3a62263ad8d0aa5866` |

Toolchain: Lean 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`),
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (verified by `git rev-parse`
in `../formal/.lake/packages/mathlib`). Toolchain binaries:
`/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`.

## Reproduction

Nothing outside this directory is modified; the existing cached environment
`../formal` is used read-only via `lake env`.

```bash
cd /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal
PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH \
  lake env lean /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/matrix-disk-formal-glm-r1/FiniteVariance.lean
```

Expected: exit code 0, no errors, no warnings, and the three `#print axioms`
lines shown above. (A `set_option linter.unusedSectionVars false` is set in
the file because `DecidableEq I` is part of the requested hypothesis profile
but is never used by the algebra; it is kept in the statements as specified.)

Optional independent checks (empty-type applicability and a concrete `Fin 2`
numeric evaluation agreeing with the theorem on both sides, deficit = 2):

```bash
# build the olean once (from this campaign directory)
cd /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/matrix-disk-formal-glm-r1
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
cd ../formal && LP=$(lake env printenv LEAN_PATH) && cd ../matrix-disk-formal-glm-r1
LEAN_PATH="$LP:output" lean -o output/FiniteVariance.olean FiniteVariance.lean
LEAN_PATH="$LP:output" lean Checks.lean
```

Expected for `Checks.lean`: exit 0; the only output is the three `#print
axioms` lines for `K2_row`, `K2_col`, `K2_nonneg` (all
`[propext, Classical.choice, Quot.sound]`).

## Proof coverage summary

| statement | status |
|---|---|
| `bistochastic_variance` (exact identity, exact hypotheses, arbitrary finite `I` incl. empty) | proved |
| `variance_deficit_nonneg` (deficit ≥ 0 under `0 ≤ K i j`) | proved |
| `tripleSum_column` (per-column expansion) | proved |

Honest failed attempts retained: the first drafts used `rw` with a
higher-order pattern under a binder, which `rw` cannot match (documented in
the working history; final proof uses `Finset.sum_congr`/`simp only` at
double-sum level, a general linearity lemma `sum_add_sub_two_mul`, and
explicit `X`/`Y`/`Z` instantiations to avoid a `whnf` heartbeat timeout). No
weakening of the statement (no fixed cardinality, no extra hypotheses) was
needed at any point.
