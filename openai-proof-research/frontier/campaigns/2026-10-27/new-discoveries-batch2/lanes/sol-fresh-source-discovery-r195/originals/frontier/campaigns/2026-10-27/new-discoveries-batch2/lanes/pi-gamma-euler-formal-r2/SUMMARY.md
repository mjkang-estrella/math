# SUMMARY — pi-gamma-euler-formal-r2 (genuine closed Gamma HasSum bridge + literal ratio equivalence)

Lane: `frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/pi-gamma-euler-formal-r2`
Worker: Pi implementation sub-agent, solo, no children. No git/stage/shared/other-lane
edits; predecessor `pi-gamma-euler-formal-r1` untouched (its files were empty/preserved);
no manuscript, no count, no source acceptance.

## Status: COMPLETE — fresh compile PASS, axiom audit clean

Both priorities delivered as closed Lean 4 component with no residual analytic premises,
no `sorry`/`admit`/`axiom`/`unsafe`/`native_decide`, `autoImplicit false`,
`warningAsError true`. All 9 new declarations' `#check` types and `#print axioms`
were read from actual compiler output; only `propext`, `Classical.choice`,
`Quot.sound` occur (standard 3).

## Toolchain (absolute, pinned)

- Lean 4.34.1: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`
  (version string `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`)
- Mathlib: `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib`, git rev `d13f23b723b8a846827a245b89c10fc7d3f11612` (verified), plus the 8 adjacent compiled deps resolved by `run_lean.py` LEAN_PATH.
- `run_lean.py` copied unchanged from root-gamma-level-formal-r1 (sha256 `6c242b10c855b5daa4cd1fca6fe87e02a966fd285e2da80b76c65109dd453fbd`); it pins the absolute toolchain and works in temp dirs (used by the fresh replay).

## Files

| file | sha256 |
|---|---|
| `formal/GammaDefs.lean` (COPY, byte-identical to root formal, interface unchanged) | `86fa21b273478be47f2b7309a0a4740802cb2a1d8c5a66d7567891b2ca4520a7` |
| `formal/GammaEuler.lean` (new) | `ff21f185a87e541ee476debc427c08b551eeb427c8249224fc81056366b48b92` |
| `formal/GammaRatio.lean` (new) | `0b88bddfe53b9596f4098be8169228f5d2beff40ef5c88d20323f954f1444e65` |
| `formal/Checks.lean` (new, #check/#print axioms audit) | `95c54c7c79efba90045261024a004f169781b6ab835ea543d23f4222d701680f` |
| `formal/run_lean.py` (COPY) | `6c242b10c855b5daa4cd1fca6fe87e02a966fd285e2da80b76c65109dd453fbd` |
| `verify_component.py` (new fresh-replay driver) | `a9f1317dcd863f9c953d7343d88a6d95cb739c936a7db97f85595fadd937ca0c` |

Oleans (`GammaDefs/GammaEuler/GammaRatio.olean`) are lane-local build artifacts.

## Exact interfaces (from actual `#check` output, verification/Checks.log)

PRIORITY 1 — genuine closed `GammaHasSum` (`GammaEuler.lean`, namespace `GammaLevel`):

```lean
theorem finite_sum_eq_logGammaSeq {x s : ℝ} (hx : 0 < x) (hsx : x < s) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), seriesTerm x s m =
      Real.BohrMollerup.logGammaSeq (s - x) n + Real.BohrMollerup.logGammaSeq (s + x) n -
        2 * Real.BohrMollerup.logGammaSeq s n

theorem tendsto_logGammaSeq_mix {x s : ℝ} (hx : 0 < x) (hsx : x < s) :
    Tendsto (fun n => Real.BohrMollerup.logGammaSeq (s - x) n + ... - 2 * ... s n)
      atTop (𝓝 (logDefect x s))

theorem tendsto_partialSum_logDefect {x s : ℝ} (hx : 0 < x) (hsx : x < s) :
    Tendsto (fun n => ∑ m ∈ Finset.range n, seriesTerm x s m) atTop (𝓝 (logDefect x s))

theorem seriesTerm_nonneg {x s : ℝ} (hx : 0 < x) (hsx : x < s) : ∀ m : ℕ, 0 ≤ seriesTerm x s m

theorem gammaHasSum {x s : ℝ} (hx : 0 < x) (hsx : x < s) :
    HasSum (seriesTerm x s) (logDefect x s)          -- genuine, unconditional filter

theorem gammaHasSum' : ∀ x s : ℝ, 0 < x → x < s → HasSum (seriesTerm x s) (logDefect x s)
```

PRIORITY 2 — literal ratio equivalence (`GammaRatio.lean`):

```lean
theorem logDefect_shift (x y : ℝ) :
    logDefect x (x + y) = log Γ y + log Γ (y + 2*x) - 2 * log Γ (y + x)

theorem logDefect_eq_log_iff_ratio {x y c : ℝ} (hx : 0 < x) (hy : 0 < y) (hc : 0 < c) :
    logDefect x (x + y) = Real.log c ↔
      Real.Gamma y * Real.Gamma (y + 2 * x) / Real.Gamma (y + x) ^ 2 = c

theorem sourceLevel_iff_defect {c x y : ℝ} (hx : 0 < x) (hc : 0 < c) :
    SourceLevel c x y ↔ 0 < y ∧ logDefect x (x + y) = Real.log c
```

## Proof mechanism (no unproved Euler-Gamma axiom, no abstract surrogate)

1. **Finite exact cancellation.** Each term rewrites as
   `seriesTerm x s m = 2*log(s+m) - log((s-x)+m) - log((s+x)+m)` (uses
   `(s+m)/x > 1`, `inv`/`div_pow`, `one_sub_div`, `Real.log_mul/div/pow`).
   Summing over `range (n+1)` and comparing with the *actual* Mathlib definition
   `Real.BohrMollerup.logGammaSeq a n = a*log n + log n! - ∑_{m∈range(n+1)} log (a+m)`
   (verified type `ℝ → ℕ → ℝ`), the `x log n` and `log n!` coefficients are
   `(s-x)+(s+x)-2s = 0` and `1+1-2 = 0`: they cancel **identically in each finite
   `n`** (closed `ring` step over sum atoms), not asymptotically.
2. **Limit.** `Real.BohrMollerup.tendsto_log_gamma {x : ℝ} (hx : 0 < x) :
   Tendsto (logGammaSeq x) atTop (𝓝 (log (Gamma x)))` (actual type verified; the
   generic `tendsto_logGammaSeq` needs `ConvexOn`+`f`-equation hypotheses and is
   NOT used) applied at `s-x, s+x, s`, all positive since `0 < x < s`, gives
   `tendsto_logGammaSeq_mix`.
3. **Index shift.** Partial sums over `range n` equal the mixed sequence at `n-1`
   (`Filter.eventually_atTop`, `ω`); `(n-1)` tends to `atTop` (proved inline via
   `Filter.tendsto_atTop`), composed with the mixed-sequence tendsto.
4. **HasSum conversion.** Every term is nonnegative (`seriesTerm_nonneg`), so
   `hasSum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (r : ℝ) :
   HasSum f r ↔ Tendsto (fun n => ∑ i ∈ range n, f i) atTop (𝓝 r)`
   (actual signature verified from `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean:560`)
   converts the partial-sum limit into a genuine `HasSum`. No positivity-based
   existence surrogate: the exact limit value is carried through.
5. **Ratio equivalence.** `Real.Gamma_pos_of_pos` at `y, y+2x, y+x`, then
   `Real.log_div`, `Real.log_mul`, `Real.log_pow` collapse the defect into one
   logarithm (`logDefect_shift` + `hlogform`), and `Real.log_injOn_pos` gives the
   iff. `sourceLevel_iff_defect` transports it to the literal `SourceLevel`.

## Verification

- Compile order: `GammaDefs.lean → GammaEuler.lean → GammaRatio.lean`, then
  `Checks.lean`. All exit 0, **zero warnings** under `warningAsError true`.
  Logs: `buildlogs/Gamma{Defs,Euler,Ratio}.log`, `buildlogs/Checks.log`,
  `verification/Checks.log` (types + axiom reports), `verification/bohrmollerup-types.log`.
- **Fresh replay**: `python3 verify_component.py` copies all sources to a clean
  temp dir and recompiles from scratch with the pinned toolchain; result **PASS**
  (`verification/replay.log`), including per-declaration axiom-report checks and
  banned-token scan.
- Axioms of all 9 new declarations: `[propext, Classical.choice, Quot.sound]` only.

## Scope notes for root assembly

- `gammaHasSum` has exactly the shape of the `hseries` hypothesis consumed by
  root's `ConvexAssembly.defect_strict_mixture` / `level_height_strictConvexOn`
  (`∀ x s, 0 < x → x < s → HasSum (seriesTerm x s) (logDefect x s)` — the
  closed-universal form is `gammaHasSum'`).
- The ratio bridge gives root the literal `SourceLevel` ↔ defect-level transport
  needed to instantiate the level `d = log c` on the implicit curve; it does NOT
  construct the level/monotonicity (that is the parallel worker's lane, not
  duplicated here), and claims no new convexity tool. All `c > 1` is one family.
- Definitions `logDefect`, `profile`, `seriesTerm`, `SourceLevel` come solely from
  the unchanged copied `GammaDefs.lean`; no redefinition, no editing of root files.
- No residual analytic premises inside this component's own statements: every
  hypothesis is an order condition on `x, s, y, c`; all analytic content
  (Euler/Bohr-Mollerup limit, log rules, HasSum conversion) is discharged inside
  the proofs from Mathlib.
