# Pi lane: closed literal series-level analysis of the defect series

**Status: COMPLETE.** `SeriesDefect.lean` compiles strict (Lean 4.34.1, Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612, `warningAsError` + `autoImplicit false`),
produces `SeriesDefect.olean`, and every public declaration's axiom report lists
only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `axiom`,
`unsafe`, or `native_decide` anywhere in the lane.

## Exact height statement (the endpoint)

```lean
theorem GammaLevel.existsUnique_seriesDefect (x : ℝ) (hx : 0 < x) {d : ℝ} (hd : 0 < d) :
    ∃! y : ℝ, 0 < y ∧ GammaLevel.seriesDefect x (x + y) = d
```

i.e. for every `x > 0` and `d > 0` there is exactly one height `y > 0` with

```
seriesDefect x (x + y) = d,   where   seriesDefect x s := ∑' m, profile ((s + m) / x),
profile u := -log (1 - u⁻¹²)   (from the unchanged GammaDefs.lean).
```

This is closed **at the series level**: it uses no Gamma identification, no
Source Lemma 15, and no new convexity-tool claims.

## All results proved in this lane

1. **Summability.** `summable_seriesTerm : 0 < x → x < s → Summable (seriesTerm x s)`.
   Key bound (m ≥ 1): `0 ≤ seriesTerm x s m ≤ x²/((s+m)²−x²) ≤ x²/m²` for `s > x`
   (`seriesTerm_nonneg`, `seriesTerm_le_inv_sq`), via
   `((s+m)/x)⁻¹² = x²/(s+m)²` and `1 − x²/(s+m)² ≥ 1 − x²/m²`.
2. **Continuity.** `continuousOn_seriesDefect x : 0 < x → ContinuousOn (seriesDefect x) (Ioi x)`
   (also for the tail), via uniform convergence of partial sums on `Ioi x`
   (`tendstoUniformlyOn_tsum_nat_eventually` + `Metric.tendstoUniformlyOn_iff`)
   plus `continuousOn_tsum`.
3. **Strict antitonicity.** `strictAnti_seriesDefect x : 0 < x → StrictAntiOn (seriesDefect x) (Ioi x)`,
   termwise from `profile_strictAnti` (the root lane's unchanged lemma) plus a
   strict `∑' (f − g) > 0` argument via `Summable.tsum_sub`/`Summable.le_tsum`.
4. **Vanishing at +∞.** `seriesDefect_tendsto_zero x : 0 < x → Tendsto (seriesDefect x) atTop (𝓝 0)`
   (termwise vanishing + uniform tail control).
5. **Divergence at the boundary.** `seriesDefect_tendsto_atTop x : 0 < x →
   Tendsto (seriesDefect x) (𝓝[Ioi x] x) atTop`. Core estimate
   `seriesTerm_zero_ge : x < s → s ≤ x / √(1 − e^{−M}) → M ≤ seriesTerm x s 0`
   (elementary squaring + `Real.exp_lt_one_iff`); the `M ≤ 0` case is trivial.
6. **Existence + uniqueness.** `exists_seriesDefect` (IVT via
   `intermediate_value_Icc'`, using 4 + 5 + 2) and
   `existsUnique_seriesDefect` (uniqueness from 3).

## What is NOT claimed

No Gamma identification, no bridge to `logDefect`, no Source Lemma 15, no new
convexity machinery. Helpers (`neg_log_sub_le`, `summable_u`,
`continuousOn_profile_shift`) are private and fully discharged.

## Reproduction

In `formal/` (pinned toolchain via `run_lean.py`):

```
python3 run_lean.py GammaDefs.lean -o GammaDefs.olean     # GAMMADEFS_OK
python3 run_lean.py SeriesDefect.lean -o SeriesDefect.olean
python3 run_lean.py Checks.lean                           # CHECKS_OK
```

`Checks.lean`/`Checks.log`: 17 `#check` type displays + 17 `#print axioms`,
all reading `[propext, Classical.choice, Quot.sound]`. Fresh replay performed
after deleting all `.olean` artifacts (see provenance.json).

## Scope note

Supporting formal component for the batch's series-level Gamma track. The
countable-family mixture and paper integration remain with root
(root-gamma-level-integration-r2 lineage). No count or acceptance claimed by
this lane.
