# pi-sendov-selection-formal — lane summary

Lane owner: pi implementation sub-agent (solo, no children). Credit0 candidate;
**accepted tally14/30, candidate credit0** per tasking. Parent integrates; this
lane claims no full source endpoint result and no new discovery.

## Deliverables (both compile clean, `warningAsError=true`)

Pinned toolchain: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`
(Lean 4.34.1). Mathlib from the pinned checkout
`openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib`
at revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.

```
lanes/pi-sendov-selection-formal/
├── formal/
│   ├── run_lean.py          # own-authored runner; sets LEAN_PATH (cwd + pinned packages)
│   ├── Selection.lean       # PRIMARY deliverable (standalone, imports Mathlib only)
│   ├── Selection.olean      # build artifact (for importing from other lanes)
│   ├── ConvexWeights.lean   # SECOND deliverable (standalone, imports Mathlib only)
│   └── ConvexWeights.olean  # build artifact
├── formal-build.log         # full build + type/axiom inspection log
└── SUMMARY.md               # this file
```

Build: `cd formal && python3 run_lean.py -DwarningAsError=true Selection.lean`
(and likewise `ConvexWeights.lean`). Both files are mutually independent; each
imports only `Mathlib`. Namespace: `CStarSendov`.

## PRIMARY — `formal/Selection.lean` (global selection rigidity)

All results hold for a topological space `X` with `[PreconnectedSpace X]`.
**`[Nonempty X]` is not required** — on an empty space the conclusions are
vacuous but true and the proofs go through unchanged (noted in the module
docstring). For the parent's `X = [0,1]` the instance comes from connectedness.

1. `CStarSendov.continuous_two_point_selection` — general rigidity lemma: a
   continuous map from a preconnected space into a `MetricSpace` taking values
   in two distinct points `p ≠ q` is *globally* constant at `p` or at `q`.
   Proof: separates `p, q` by open balls of radius `dist p q / 2` and applies
   `isPreconnected_univ` (the `IsPreconnected` open-partition definition) to the
   two disjoint nonempty preimages. No `IsPreconnected.constant_of_mapsTo` /
   `IsDiscrete` needed.
2. `CStarSendov.selection_rigidity` — **the requested primary theorem**: for
   continuous `b f g : X → ℂ` with `f x ≠ g x` for *every* `x` and
   `b x = f x ∨ b x = g x` for every `x`, conclude `b = f ∨ b = g` as functions
   (via the continuous coordinate `r = (b−g)/(f−g)` valued in `{0,1}`).
   The global selection property is *proved*, not assumed.
3. `CStarSendov.selection_rigidity_cmap` — same statement for bundled
   continuous maps `C(X, ℂ)` (`ContinuousMap.ext`).
4. `CStarSendov.factor_root_global` — specialization: every continuous `b`
   satisfying the pointwise factor equation `(b x − b1 x) * (b x − b2 x) = 0`
   (for all `x`) is globally `b1` or `b2`. **Zero-divisor caution** (also in the
   docstring): the equation is hypothesized and used *pointwise in ℂ*;
   `mul_eq_zero` is applied only after pointwise evaluation. An equation stated
   at the level of the function algebra `X → ℂ` (which has zero divisors) would
   not by itself license the pointwise alternative.
5. Proximity obstruction (discharges the parent's load-bearing topological
   branch "no critical element lies in the pointwise C\*-unit disc around the
   distinguished root"):
   * `no_proximity_factor_root` — if `b1, b2` are continuous and everywhere
     apart and there are points `x1, x0` with `1 < ‖a0 x1 − b1 x1‖` and
     `1 < ‖a0 x0 − b2 x0‖`, then no continuous factor root `b` of the pointwise
     equation satisfies `‖b x − a0 x‖ ≤ 1` for every `x`.
   * `exists_no_proximity_factor_root` — the `¬∃ b, …` form, for direct
     discharging.
   * `no_proximity_factor_root_dist` — the same with `dist` instead of `‖·‖`.
   * `dist_le_one_iff_normSq_le_one` — bridge from `dist z w ≤ 1` to the
     parent's pointwise `|z − w|² ≤ 1` (`Complex.normSq (z − w) ≤ 1`)
     formulation of the C\*-unit disc condition.

**Not done here (parent's job, per tasking):** explicit `exp`/`sqrt` branch
functions, unit-norm bounds, scalar endpoint values, the final source
C\*-statement, and the identification of the parent's specific `B±`, `a0` with
the hypotheses above. This lane makes **no** claim about the source endpoint or
the full conjecture refutation.

## SECOND — `formal/ConvexWeights.lean` (positive convex weights)

* `CStarSendov.deletedProductDeriv B a x = ∑_j ∏_{k≠j} (B x − a_k x)` — the
  literal deleted-product derivative (with `deletedProductDeriv_apply` = rfl).
* `CStarSendov.exists_convex_weights` — for continuous `B : X → ℂ` and roots
  `a : Fin 3 → X → ℂ` (any topological `X`; **no connectedness/nonemptiness
  needed**) with `B x ≠ a j x` everywhere and
  `∀ x, deletedProductDeriv B a x = 0`, there is `ω : Fin 3 → X → ℝ` with
  * `∀ j, Continuous (ω j)`,
  * `∀ x j, 0 < ω j x` (strictly positive real-valued),
  * `∀ x, ∑_j ω j x = 1`,
  * `B = ∑_j ω j • a j` (as functions, hence in `C(X, ℂ)`).
  Witness: `ω j x = r j x / (∑_i r i x)` with `r j x = 1 / |B x − a j x|²`.
  Proof path mirrors the parent's hand argument: divide the vanishing deleted
  product by the nonvanishing `∏_k (B x − a_k x)` to get the harmonic identity
  `∑_j (B x − a_j x)⁻¹ = 0`; conjugate once to get
  `∑_j r_j • (B x − a_j) = 0`; expand and divide by the positive total.
  Key supporting identities proved inside: `harmonic_sum_zero` (private) and
  `conj_inv_eq_rmul` (private), i.e. `(⋆(B−a_j)⁻¹) = (1/|B−a_j|²) • (B−a_j)`.

**Exact remaining bridge to the C\*-order (NOT formalized here):** the pointwise
conclusions give, in `A = C(X, ℂ)`, elements `ω_j` that are *self-adjoint
real-valued continuous functions, pointwise `> 0`, summing to `1` in `A`, with
`B = ∑_j ω_j • a_j` in `A`. To match the source's positivity hypothesis one
still needs: *for compact Hausdorff `X` (e.g. `[0,1]`), a self-adjoint
`f ∈ C(X)` is a positive element of the C\*-algebra iff `f(t) ≥ 0` for every
`t`* (equivalently `σ(f) ⊆ [0,∞)`, with `σ(f)` the sup-norm spectrum, which for
compact `X` is the closure of the range). This bridge is **not** proven in this
lane; the parent may either cite it as a standard fact or formalize it later.

## Verification status

* Both files compile with zero errors **and zero warnings** under
  `-DwarningAsError=true` (exit 0; see `formal-build.log`).
* No `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` anywhere
  (grepped).
* `#print axioms` on **every** new declaration (public and the two private
  helpers) shows exactly `[propext, Classical.choice, Quot.sound]` — the
  standard three axioms, nothing else. Full log: `formal-build.log`.

## Honest limitations / gaps

* All results are stated for `X → ℂ` (functions) or `C(X, ℂ)` (bundled maps);
  nothing here touches C\*-algebra positivity, spectra, or the source's
  Equation (1) beyond the pointwise identity `B = ∑ ω_j • a_j` above.
* `deletedProductDeriv` is the *literal* deleted-product form; no connection to
  `Polynomial.derivative` of an explicit cubic is formalized (the parent's
  factorization supplies the pointwise vanishing hypothesis directly).
* The proximity obstruction assumes the parent has *already* identified its two
  global critical branches `b1, b2` (continuous, everywhere apart) and the
  scalar endpoint distances `> 1`; those numeric bounds are not proven here.
* The `MetricSpace` (not `PseudoMetricSpace`) hypothesis in
  `continuous_two_point_selection` is only because this Mathlib pins `dist_pos`
  to `MetricSpace`; ℂ satisfies it.

## Usage sketch for the parent

```lean
import ConvexWeights  -- or: import Selection (independent modules)

open CStarSendov
-- With b1, b2 : X → ℂ the two continuous critical branches, everywhere apart,
-- a0 the distinguished root, and scalar endpoint bounds at x0, x1:
example [PreconnectedSpace X] {a0 b1 b2 : X → ℂ} (hb1 : Continuous b1)
    (hb2 : Continuous b2) (hap : ∀ x, b1 x ≠ b2 x) {x0 x1 : X}
    (h1 : 1 < ‖a0 x1 - b1 x1‖) (h2 : 1 < ‖a0 x0 - b2 x0‖) : True := by
  -- No continuous factor root stays in the pointwise unit disc around a0:
  have := exists_no_proximity_factor_root hb1 hb2 hap h1 h2
  trivial
```

No staging, commits, or edits outside this lane were performed. No external
communications. No children were spawned.
