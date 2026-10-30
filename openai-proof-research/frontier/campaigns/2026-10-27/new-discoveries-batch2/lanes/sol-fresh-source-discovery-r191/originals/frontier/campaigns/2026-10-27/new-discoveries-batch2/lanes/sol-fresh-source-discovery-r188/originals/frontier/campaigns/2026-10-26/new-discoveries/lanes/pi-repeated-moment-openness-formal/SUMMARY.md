# Lane Summary — `pi-repeated-moment-openness-formal`

## Deliverable

`formal/MomentOpen.lean` — a complete, axiom-clean Lean 4 / mathlib proof of:

```lean
theorem smoothMomentSet_convex (n : ℕ) : Convex ℝ (RepeatedIntegrals.smoothMomentSet n)
theorem smoothMomentSet_isOpen (n : ℕ) : IsOpen (RepeatedIntegrals.smoothMomentSet n)
```

for the frozen interface `MomentDefs.lean` (`MomentSpace n = Fin (n+1) → ℝ`,
`densityMoments n ρ i = ∫ t in 0..1, t^i.val * ρ t`, `GoodDensity`, `smoothMomentSet n`).

## Exact scope

- **Proved**: Convexity and openness of `smoothMomentSet n` **for every `n : ℕ`**,
  including `n = 0` (no special-casing anywhere).
- **Proved with**: no `sorry`/`admit`/`axiom`/`unsafe`/`native_decide`; the only
  axioms used are `propext`, `Classical.choice`, `Quot.sound` (verified by
  `#print axioms`; see `axiom_check.log`).
- **Actual moment integrals used throughout** — no abstract surrogate for the moment
  map: the perturbation's moment contribution is computed as the honest Gram matrix
  `gramMatrix n i j = ∫ t in 0..1, t^(i+j) * χ t` (positive definite because
  `∫ χ · p(t)^2 dt > 0` for every nonzero polynomial `p`, which follows from a
  compactness/finite-roots argument), and the realization step is the honest identity
  `densityMoments n (perturb ρ0 c) = densityMoments n ρ0 + gramMatrix n *ᵥ c`.
- **No residual assumptions**: no basis invertibility, no existence/positivity/rank
  hypotheses remain; all constants are constructed (explicit bump `χ`, explicit
  coefficient vector `c = (gramMatrix n)⁻¹ *ᵥ (y - y0)`, explicit radius
  `r = (m0 / (2 (n+1))) / B`).

## Proof sketch

1. Fixed smooth bump `χ` (via mathlib `ContDiffBump` at 1/2, radii 1/8 → 1/4):
   `0 ≤ χ ≤ 1`, `χ > 0` on `ball (1/2) (1/4) = Ioo (1/4) (3/4)`, `χ = 0` for
   `t < 1/4` and `t > 3/4`.
2. Perturbation `perturb ρ0 c = ρ0 + χ · (∑ c_i t^i)`. Moments are linear:
   `densityMoments n (perturb ρ0 c) = densityMoments n ρ0 + gramMatrix n *ᵥ c`.
3. `gramMatrix n` is positive definite: for `c ≠ 0` the integrand
   `χ(t) · (∑ c_i t^i)^2` is ≥ 0, continuous, and > 0 somewhere in `Ioo (1/4) (3/4)`
   (a nonzero polynomial has finitely many roots, so it cannot vanish on the whole
   ball); hence `gramMatrix n` is invertible.
4. `goodDensity_perturb`: if `ρ0 ≥ m0 > 0` on `[0,1]` and `∑ |c_j| ≤ m0/2`, then
   `perturb ρ0 c` is again a `GoodDensity` (positivity via `0 ≤ χ ≤ 1`, `|t| ≤ 1`;
   endpoint germs preserved since `χ = 0` near 0 and 1).
5. **Convexity**: for `a, b > 0`, `a + b = 1`, the density
   `t ↦ ρ1 t * a + ρ2 t * b` is good (positive convex combination; germs via
   `filter_upwards` on the intersection of the two endpoint neighborhoods) and its
   moments are `a • m(ρ1) + b • m(ρ2)`.
6. **Openness**: at a good `ρ0` with `m0 = min ρ0` on `[0,1]`, let
   `eps = m0 / (2 (n+1))`, `B = 1 + ∑_{i',j} |(gramMatrix n)⁻¹_{i'j}|`,
   `r = eps / B`. For any `y` in the sup-norm ball `ball y0 r`, the coefficient
   vector `c = (gramMatrix n)⁻¹ *ᵥ (y - y0)` satisfies `∑ |c_j| ≤ (n+1) · eps = m0/2`
   (row-sum bound via `dist_pi_lt_iff`), so `perturb ρ0 c` is good and has moments
   exactly `y0 + (y - y0) = y`. Hence `ball y0 r ⊆ smoothMomentSet n`.

## Verification (reproducible)

```bash
cd formal
python3 run_lean.py MomentOpen.lean            # exit 0, no errors/warnings (moment_open_build.log)
python3 run_lean.py -o MomentOpen.olean MomentOpen.lean
python3 run_lean.py AxiomCheck.lean            # axiom_check.log
```

`AxiomCheck.lean` output:
```
'RepeatedIntegrals.smoothMomentSet_convex' depends on axioms: [propext, Classical.choice, Quot.sound]
'RepeatedIntegrals.smoothMomentSet_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Toolchain: `.../dlp-research/.tools/lean-4.34.1-linux/bin/lean`, mathlib pinned at
`.../campaigns/2026-10-14/formal/.lake/packages` (d13f23b7). Compile driver: parent's
`run_lean.py` (sets `LEAN_PATH`, cwd-relative).

## Input hashes

- `MomentDefs.lean` (local copy): SHA256
  `8127777ab40d0d005cb13a6edf42a524c3ee8ba066726deddeedd5fe0c3563b2`
- Parent's `.../lanes/parent-repeated-integrals/formal/MomentDefs.lean`: SHA256
  `8127777ab40d0d005cb13a6edf42a524c3ee8ba066726deddeedd5fe0c3563b2` — **byte-identical**.
- `MomentDefs.lean` was **not modified** by this lane.

## Scope boundaries / what this does NOT claim

- This lane does **not** claim the full conjecture (Conjecture 1.2 / (P_n) of
  arXiv:2512.02151v1) and does **not** claim nonemptiness of the open moment cone,
  dual-cone statements, or the source-level `SourceW n` openness. Parent handles the
  bridges (Stieltjes transform / source side) and final integration/review.
- The theorem proven here supplies the two mathematical premises the parent's
  pipeline was missing: `smoothMomentSet_convex` and `smoothMomentSet_isOpen`.
- Note on interpretation: `smoothMomentSet n` is the set of moment vectors of
  *good* densities (smooth, strictly positive on [0,1], endpoint germs `= 1`). The
  openness argument is *local*: every good density has an open neighborhood of
  moment vectors realized by good densities. Global nonemptiness / identification
  with the conjectured moment cone is out of scope here.

## Files

- `formal/MomentOpen.lean` — the deliverable (single file, namespace `RepeatedIntegrals`,
  imports exact `MomentDefs`).
- `formal/MomentOpen.olean` — compiled object.
- `formal/AxiomCheck.lean`, `formal/axiom_check.log` — axiom verification.
- `formal/moment_open_build.log` — clean compile log (empty output = no diagnostics).
- `formal/MomentDefs.lean`, `formal/run_lean.py` — copied unmodified from parent lane.
