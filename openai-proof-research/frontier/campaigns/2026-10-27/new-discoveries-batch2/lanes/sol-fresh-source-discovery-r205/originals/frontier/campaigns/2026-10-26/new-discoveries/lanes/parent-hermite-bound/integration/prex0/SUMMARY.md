# Pre-cutoff trigonometric bound — formal lane summary

Lane: `pi-hermite-prex0-formal` (solo, own lane only; no parent/shared edits,
no git staging/commits, no external contacts). Date: 2026-10-27.

## Scope

Deliverable: one self-contained Lean 4 / Mathlib lemma needed for the
"Bound before x0" step (section 4) of the parent Hermite346243 proof
(`lanes/parent-hermite-bound/PROOF.md`, tail checkpoint `TAIL-CHECKPOINT.md`
@ parent). The parent helpers were **not** mutated or copied; nothing from
the parent proof is assumed.

Main theorem (`HermiteEnvelope.preX0_sin_sq_bound`, in
`formal/PreOriginTrig.lean`):

    theorem preX0_sin_sq_bound (E : ℝ) (hE : 7 ≤ E) (u : ℝ) (hu : 0 ≤ u)
        (hu2 : u ≤ √2) :
        (1 - u^2 / E^2) * Real.sin (√(1 - 2/E^2) * u)^2
          ≤ (49/50) * (1 - 2/E^2)

Exactly the requested statement: real `E, u`, `E ≥ 7`, `0 ≤ u ≤ √2`,
`c = √(1 - 2/E²)`; no extra hypotheses, no assumed conclusion.

## Supporting declarations (all in `HermiteEnvelope`)

1. `ge_zero_of_deriv_nonneg` — generic calculus helper: derivative ≥ 0 on
   `(0,∞)` and `f 0 ≥ 0` imply `f ≥ 0` (via `monotoneOn_of_deriv_nonneg`).
2. `cos_le_poly4` — degree-4 alternating Taylor **upper** bound
   `cos t ≤ 1 - t²/2 + t⁴/24` for `t ≥ 0` (first ladder rung; needed to start
   the induction, not used numerically in the final bound).
3. `sin_le_poly5` — `sin t ≤ t - t³/6 + t⁵/120` for `t ≥ 0`.
4. `cos_ge_poly6` — `1 - t²/2 + t⁴/24 - t⁶/720 ≤ cos t` for `t ≥ 0`.
5. `cos_sqrt2_ge_seven_45` — `7/45 ≤ cos √2` (degree-6 bound at √2:
   `1 - 1 + 4/24 - 8/720 = 7/45`).
6. `sin_sqrt2_le_seven_tenth_sqrt2` — `sin √2 ≤ (7/10)√2` (degree-5 bound:
   `√2(1 - 1/3 + 1/30) = (7/10)√2`).

## Proof route (as suggested, completed)

- `M(u) = (1 - u²/E²)·sin²(cu)` is **strictly increasing** on `[0, √2]`:
  `M'(u) = 2 sin(cu)·[c(1-u²/E²)cos(cu) - (u/E²)sin(cu)]` and the bracket is
  positive because
  - `9/10 ≤ c ≤ 1` (from `E ≥ 7`, `1 - 2/E² ≥ 47/49 ≥ 81/100`),
  - `0 ≤ cu ≤ √2 < π/2` (using `π > 3 > 2√2`),
  - `cos(cu) ≥ cos √2 ≥ 7/45` (cos antitone on `[0,π]` + degree-6 Taylor),
  - `c(1-u²/E²)cos(cu) ≥ (9/10)(47/49)(7/45) = 329/2450` while
    `(u/E²)sin(cu) ≤ √2/49 ≤ 2/49 < 329/2450`,
  - `sin(cu) > 0` for `u ∈ (0,√2)`.
  Strict monotonicity via `strictMonoOn_of_deriv_pos` on `Icc 0 √2`
  (differentiability of `M` supplied by explicit `HasDerivAt` composition).
- Hence `M(u) ≤ M(√2) = (1-2/E²)·sin²(c√2)` (`u = 0` case is `M 0 = 0`).
- `sin(c√2) ≤ sin √2 ≤ (7/10)√2` (sin monotone on `[-π/2, π/2]`), so
  `sin²(c√2) ≤ 49/100·2 = 49/50`, giving `M(√2) ≤ (49/50)(1-2/E²)`.

The Taylor bounds were **proved from first principles** by a derivative
ladder (no assumed trig bounds): `sin t ≥ t - t³/6` (Mathlib
`Real.sin_ge_sub_cube`) ⇒ `cos t ≤ 1 - t²/2 + t⁴/24` ⇒ `sin t ≤ t - t³/6 + t⁵/120`
⇒ `cos t ≥ 1 - t²/2 + t⁴/24 - t⁶/720`, each rung an application of the
monotonicity helper. Mathlib precise bounds were used where present
(`Real.sin_ge_sub_cube`, monotonicity/positivity lemmas); no Mathlib lemma
gives the degree-5/6 two-sided bounds directly.

## Verification

- Toolchain: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`;
  Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` from the pinned packages
  directory (`2026-10-14/formal/.lake/packages`).
- `formal/PreOriginTrig.lean`: compiles with `warningAsError = true`,
  `autoImplicit = false`; log **0 bytes** (`prex0-module.log`).
- `formal/PreOriginTrig.olean`: produced by the runner (`prex0-olean.log`, 0 bytes).
- `formal/PreOriginTrigAxioms.lean` → `prex0-axioms.log`: `#check` and
  `#print axioms` on **every** new declaration (all 7). Only
  `propext, Classical.choice, Quot.sound` (standard3). No `sorry`, `admit`,
  `axiom`, `native_decide`, or unsafe features anywhere.
- Actual compiled types were read from the `#check` output above (they match
  the requested statement verbatim; `c` appears spelled out as
  `√(1 - 2/E^2)`).
- Runner `formal/run_lean.py` copied verbatim from the parent lane;
  commands recorded in `prex0-build.json` (includes SHA-256 hashes).

## Independent numerical sanity (NOT a proof)

Float grid over `E ∈ {7, 7.3, 10, 50, 1000}` and 2001 points `u ∈ [0, √2]`:
minimum margin `(49/50)(1-2/E²) - M(u) > 4.3×10⁻³`; worst point near
`u = √2, E = 7`, consistent with the proof's tight constants
(`sin²√2 ≈ 0.9757 ≤ 0.98`). Sanity only.

## Gaps / limits

- This lane proves **only** the pre-cutoff trigonometric lemma. It does not
  prove the Hermite conjecture, the odd initial comparison (assigned to
  another live worker), the energy-loss step, or any assembly; those remain
  with the parent lane.
- The bound is the one requested; a stronger constant was not pursued
  (numerically the inequality has slack ≥ 4.3×10⁻³ on the tested grid).
- `cos_le_poly4` is a ladder rung only; it is not needed in the final
  numerical chain but is included as the base case of the Taylor ladder.
- No manuscript, no count claims, no discovery credit: helper lemma for the
  parent integration, credit 0.

## Files (all inside this lane)

- `formal/PreOriginTrig.lean` — the lemma module (7 public declarations).
- `formal/PreOriginTrig.olean` — compiled olean.
- `formal/PreOriginTrigAxioms.lean`, `prex0-axioms.log` — #check/#print axioms.
- `formal/run_lean.py` — runner (verbatim copy of parent's).
- `prex0-module.log`, `prex0-olean.log` — build logs (both 0 bytes).
- `prex0-build.json` — machine-readable build record + hashes.
- `SUMMARY.md` — this file.
