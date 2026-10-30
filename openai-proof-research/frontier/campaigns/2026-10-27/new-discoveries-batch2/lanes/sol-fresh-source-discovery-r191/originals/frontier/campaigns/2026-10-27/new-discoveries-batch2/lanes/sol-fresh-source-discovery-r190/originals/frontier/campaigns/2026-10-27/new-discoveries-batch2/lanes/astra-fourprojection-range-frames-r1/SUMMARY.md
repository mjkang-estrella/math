# Canonical projection range frames — complete support module

**PASS: the assigned frame-construction and source-input-data work is complete.** No source inequality, novelty, acceptance, or discovery credit is claimed.

`formal/RangeFrames.lean` imports this lane's exact copies of the stable root `ProjectionFrames.lean` and `HSBridge.lean`. Root files and shared ledgers were not edited.

## Interfaces for integration

All declarations are in `FourProjection`. Put `import RangeFrames` and `open scoped Matrix` in the consuming module. Use `classical` when manipulating the noncomputable finite spectral-support indices.

For `{N : Type*} [Fintype N] [DecidableEq N]`, `{P R : Matrix N N ℂ}`, `hP : P.IsHermitian`, `hR : R.IsHermitian`, `hPP : P*P=P`, and `hRR : R*R=R`, define:

```lean
let p := projectionFrame hP
let r := projectionFrame hR
let E := projectionPairFrame hP hR
-- E : Matrix N (ProjectionFrameIndex hP ⊕ ProjectionFrameIndex hR) ℂ
-- E is definitionally Matrix.fromCols p r
```

| Interface | Proven conclusion |
|---|---|
| `projectionFrame_isometry hP` (copied) | `pᴴ * p = 1` |
| `projectionFrame_mul_adjoint hP hPP` | `p * pᴴ = P` |
| `projection_mul_frame hP hPP` | `P * p = p` |
| `projectionFrame_mulVec_injective hP` | `Function.Injective p.mulVec` |
| `projectionFrame_range hP hPP` | `LinearMap.range p.mulVecLin = LinearMap.range P.mulVecLin` |
| `projectionFrame_coordinates hP hPP v hv` | unique x with `p *ᵥ x = v`, for v in the source range |
| `projectionFrame_surjOn_range hP hPP` | `Set.SurjOn p.mulVec Set.univ (LinearMap.range P.mulVecLin)` |
| `range_inf_eq_bot_iff P R hPP hRR` | literal range-intersection condition iff every common fixed vector is zero |
| `projectionPairFrame_injective hP hR hPP hRR hdisj` | `Function.Injective E.mulVec` |
| `projectionPairFrame_mul_adjoint hP hR hPP hRR` | `E * Eᴴ = P + R` |
| `projectionPairFrame_selector_left hP hR hPP` | `E * frameSelectorLeft _ _ * Eᴴ = P` |
| `projectionPairFrame_selector_right hP hR hRR` | `E * frameSelectorRight _ _ * Eᴴ = R` |
| `projectionPairFrame_gram hP hR` | `Eᴴ * E = Matrix.fromBlocks 1 (pᴴ*r) (rᴴ*p) 1` |
| `projectionPairFrame_gram_diag hP hR` | `Matrix.diag (Eᴴ * E) = 1` |
| `projectionFrames_cross_eq_zero hP hQ hPP hQQ hPQ` | `pᴴ * q = 0` |

The exact hypothesis `hdisj` is
`LinearMap.range P.mulVecLin ⊓ LinearMap.range R.mulVecLin = ⊥`.
The cross-Gram hypothesis `hPQ` is `P * Q = 0`.
The selectors are exactly `Matrix.fromBlocks 1 0 0 0` and `Matrix.fromBlocks 0 0 0 1`.
Generic versions `fromCols_mulVec_injective`, `fromCols_selector_left/right`, `fromCols_gram`, and `fixed_frames_cross_eq_zero` support externally named frames if needed. Instantiate the pair lemmas with Q/S for the second source pair; no duplicated construction or rank comparison is needed.

No theorem assumes frame existence, nonempty types, rank balances, or ambient invertibility. Zero-rank projections and singular P+R are included. The Gram theorem asserts identity diagonal **blocks**, not that the entire Gram matrix is identity.

## Validation and provenance

Run `python3 verify.py` from any directory using this file's absolute path if needed. It rebuilds the copied dependencies and new module with the specified Lean 4.34.1 binary, pinned mathlib build path, and `-DwarningAsError=true`; then runs both the readable and fully explicit declaration audits. It rejects forbidden proof tokens and any axiom outside `propext`, `Classical.choice`, `Quot.sound`.

- `logs/Checks.log`: actual public types and actual axiom reports, read after compilation.
- `logs/ExplicitChecks.log`: actual fully explicit types, including typeclass arguments, and the same axiom reports.
- `logs/HSBridge.log`, `logs/ProjectionFrames.log`, `logs/RangeFrames.log`: clean successful compiler outputs.
- `verification.json`: successful command return codes, Lean version, per-declaration axioms and source hashes.
- `provenance.json`, `SOURCE.md`: copied-input hashes, source statement, and exact scope.

All audited declarations use only the standard three permitted axioms. No sorry/admit/axiom/unsafe/native_decide appears in the support source.

Remaining work belongs to integration: connect these inputs with the separate polar, graded and block-inequality modules and prove the literal source endpoint. This lane did not perform an independent adversarial review, prior-art clearance, paper preparation, or final extracted source-proof replay. Those acceptance gates remain with root.
