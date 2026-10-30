The requested polar normalization bottleneck is fully proved in `formal/PolarFrameBridge.lean`. This is reusable infrastructure, not a proof of Banica–Nechita Conjecture 6.6 and not a discovery/count claim.

Fresh strict replay: **PASS**, 22 public declarations (4 definitions and 18 theorems), plus 2 private proved helpers and 4 boundary examples. Every public declaration's actual type and `#print axioms` output was inspected. The only axioms reported are `propext`, `Classical.choice`, and `Quot.sound`. No prohibited proof holes, new axioms, unsafe code, or native decision procedure occurs in the sources.

The frozen candidate was read only. All **46** paths in its preliminary hash manifest still match. Its commit label `74f23e9fb2` is supplied by the task; no git operation was used to independently query it.

Main interfaces, all in namespace `FourProjection`:

- `mpInvSqrt A := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) A`.
- `mpInvSqrt_spectral hA` proves equality to the actual unitary spectral formula with diagonal entries `((sqrt (hA.eigenvalues i))⁻¹ : ℂ)`.
- `mpInvSqrt_posSemidef hA`, `mpInvSqrt_zero`, and `mpInvSqrt_mulVec_eq_zero hA x hx` establish positivity and annihilation of the kernel. Thus on positive semidefinite matrices this has exactly the source's positive Moore–Penrose support reading. Negative spectral inputs are outside that interpretation; the total real function is still defined there.
- `invSqrt A` is the same total CFC operation, used on the positive definite column Gram matrix. `mpInvSqrt_sandwich_of_posDef hA` proves `mpInvSqrt A * A * mpInvSqrt A = 1`.
- `mpInvSqrt_mul_eq_mul_invSqrt E` proves `mpInvSqrt (E * Eᴴ) * E = E * invSqrt (Eᴴ * E)` for **every** finite rectangular complex matrix, without a rank hypothesis.
- `polarFrame E := E * invSqrt (Eᴴ * E)`.
- `polarFrame_eq_mpInvSqrt_mul E` identifies this with the literal ambient support normalization.
- `polarFrame_isometry E hE` proves `(polarFrame E)ᴴ * polarFrame E = 1`, with the sole mathematical hypothesis `hE : Function.Injective E.mulVec`.
- `normalized_congruence E C` proves the exact formula
  `mpInvSqrt (E * Eᴴ) * (E * C * Eᴴ) * mpInvSqrt (E * Eᴴ) = polarFrame E * C * (polarFrame E)ᴴ`
  for every coordinate matrix `C`, without rank, Hermitian, or idempotence hypotheses.
- `normalized_congruence_is_projection E hE C hC hCC` proves Hermitianity and idempotence when `C` is an orthogonal projection.
- `coordinateProjection s` is the diagonal selector of a `Finset n`; its Hermitianity, idempotence, exact normalized formula, and normalized orthogonal-projection property are proved.

The generic reusable ingredient is `hermitian_cfc_intertwine hA hB T h f`:

```lean
(A * T = T * B) → cfc f A * T = T * cfc f B
```

Here `A : Matrix m m ℂ`, `B : Matrix n n ℂ`, `T : Matrix m n ℂ`, both square matrices are Hermitian, and `f : ℝ → ℝ` is arbitrary. Both types are arbitrary finite types, with decidable equality where needed. No continuity premise is required because the spectra are finite. There is no assumed SVD, polar decomposition, spectral existence premise, or reduced-frame existence premise.

Proof mechanism: diagonalize the two Hermitian matrices independently using mathlib's proved spectral theorem. An intertwiner entry between distinct eigenvalues vanishes; between equal eigenvalues applying any common scalar function preserves the equality. Conjugating back proves rectangular CFC intertwining. Apply this to `A=EEᴴ`, `B=EᴴE`, `T=E`. For isometry, mathlib's `Matrix.PosDef.conjTranspose_mul_self` derives positive definiteness from column injectivity. Positive eigenvalues satisfy `(sqrt t)⁻¹ * t * (sqrt t)⁻¹ = 1`; CFC multiplication and the finite spectral formula give the required cancellation. The normalization formula follows by conjugate transpose and associativity.

Dimensions and instance discipline:

- No `Nonempty` hypothesis occurs. Empty ambient and/or column types are included.
- `BoundaryChecks.lean` strictly compiles both-empty, empty-column, and empty-ambient instances, plus an injective `2 × 1` column whose ambient Gram determinant is proved zero while its polar frame is proved isometric.
- This module uses the real Hermitian matrix CFC and proves its spectral identification. It does not use `CStarMatrix`, change matrix norm instances, or use any operator-norm estimate. Consequently no unproved norm transport is involved.
- `open scoped ComplexOrder` supplies the standard real-axis positivity instance needed by `Matrix.PosDef` and `Matrix.PosSemidef`.
- No ordinary inverse of the singular ambient square matrix is used anywhere.

Reproduction from this lane:

```sh
python3 scripts/replay.py
```

The script invokes exactly `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, version 4.34.1, with `-DwarningAsError=true`. It checks the manifest pin `d13f23b723b8a846827a245b89c10fc7d3f11612`, rebuilds local modules in `verification/fresh`, and audits all 22 public declarations. It reuses the pinned compiled mathlib dependencies; it does not rebuild all of mathlib.

Authoritative artifacts:

- `formal/PolarFrameBridge.lean`: implementation.
- `formal/BoundaryChecks.lean`: empty/singular boundary certificates.
- `formal/Checks.lean`: all public type/axiom requests.
- `verification/fresh/Checks.log`: actual types and axiom results.
- `verification/result.json`: compiler, source hashes, axioms, declaration inventory, scope.
- `provenance.json`: input hashes, pinned source URLs, local access limits, frozen-manifest verification.
- `artifacts-sha256.json`: final lane artifact hashes.

Remaining integration belongs to the parent: construct the projection frames from the source hypotheses, prove their column injectivity and the identities `P+R=EEᴴ`, `P=E C_P Eᴴ`, etc.; combine with the HS/trace, graded spectral, and scalar-core arguments; state and prove the literal source inequality. The present lemma does not assume those constructions exist, and does not claim they are implemented. There is no remaining gap in the advertised generic polar/intertwining/isometry/normalized-coordinate formulas themselves. Independent adversarial review and source-conjecture acceptance remain separate gates.

Source scope: cached arXiv:1602.04456v3, printed p.20, Conjecture 6.6 (including the explicit Moore–Penrose convention), and the frozen candidate proof Appendix and Lean plan. No fresh HTTP retrieval, prior-art clearance, priority claim, publication, account mutation, shared edit, or child delegation was performed.
