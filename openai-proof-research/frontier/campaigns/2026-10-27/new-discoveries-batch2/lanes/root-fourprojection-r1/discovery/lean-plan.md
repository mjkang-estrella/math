# Literal Lean completion plan — currently incomplete

The eight declarations in `../formal/ScalarCore.lean` and `../formal/SpectralCore.lean` are compiled with the pinned absolute Lean 4.34.1 binary and the supplied mathlib build. They prove the scalar spectral comparison and its full finite rectangular-array aggregation. Their actual assumptions are visible in the source and type report. They do **not** state the four-projection theorem. No axiom or assumed proposition stands in for the missing bridge.

## Required literal endpoint

For any finite index type n and P,Q,R,S : Matrix n n ℂ, assume each is Hermitian and idempotent, P*Q=0, R*S=0, and disjoint ranges for (P,R) and (Q,S). The source's two rank equations can be included in its corollary, though the proposed proof establishes the stronger endpoint without them. Define

    mpInvSqrt X := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) X
    P' := mpInvSqrt (P+R) * P * mpInvSqrt (P+R)

and analogously R',Q',S'. For a finite Hermitian PSD matrix this cfc is the eigenvalue function t ↦ 1/sqrt(t), with value zero at t=0, exactly the positive Moore–Penrose inverse square root. The final proposition must be

    (Matrix.trace (P'*Q' + R'*S')).re ≤ (Matrix.trace (P*R + Q*S)).re.

The existence and correctness of this interpretation must be proved; using nonsingular inverse on the original possibly singular square matrix is NOT a valid substitute.

## Modules still required (all genuine proofs, no assumed bridges)

1. **RectangularFrames.lean.** Obtain an orthonormal basis of each projection's range, via the finite-dimensional `stdOrthonormalBasis`/`exists_orthonormalBasis` interface (`Analysis/InnerProductSpace/PiL2.lean`). Form rectangular column matrices p,q,r,s. Prove pp*=P etc. Disjoint ranges imply injectivity of [p r] and [q s]. Handle empty index types.
2. **PolarFrameBridge.lean.** Establish the finite-spectrum cfc formula for the inverse square root; prove `(EE*)^{†/2} E = E(E*E)^{-1/2}` for injective E, either with a reduced spectral construction or intertwining of cfc on the finite union of spectra. Prove U*U=I and the exact P',R' formulas. This is the most substantial remaining formal infrastructure, not a trivial renaming step.
3. **GradedSpectralBridge.lean.** G=E*E, H=F*F, A=G-I, B=H-I; build coordinate-sign involutions J,L. Derive JAJ=-A, LBL=-B and J(E*F)L=−E*F. Show G and 2I−G positive definite, so every eigenvalue of A has square <1. Use `Matrix.IsHermitian.eigenvectorUnitary`, `.conjStarAlgAut_star_eigenvectorUnitary`, and `.spectral_theorem`, which are present in the pinned `Analysis/Matrix/Spectrum.lean`. `Analysis/Matrix/HermitianFunctionalCalculus.lean` contains the finite-spectrum cfc representation. Derive the actual entrywise square-root relation in the two separate eigenbases.
4. **HilbertSchmidtBridge.lean.** Prove row/column bounds for U*V and J(U*V)L using the isometry identities; prove preservation under the two unitary basis changes. Express HS norm as sum of `Complex.normSq`; prove the diagonal-block norm identity and trace/cross-Gram identity. Show Tr(A²)=2Tr(PR), Tr(B²)=2Tr(QS).
5. **FourProjection.lean.** Instantiate `FourProjection.spectral_core` with the actual spectral arrays, discharge ALL its assumptions using 1–4, and conclude the literal trace endpoint. Only then add the source hypothesis/rank-balance corollary.

## Acceptance boundary

No source theorem is yet a Lean declaration in this lane. The complete ordinary mathematical proof is in `proof.md`, including the literal Moore–Penrose bridge. A successful replay of the current eight core declarations must not be reported as completion of Conjecture 6.6. The future literal theorem still needs independent source/math/formal review and an extracted strict replay. All permitted axioms are limited to propext, Classical.choice, Quot.sound.
