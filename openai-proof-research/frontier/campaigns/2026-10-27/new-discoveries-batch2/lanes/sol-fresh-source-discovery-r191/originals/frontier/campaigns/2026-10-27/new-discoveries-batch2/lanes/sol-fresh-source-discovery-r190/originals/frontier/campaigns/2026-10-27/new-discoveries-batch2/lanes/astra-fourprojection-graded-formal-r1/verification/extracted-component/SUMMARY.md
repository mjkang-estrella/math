The requested generic graded spectral bridge is **complete and strictly compiled**. This is an implementation component, not the Banica–Nechita source endpoint and not a discovery/count claim.

Fresh replay: **PASS**, using the pinned absolute Lean 4.34.1 binary and mathlib manifest revision `d13f23b723b8a846827a245b89c10fc7d3f11612`, with `-DwarningAsError=true`. All **63 public declaration types and axiom reports** were inspected. This inventory comprises 39 byte-identical imported declarations, 22 new production declarations, and 2 named boundary certificates. There are also 3 anonymous empty-dimension examples. Only `propext`, `Classical.choice`, and `Quot.sound` occur. No proof holes, new axioms, unsafe code, or native decision procedure is used.

The frozen candidate was read only. All **46** files in its preliminary hash manifest still match. `74f23e9fb2` is the supplied candidate label, not a git-query result. No git, shared-file edits, child agents, external messages, accounts, or network requests were used.

Main interfaces are in namespace `FourProjection`:

- `spectralCoords hA hB K` is literally `star hA.eigenvectorUnitary * K * hB.eigenvectorUnitary`. The bases are independently constructed by mathlib for the actual Hermitian matrices. There is no supplied spectral array, simultaneous-diagonalization premise, or assumed spectral bridge.
- `cfc_sqrt_one_add` and `cfc_sqrt_one_sub` identify the actual CFC square roots of `1 ± A` with CFC of the shifted scalar functions on `A`.
- `spectralCoords_cfc_mul` diagonalizes two-sided CFC multiplication entry by entry for arbitrary real scalar functions.
- `sqrt_grading hA G hG hanti` proves `G * cfc Real.sqrt (1 + A) * G = cfc Real.sqrt (1 - A)` from `G*G=1` and `G*A*G=-A`.
- `spectral_entry_relation` turns the actual two-root matrix equation into the scalar entry equation with real weights `sqrt(1+a_i)*sqrt(1+b_j)` and `sqrt(1-a_i)*sqrt(1-b_j)`. Their nonnegativity and exact squares `(1+a_i)*(1+b_j)` and `(1-a_i)*(1-b_j)` are proved inside the matrix endpoint.
- `spectral_bounds` uses membership of the actual eigenvalues in the actual real spectrum. `spectrum_bounds_of_posDef_shifts` additionally derives strict spectral bounds from positive definiteness of `1±A`. `posDef_one_sub_of_grading` derives the negative-shift premise from the positive shift and a self-adjoint unitary grading.
- `GramContractive K` means **both** `(1-K*Kᴴ).PosSemidef` and `(1-Kᴴ*K).PosSemidef`. Its row and column estimates are proved from diagonal positivity. `GramContractive.unitary_change` proves preservation under arbitrary independent unitary changes of the two bases.
- `gramContractive_cross_isometries U V hU hV` proves these two PSD inequalities for `Uᴴ*V` from `Uᴴ*U=1` and `Vᴴ*V=1`. The proof factors the complementary orthogonal projections, then compresses them. No operator norm instance or assumed Bessel inequality is involved.
- `hsSq_spectralCoords` and `trace_square_eq_spectral_sum` connect the scalar sums to the actual HS square and actual matrix traces.

The central endpoint `hermitian_spectral_bound` takes actual Hermitian matrices `A : Matrix I I ℂ`, `B : Matrix J J ℂ`, their strict real-spectrum bounds, rectangular `K,L`, `GramContractive K`, `GramContractive L`, and the equation

```lean
cfc Real.sqrt (1 + A) * K * cfc Real.sqrt (1 + B) +
  cfc Real.sqrt (1 - A) * L * cfc Real.sqrt (1 - B) = 0
```

It proves, by the copied and previously proved `spectral_core`,

```lean
hsSq (K + L) / 4 ≤ (Matrix.trace (A * A) + Matrix.trace (B * B)).re / 2
```

`graded_spectral_bound` specializes to `L = G*K*H` for unitary `G,H`, deriving its contraction rather than assuming it. This direct-equation theorem does not need anticommutation or self-adjointness of the gradings: those are used upstream to obtain the equation.

The most integrated endpoint is `graded_cross_isometry_bound` in `formal/GradingConsequences.lean`. Its only mathematical premises are:

1. `A,B` Hermitian, with `1+A` and `1+B` positive definite.
2. `G,H` self-adjoint unitaries with `G*A*G=-A`, `H*B*H=-B`.
3. Rectangular frames `U : Matrix N I ℂ`, `V : Matrix N J ℂ`, with `Uᴴ*U=1`, `Vᴴ*V=1`.
4. For `X = cfc Real.sqrt (1+A) * (Uᴴ*V) * cfc Real.sqrt (1+B)`, the actual odd-cross identity `G*X*H=-X`.

Its conclusion is the requested HS/trace inequality for `K=Uᴴ*V`, `K'=G*K*H`. It derives the strict spectra, CFC two-root equation, scalar weights, every row/column bound in the independent spectral bases, and the spectral-sum/trace identification. No residual spectral or contractivity bridge is assumed.

All dimensions are arbitrary finite types with decidable equality. There is no nonemptiness or equality-of-ranks premise. `BoundaryChecks.lean` instantiates the matrix theorem for empty rows, empty columns, and both empty; it also proves contraction for the nonzero rectangular column `[1,0]ᵀ` using the isometry theorem.

Exact remaining parent integration:

- Construct the original projection range frames and prove the source-specific identities, injectivity, and the positive Gram hypotheses.
- With `A=Eᴴ*E-1`, `B=Fᴴ*F-1`, `U=polarFrame E`, `V=polarFrame F`, prove the reconstruction identity
  `Eᴴ*F = cfc Real.sqrt (1+A) * (Uᴴ*V) * cfc Real.sqrt (1+B)`
  and the odd-cross equation coming from the two vanishing diagonal blocks. The generic grading/CFC transport after that equation is complete here.
- Identify `hsSq (K+G*K*H)/4` with the primed-projection target traces and identify the RHS trace squares with the original two projection products. This source-specific block/trace integration is assigned to the parent.
- State and prove the literal source endpoint, obtain independent adversarial review, resolve novelty/source gates, write the paper and produce the final full-source packet. This lane performs none of those acceptance steps.

Source scope: cached Banica–Nechita arXiv:1602.04456v3, printed p.20, Conjecture 6.6, including the explicit Moore–Penrose convention; the frozen candidate proof; copied PolarFrameBridge, HSBridge, ScalarCore and SpectralCore. The four copied Lean files are byte-identical to the inputs recorded in `provenance.json`. No new prior-art or priority claim is made.

Reproduce from this lane:

```sh
python3 scripts/replay.py
python3 scripts/packet.py
```

`replay.py` rebuilds all local modules in `verification/fresh`, audits every public declaration, and writes `verification/result.json`. It uses the pinned compiled mathlib dependency library and does not rebuild all mathlib. `packet.py` writes a deterministic component ZIP, freshly extracts it within this lane, runs the same strict replay there, and records the archive hash and extracted result in `verification/packet-result.json`. This is a component packet, not an accepted source-conjecture packet.

Authoritative new sources: `formal/ContractiveBridge.lean`, `formal/GradedSpectralBridge.lean`, `formal/GradingConsequences.lean`; actual type/axiom evidence: `verification/fresh/Checks.log`.
