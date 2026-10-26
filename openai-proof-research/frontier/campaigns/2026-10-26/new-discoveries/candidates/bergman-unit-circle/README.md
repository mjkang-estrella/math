# Full Bergman polynomial conjecture: MathDB368572

This packet proves Edholm–Mathew's published2026 Conjecture4.20 for every pair of coprime positive integers m>n. Their exact degree2(m−n) polynomial Q has no zero on the unit circle and exactlym−n roots in the punctured unit disc, counted with multiplicity. This is one all-parameter outcome; known differences, helpers, root allocation and the analytic kernel consequence are never separately counted.

The central identity on the unit circle is Q(z)=z^(m−n)Σr|Ar(z)|², where Ar(z)=Σp<m z^(p−floor((np+r)/m)). Coprimality gives a single carry index and A1−A0=monomial·(1−z). Thus A0,A1 have no common nonzero root and the sum is strictly positive. The certificate proves all coefficient/reindex identities from the literal source numerator, not as premises. It also constructs an ordinary polynomial, proves selected integer exponents nonnegative before converting to natural exponents, proves its exact degree, nonzero constant and reciprocity, and counts the root multiset through full complex factorization.

## Contents and replay

- paper.pdf and main.tex: complete four-page manuscript with source formulas, proof, prior credit and limitations.
- formal/: ten frozen modules,78 declarations. Main endpoint: BergmanUnitCircle.source_full_conjecture_368572.
- reviews/: independent source/math/formal/final-manuscript review and separate parent review of the matrix author's five-declaration allocation helper.
- verification/: exact compiler/dependency pins, independent isolated receipts, declaration types/axioms, rendered-page QA and strict verifier.
- sources/: full MathDB post and primary URLs/hashes; full third-party manuscripts are referenced rather than redistributed.
- scripts/: an independent standard-library finite coefficient-bijection cross-check,71 coprime pairs. Finite checks are not the uniform proof.

With Lean4.34.1 and the exact compiled dependencies in verification/pins.json, run from the extracted packet root:

```sh
python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
python3 scripts/check_bijection.py
```

The verifier checks dependency revisions and tracked cleanliness, compiles isolated byte-identical sources with warnings as errors, and inspects every local declaration's type and axioms. Only propext, Classical.choice and Quot.sound are permitted; no proof holes, new axioms, unsafe or native_decide are used.

The actual full June2026 target publication retains the conjecture. Almughrabi2023 Eq24 already gives the weighted roots-of-unity identity and is prominently credited, as are older triangular kernel formulas and classical algebra. The new conclusion is full strict boundary positivity/nonvanishing and the source conjecture, not a new generic Fourier identity. The source mentions a successor in preparation; no public full version was located. This is a documented, bounded prior-art check, not an absolute priority certificate. See NOVELTY.md and the independent review.

The analytic kernel consequence uses the published kernel formula and an explicit realization of the products. Lean certifies the entire polynomial conjecture; it does not construct Bergman spaces, kernels or proper maps. No external posting, author contact, publication, upload or push occurred.
