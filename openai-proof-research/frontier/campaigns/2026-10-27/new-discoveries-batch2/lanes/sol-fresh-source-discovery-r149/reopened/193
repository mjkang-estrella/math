# Independent review: Yuster polynomial-root conjecture, MathDB 357503

Date: 2026-10-26. **Source, mathematics, independent exact arithmetic, and the complete seven-module Lean certificate PASS53.** Novelty recommendation: provisionally accept one substantive counterexample under the documented-prior/no-known-resolution standard, with final manuscript review and packet bindings separate. No claim of exhaustive priority, minimal k, an exact total number of roots, or a new entropy inequality is supported here.

## Actual target and definitions

The actual latest arXiv history for Raphael Yuster, *Almost k-union closed set systems*, [2302.12276](https://arxiv.org/abs/2302.12276), has only v1 (23 February 2023). I read the primary HTML and downloaded the actual v1 PDF; visually inspected PDF pages 7–9 show Corollary 3.7, its exact rho/sigma formulas and recurrence, and Conjecture 3.9. The conjecture is universally quantified over the integer k≥2 from Section 3 and asserts that p_k has at most two roots in (0,1), counting multiplicity. The counterexample k=48 respects this domain.

The source defines ψ_k as the unique [0,1] root of (1−ψ)^k=ψ, φ_k=1−ψ_k, α_k=φ_k^(k−1). Hence φ+φ^k=1, φ(1+α)=1, and α(1+α)^(k−1)=1. This last equation alone is not a license to choose an arbitrary coefficient: the Lean construction actually builds the source φ and ψ, proves the source uniqueness, and then defines α as the exact source power. Its α is therefore the correct source coefficient, not a rational substitution or approximate eigenvalue-style parameter.

The coefficients satisfy C(k,0,0)=1/(k−1)!, C(k,0,j)=0 for j>0, C(k,t,0)=0 for t>0, and for positive t,j,

    C(k,t,j)=(kj−t+1)C(k,t−1,j)+k C(k,t−1,j−1).

Corollary 3.7 defines p_k=α_k rho_k−sigma_k with precisely the two finite sums in `YusterPolynomial.lean`. I checked all indices: j=0,…,k−1; sourceC index j+2 at t=k+1; factorial j!; exponent k−j−1; exponent kj+k; binomial (k+1 choose j+2); geometric sum through k−1; and the subtracted (x^k−1)^k term in each summand. These match actual PDF page 8. The integral dynamic row equals (k−1)! C, and the implementation divides by that factorial before forming rho. The signed factor kj−t+1 uses integers/rationals, never truncated natural subtraction. Natural exponent subtraction is safe since j<k in every summand.

I also read the source author's generator at pinned public commit `c41ecb533f7fa7f8d727764a2adc05b4ca345ff1` of `raphaelyuster/almost-k-union-closed`. It constructs the same sums and divides its integral coefficient row by (k−1)!. Its only top-level example is k=4; it states no general resolution or counterexample.

The independently retrieved live MathDB post UUID `87450769-71a2-4415-98b7-6f1e11e01647` has empty solutions and repeats the root-count target. Its references field inaccurately labels the source solved by quoting a passage about an earlier union-closed result. That metadata error is **not** the proposed discovery. The actual primary conjecture and an exact four-root counterexample are the target and mathematical outcome.

## Independent arithmetic and four roots

I did not import the author's experiment, recurrence implementation, FLINT output, or Lean finite-certificate values. Instead `check_signs.py` computes C by the independent closed formula

    C(k,t,j)=t!/((k−1)!j!) Σ_(a=0)^j (−1)^(j−a) binom(j,a) binom(ka,t).

This follows by extracting [z^t] from ((1+z)^k−1)^j and the chain-rule expansion; it is a finite-difference coefficient formula. Exact Fraction arithmetic then evaluates the literal original Corollary 3.7 sums. As normalization checks, the k=2 and k=3 rho/sigma evaluations at 0,1/3,2/3 match the source Table 2 expressions.

Let a=61/1000 and b=613/10000. Exact arithmetic checks a(1+a)^47<1<b(1+b)^47. The function u↦u(1+u)^47 is strictly increasing for u≥0, so the canonical α_48 belongs to (a,b). At all five sample points rho_48 is strictly negative. Both endpoint evaluations a rho−sigma and b rho−sigma have the following exact signs:

| x | 1/100 | 1/10 | 1/2 | 3/5 | 4/5 |
|---|---|---|---|---|---|
| sign p_48(x) | − | + | − | + | − |

The dependence on α is affine, so the same strict signs hold throughout the closed coefficient interval, in particular for α_48. The certificate is `independent-sign-certificate.json`, SHA256 `175f133d61a96b666bba8da9a29b0ecfcfca874ad0141f4302476a7c71adbc56`.

Polynomial continuity and the intermediate value theorem now give roots in four pairwise disjoint open intervals:

    (1/100,1/10), (1/10,1/2), (1/2,3/5), (3/5,4/5).

Strict endpoint signs exclude all shared endpoints. Each interval lies in (0,1). The resulting four roots are distinct, which already contradicts an upper bound of two counting multiplicity. There is no need to prove simple roots or to determine the other roots of the degree-2303 source polynomial. No denominator has been cleared in the construction: the certificate evaluates the literal source polynomial itself. Even if one reinterprets it as the numerator of the (k+1)-st entropy derivative, its denominator x(x^k−1)^k is nonzero throughout (0,1), so it introduces no extra interior roots.

The source's entropy inequality is not disproved. Yuster's Lemma 3.10 is a one-way implication from this proposed root bound to the entropy inequality. Its converse is neither stated nor valid in this counterexample. More oscillations of a high derivative are consistent with a nonnegative original function.

## Closest later literature and novelty boundary

Tanay Wakhare, *Iterated Entropy Derivatives and Binary Entropy Inequalities*, [2312.14743v2](https://arxiv.org/html/2312.14743v2), latest arXiv revision 14 January 2025, published Journal of Approximation Theory 307 (May 2025), 106143, DOI [10.1016/j.jat.2025.106143](https://doi.org/10.1016/j.jat.2025.106143), states the generalized exact-two-root Conjecture 2. Its primary arXiv body gives formulas (1.3), (1.4), the functional equation, and the derivative rational forms; the publisher's accessible indexed primary excerpt repeats this conjecture. Direct full publisher-page retrieval was 403, so the full published bytes have not been independently read. The primary arXiv v2 was read, not merely its abstract.

For r=1, comparing Wakhare's actual rational derivative formula (Theorem 4, equation 1.7) with Yuster Corollary 3.7 gives on (0,1), and hence as a polynomial identity,

    p_W(k,1;x)=(-1)^(k+1) (1−x)^k p_Y(k;x)/k.

The factor is nonzero on (0,1); it changes neither the interior roots nor their multiplicities. I independently checked both rho and sigma parts of this identity at every sample point by separately evaluating Wakhare's equation (1.3) binomial sums, not reusing sourceC. `check_wakhare.py` and `wakhare-relation-check.json` record those checks (certificate SHA256 `9291bc1a68d06440352789796fdb3800b396036a08d865185209d1dffcec7e69`). The identity itself follows from the two published derivative formulas; the sample checks only cross-check normalization. Thus the same mathematical example also contradicts Wakhare's Conjecture 2 at (48,1). This is the **same one result**, not another count. If the final packet does not formalize the Wakhare identity, its formal scope must remain the literal Yuster polynomial while explaining the related consequence in the paper.

Boon Suan Ho, *A generalization of Boppana's entropy inequality*, [2601.19327v1](https://arxiv.org/html/2601.19327v1), latest history only 27 January 2026, proves the entropy inequality for all real k>1 and characterizes equality, with Lean formalization. I read its full primary four-page argument. It uses the first derivative of the entropy ratio and logarithmic-mean monotonicity, not the proposed high-derivative polynomial root bound. It neither proves nor refutes the root-count conjecture. It credits Yuster/Yashfe's November 2024 seminar for the entropy cases k≤20; that primary seminar abstract still describes the root statement as a conjectural reduction. Those earlier entropy results are not new here.

I additionally screened the actual August 2026 primary *GPT, the Counterexample Machine*, arXiv:2608.29595v1, and its public repository inventory pinned at `dbf673741a54c7dc9d88a6aec0e8148a538f4a3a`. Its listed counterexamples and repository paths contain no Yuster/Wakhare entropy-root result. Targeted searches for Yuster Conjecture 3.9, Wakhare Conjecture 2, entropy-polynomial root counterexamples and the parameter 48 found no earlier explicit resolution. The local pinned upstream manuscript catalogue search also found no corresponding claim.

This bounded literature screen supports acceptance under the documented-prior/no-known-resolution standard; it is not a proof of global novelty. The example is substantive: it refutes an actual all-degree conjecture using its canonical irrational coefficient, not a source typo, altered polynomial, bounded sufficient lemma, or already proved entropy case.

## Independent formal replay of frozen author modules

The owned copies of the five frozen modules were read and freshly compiled with pinned Lean 4.34.1 and warnings-as-errors. **PASS, all 44 local declarations; only propext, Classical.choice, Quot.sound.** No sorry, admit, custom axiom, unsafe declaration, or native_decide was used. The finite checks use ordinary kernel reduction (`decide +kernel`). Receipt: `build/fresh-audit-kk08ls9i/receipt.json`.

| Module | SHA256 |
|---|---|
| YusterCoefficients | 5a29ee8715c65239d2938eddaed9c06a2b9c0beb7754428e77a2b7b08c6a0a00 |
| YusterPolynomial | 11b3c70422403f12c24a8976515c54122f3451e10201fab4429bd85f8fa19c3b |
| YusterArithmetic | 36c369ff7425bc08fce24a98f337b0025387a6260de590bcd2355e0a089433eb |
| YusterAlpha | f6b2e4c0b72e50f8e2cd2ccaa19d49d7c74b6babb31fe91a252ddaa1519b3510 |
| YusterSigns | 17d5938f82fee85b2622366124dcaa5b1d01cdbfb829d16607b1a2bdcfa4f9e5 |

The main frozen endpoint `sourceP_signs` is exactly the five strict signs of `sourceP 48 sourceAlpha48`. Alpha is built by IVT with the source ψ/φ normalization and its actual defining power, not supplied as a hypothesis. The original coefficient recurrence is fully realized, and literal rational evaluation is connected to real polynomial evaluation. Sign transfer correctly uses the lower α endpoint for negative evaluations and the upper endpoint for positive evaluations, because rho<0.

These five modules alone do **not yet state the four-root existence or final negation**. The mathematical IVT/counting argument above checks independently, but its parent-authored final Lean wrapper and final manuscript remain to review when frozen. This report does not mark that unfinished formal endpoint complete.

## Complete source root-count endpoint: independent PASS53

The final `FourRoots.lean` SHA256 `9d8b6dd58281d222e2768428dd3e9b0b02785c667db6e7595097b15b09d6e656` and `YusterRootCounterexample.lean` SHA256 `e22fdccf02e86ccb9518bc6c9ecf21e9c329bffe67cead501367c58edab8effb` were independently read, copied, and freshly replayed with the five unchanged source modules. **All 53 local declarations PASS**, pinned Lean 4.34.1, warnings-as-errors, and every declaration depends on at most `propext`, `Classical.choice`, `Quot.sound`. Receipt: `build/fresh-audit-wmvh3tvi/receipt.json`. This final replay supersedes the earlier report's unfinished-wrapper qualification.

The IVT lemmas use polynomial continuity and strictly opposite endpoint signs to select roots in open intervals, so roots cannot coincide at the rational dividing points. The wrapper then orders four roots strictly inside (0,1). `interiorRootCount` is the cardinality of the **multiset** `p.roots` filtered by 0<x<1; this is the real-root count with multiplicities, not a distinct-root proxy. The proof first establishes that p is nonzero from its negative sampled value, inserts four strictly ordered roots into the filtered-root toFinset, and then uses the inequality between the finite-set cardinality and multiset cardinality. Thus the four distinct roots rigorously imply a multiplicity count at least four. Zero-polynomial root conventions are irrelevant because nonzeroness is proved.

The final theorem `source_conjecture_357503_false` negates the universal statement for all natural k≥2 and all ψ∈[0,1] satisfying (1−ψ)^k=ψ, with the coefficient defined as (1−ψ)^(k−1). It instantiates k=48 and the canonical sourcePsi48 whose source equation and interval membership were proved in the unchanged alpha module, then identifies the resulting power with sourceAlpha48. This is exactly the source's defining parameter, with no additional hypotheses, auxiliary coefficient interval premise, approximate α, dimension restriction, or alternative polynomial left in the endpoint. The resulting contradiction uses the proved count≥4 versus count≤2.

Final recommendation: **ACCEPT the mathematical and formal resolution of the literal Yuster root-count conjecture as one substantive counterexample**, under the bounded prior-art standard described above. Wakhare's equivalent r=1 formulation supplies no second count; its general identity was checked mathematically from the primary derivative formulas but is not an extra endpoint in this Lean packet. The known true entropy inequality remains outside the claimed refutation. Final manuscript byte/scope review remains separate.

## Final manuscript independent review: PASS

I independently read the complete parent-authored final TeX `candidates/yuster-rootcount/main.tex`, SHA256 `0e59b5110e5fbbe404442035a4d3c3fbce452f8873ecbdcb0637ada0c856f409`. **Math, source fidelity, formal scope, credit, and claim qualification PASS.** The literal rho/sigma formulas, source factorial normalization, canonical psi/phi/alpha, rational interval, endpoint sign selection, and four disjoint open root intervals agree with the independently checked source and complete 53-declaration certificate. The manuscript claims at least four roots rather than an exact root count or smallest counterexample; it does not refute Ho's known entropy inequality or count Wakhare's formulation separately. The source record's inconsistent solved metadata is correctly explained. Missing full Yuster–Yashfe manuscript and unread separate published Wakhare body are stated as limits, with no exhaustive priority claim. Parent owns PDF rendering/layout QA; this is an independent mathematical/text/scope review. This paragraph binds the final paper without changing the frozen certificate.
