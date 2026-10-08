# H006 independent rank review (Claude Opus)

Retained reviewer report. Root disposition controls accepted claims; this is not a Lean proof or experiment. Numerical estimates and broad exclusions require separate checking.

I read only the two files: no edits, experiments or delegation. **Verdict: I accept the T1 paper obstruction within the scope you stated, with a few gaps to fill in. The direct-Q repair and the D1 bound are also correct.** I found no error that breaks the argument. ECDLP improvement: none.

## 1. Rank lemma: correct

- Expand F(x0+X, y) = Σ_j a_j(y) X^j, where a_j are the Hasse-derivative coefficients (needed because the characteristic is p) and a_1 = Fx(x0, y).
- a_0 vanishes to order exactly 1 at y0 because Fy(x0, y0) ≠ 0. a_1(y0) ≠ 0.
- A term of c_k that uses m nonconstant factors has order ≥ t − m, and m ≤ k. Equality m = k forces every factor to be a_1, which gives binom(t,k)·a_1^k·a_0^(t−k). Since t < p, this has order exactly t − k.
- So c_0…c_t are independent, which gives rank ≥ t+1. Shifting x and working over an extension field do not change the rank.

**Missing step:** the draft says "D is nonzero by the rank lemma" but never states the bridge. If a bivariate G has rank ≥ r, then det[G(x_i, y_j)] (r×r) is a nonzero polynomial. The proof is Cauchy–Binet plus injectivity of Λ^r U → K[x_1..x_r]. Please write it out.

## 2. S6 specialization: correct, but the draft skips steps

These are the facts the draft needs to state:
- **Nonzero scalar.** F ≢ 0 is an open condition on (P3, P4, P5, R) because S6 ≢ 0 and the x-map is dominant. The other genericity conditions (the 8 K's distinct up to sign, K ∉ E[2]) are also open. A nonempty intersection of open sets in the irreducible E⁴ is nonempty, and F ≢ 0 gives λ ≠ 0.
- **Curves.** C_K = C_{−K}, and C_K ≠ C_{K'} unless K' = ±K. P ↦ (x(P), x(P+K)) is birational onto its image: x(P+K) = x(P−K) forces 2K = 0 or 2P = 0.
- **Exact bidegree (2,2).** Each g_K has bidegree exactly (2,2) because both projections have degree 2. Then (16,16) divisibility in a UFD forces F = λ∏g_K with λ constant. Only the "points sum to O ⇒ S6 = 0" direction of Semaev is needed. The S3 identification is correct but unnecessary.
- **Smooth mixed point.** ∂_y g_K cannot vanish identically on C_K. If it did, g_K would divide it, so ∂_y g_K ≡ 0 and g_K would be a polynomial in y^p, impossible since the y-degree is 2 < p. The same holds for ∂_x. So only finitely many bad points exist.
- **Characteristic.** p > 3 covers Semaev's char ≠ 2,3 requirement. Degree-2 projections are separable.

## 3. Finite-grid transfer: correct, with two wording fixes

- **The powering wording is wrong as written.** Left-to-right binary exponentiation visits prefixes ⌊(p−1)/2^s⌋, not powers of two. Only right-to-left visits 2^j. The addition-chain statement is the correct one: the first chain element ≥ r is ≤ 2(r−1), it is fixed by p and the schedule, and it is independent of V and R. The lemma only needs r ≤ t < p. Drop "power of two" and define t as that first crossing.
- **Allocation rule.** Assign roles by sampling order, or by any rule that ignores the values. Then the 2r+3 base coordinates are uniform over injective tuples, which equals iid uniform conditioned on distinctness.
- **Other checks:**
  - Rejection sampling gives exactly uniform X_E, since there are no 2-torsion points and so N = (q−1)/2.
  - x(R) is uniform on X_E and independent of V, and z needs no distinctness condition.
  - Bound: Pr[D = 0] ≤ 96B²/(q − 1 − B²). Schwartz–Zippel needs only total degree < N, which holds, so "nonzero polynomial" and "nonzero on X_E" are handled.
- **Simplification:** both unfoldings contain the same minor. Use rows (x_i, c1) against columns (y_j, c2, c3), and rows (x_i, c1, c2) against columns (y_j, c3). One event gives r2, r3 ≥ r with no union bound.
- **Citations.** The lower bound r_k ≥ rank(A_k) is the elementary factorization of the unfolding. Oseledets Thm 2.1 is the existence/upper-bound direction. For Semaev, cite the primary ePrint 2004/031 rather than ResearchGate.

## 4. Scope and cost: accept, and state these limits

- **Stored vs. computed.** The middle core is ≥ r²B ≈ B³/4 entries. This bounds work whenever the schedule writes out a dense TT of A^t for the crossing exponent t, whether raw Kronecker cores or compressed (raw ranks are only larger). Fused or implicit schedules that never materialize A^t are outside the claim. Since the first attempt is already expensive with probability 1 − O(q^{−3/5}), the expected total work is ≥ (1 − o(1))·B³/4.
- **Exponent dependence.** Asymptotic only: B³/4 > √q needs roughly q^{1/10} > 4. The claim requires B = q^{1/5 ± o(1)}. It does not cover B ≤ q^{1/6} unless you add a separate yield-per-relation argument, other values of m, or sparse/hierarchical formats, structured or adaptive V, or other ways of computing the indicator. The "not every fixed V" disclaimer is correct; Markov's inequality gives "most V are good for most R".

## 5. Direct-Q repair: correct

- R = (a + bk)G is uniform and independent of b.
- The whole b sequence is independent of (all R_i, V, coins), which determine the stopping time, the row selection, M and λ.
- Conditioned on those, the kept b's are iid uniform, so for any fixed nonzero λ over F_q, Pr[λ·b = 0] = 1/q.
- Full rank of M is not needed. Required conditions: resample R = O using R only, the dependency algorithm's coins must be independent of b, and retry when λ·b = 0. Yield and the cost of the dependency solver stay as open assumptions, as the draft says.

## 6. D1: correct

By linearity, the expected number of decompositions per orbit is ≤ 2^m·B/(q−1). By Markov, collecting B relations with constant probability needs Ω(q/2^m) trials. The scope stays limited to the named non-adaptive procedure, as stated.

**Disposition:** acceptable as a paper rejection of the frozen random-V, identical-grid, dense-TT addition-chain schedule once the fixes above are made: drop power-of-two, specify the allocation rule, write out the Cauchy–Binet bridge and the genericity details, correct the citations, and state the B-exponent limit. It is not a Lean proof, not universal over factor bases or representations, and not a hardness claim for ECDLP.
