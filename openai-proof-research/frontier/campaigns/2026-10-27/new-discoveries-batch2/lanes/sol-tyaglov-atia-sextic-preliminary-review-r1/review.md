# Independent preliminary review

Recommendation to root: **do not invest in Lean or a manuscript; exclude this nomination from substantive discovery credit as a routine consequence of an already public same-object body.** The proposed sextic is nevertheless a correct, full-scope refutation of the pinned universal conjecture. The exclusion has a complete mathematical bridge below; it is not based on shortness, an abstract, or the mere existence of the odd-degree Example 16.2. Root alone decides acceptance. Counts remain 9 additional / 39 total / next 40.

## Separate verdicts

| Gate | Verdict | Scope |
|---|---|---|
| Source | PASS for arXiv v5; published-version comparison HOLD | Actual p24 Conjecture 3 and Eq.3.20 read from independently extracted frozen PDF. Journal body unavailable through permitted routes. |
| Mathematics | PASS | All coefficients, derivative factors, critical values, numerator identity and eight strict sign intervals independently checked exactly. |
| Substantive eligibility | FAIL, routine published-body consequence | 2024 Section 16, specifically Lemma 16.1, already gives a complete positive even-degree refutation after elementary IVT counting. Explicit quartic adaptation below. |
| Novelty | FAIL for discovery-credit clearance; bounded priority HOLD | A complete same-target routine bridge is present. No claim that the exact sextic or the explicit quartic coefficients were previously printed; no exhaustive priority search. |
| Formal feasibility | Feasible in principle, unimplemented | Rational polynomial arithmetic, elementary calculus/coercivity and IVT suffice. No Lean or manuscript work performed or recommended. |

## Source and sextic verification

The pinned body is [Tyaglov–Atia v5](https://arxiv.org/pdf/1912.04951v5), 19 June 2020, SHA256 `7242fff819de94524d106fca14e8da73cf16fd249d391cd580f69a30de459ab6`. Conjecture 3, printed p24, quantifies over real polynomials of even degree n=2m having only nonreal zeros and having a derivative with only real zeros. It does not require an even function or forbid odd-powered terms. Eq.3.20 defines Q=(pp''−κ(p')²)/p². Its middle clause, 1/2<κ≤(n−1)/n, bounds the number of real zeros by Z_C(p). Counts include multiplicity. Eight distinct zeros already contradict that upper bound at n=6, regardless of total count.

Independent integration of 300(x+13)(x+2)(x+1)(x−3)(x−13), with constant 108312103, recovers exactly

P=50x^6−13200x^4−600x^3+177450x²+304200x+108312103.

Its critical points −13,−2,−1,3,13 are simple derivative roots. Their respective P-values are 3,108210303,108172803,109772803,5272803; respective P''-values are 16473600,−247500,201600,−960000,16380000. The positive degree-six leading term gives P(x)→+∞ at both ends. Continuity and coercivity give an attained global minimum, at which Fermat's theorem gives P'=0. The exhaustive critical list therefore proves P≥3. This is a global positivity proof, not a sample check.

With κ=3/4 strictly between 1/2 and 5/6, exact multiplication gives 4PP''−3(P')²=1200J, where

J=25x^10−13200x^8−900x^7+414050x^6+1064700x^5+525944015x^4−79953900x^3−57294664659x²−1479679536x+127901873749.

Thus the literal source Q is 300J/P². Exact endpoint evaluations are:

| Interval | J(left) | J(right) |
|---|---:|---:|
| (−20,−19) | 4354463200869 | −4696251086376 |
| (−14,−13) | −266271947271 | 164736 |
| (−13,−12) | 164736 | −184798658075 |
| (−2,−1) | −89273499975 | 72692123616 |
| (1,2) | 69574984344 | −96403570119 |
| (12,13) | −31266038939 | 287895043800 |
| (14,15) | 209008140921 | −472396598816 |
| (19,20) | −2185650428544 | 7526093619429 |

All products are strictly negative. IVT gives eight roots in pairwise disjoint open intervals. The shared boundary −13 is nonzero, so poses no disjointness problem. P² is everywhere positive: no real cancellation or pole issue exists. Consequently the number of real Q zeros is at least eight, whereas P has six nonreal zeros counting multiplicity. This genuinely refutes the universal assertion, not merely a weakened reading. The other two kappa regimes are not separately refuted or credited.

## Decisive complete adaptation of the later body

[Katkova–Tyaglov–Vishnyakova v1](https://arxiv.org/pdf/2406.00686v1), SHA256 `75895ba7d97ad42c4ef96c9d2f230732157f46fca752b549691918b4c3d9cecf`, is publicly dated 2 June 2024. I read definitions 1.1–1.2, main statements including Theorem 2.2, the interval classification in Section 4, and actual relevant Sections 12 and 16. **Theorem 2.2 says κ≥(n−1)/n, including equality**, rather than the strict inequality reported by the candidate. It does not govern κ=3/4 for degree six. The later H is κ(p')²−pp'', and its Q has denominator (p')². On the real line away from P' roots its Q equals −P²/(P')² times the original Q. At a P' root our numerator is PP''≠0. These distinctions preserve our zero comparison while forbidding a blanket identification of the rational functions.

Example 16.2 on p40 is e(x)=x²(x−1)(x−2)(x+10)+1/10. Its degree is five, its derivative is the displayed quartic, and e(3/2)=−1019/160. It is not the required positive even-degree witness. My rational evaluations independently confirm M[e](−27/20)>2/3>M[e](−11/40), where M=pp''/(p')². Together with the opposite infinite limits at the adjacent derivative roots, these give the stated three local crossings. Affine changes preserve odd degree; vertical shifts change M; simply squaring introduces derivative roots from e and offers no automatic real-rooted derivative. Example 16.2 alone is therefore insufficient as an exclusion.

However, the actual surrounding Section 16 gives the missing global bridge. Lemma 16.1 (pp39–40) says that on each infinite interval of the second type there is C in (1/2,(n−1)/n), and there are two zeros there for C≤κ<(n−1)/n. For a strictly positive even-degree polynomial with simple entirely real-rooted derivative, its outer critical points are minima, so both infinite intervals are of that type. Every finite interval between consecutive derivative roots also has opposite infinite M limits because extrema alternate while p stays positive. Hence each finite interval contributes at least one root for every finite κ. Choose κ strictly above the maximum of the two tail thresholds and below (n−1)/n. The two tails contribute four roots and the n−2 finite intervals contribute at least n−2, giving **at least n+2>n**. All intervals are disjoint, and numerator values at derivative roots are nonzero. For even n≥4 this is already a full refutation of the precise source middle clause, using the published body's mechanism and routine IVT. It is not necessary that the later authors label this consequence as a refutation of Conjecture 3.

Here is a complete exact instance, independently certified without relying on that lemma's zero count. Let

W(x)=x^4−2x²+2=(x²−1)²+1, κ=37/50.

Then W≥1, W'=4x(x−1)(x+1) has all three roots real and simple, and 1/2<37/50<3/4. Direct multiplication gives

50WW''−37(W')²=8K, K=x^6−27x^4+126x²−50.

K(0)=−50, K(1)=50, K(3)=−374, K(6)=16150, and K is even. Six disjoint strict sign intervals are (−6,−3),(−3,−1),(−1,0),(0,1),(1,3),(3,6). Thus the original Q=(4/25)K/W² has at least six distinct real zeros, exceeding four. This exhibits every hypothesis and bridge, including positivity, even degree, real-rooted derivative, the middle parameter range and the literal source rational numerator. It is the same source outcome as the sextic, not another eligible discovery. The later body's general tail result plus finite-interval crossing mechanism subsumes the proposed outcome routinely. **This is the concrete basis for substantive exclusion.**

## Coverage, gaps and next disposition

The current arXiv abstract pages and an author/topic API query were retrieved on 30 October 2026 UTC; their version listings still identify the above 2024 v1 and [Gnatyuk–Tyaglov 2506.22330v1](https://arxiv.org/pdf/2506.22330v1). The latter cached primary body, SHA256 `b7b2caae299fb7363dbf3e4eb378b9e55695f3459809f16a20046c50e795bdff`, was read at its definitions, results and relevant proof scope: Eq.1.1 fixes κ=1; Theorems 1.2, 4.5, 4.6 and Conjecture 4.7 concern logarithmic derivatives, Laguerre derivatives and Cauchy indices. They do not supply a κ=3/4 positive-sextic result. Some broad output was truncated; targeted rereads were used. No novelty conclusion comes from its abstract.

For DOI [10.1016/j.jmaa.2020.124652](https://doi.org/10.1016/j.jmaa.2020.124652), Crossref identifies the journal issue as February 2021. The DOI's 2020 string is not the issue year. OpenAlex provides only the publisher and the same arXiv repository as locations; no distinct institutional published body was located. Publisher routes are already denied and were not replayed, proxied or bypassed. Metadata cannot establish whether the journal retains this conjecture verbatim. Published-source comparison therefore remains HOLD, even though the pinned arXiv source gate passes.

Ancestor and batch instructions, ledger and prior-campaign context were read; snapshots preserve 9/39/40. The accepted families contain no matching outcome. The candidate's bounded history and retrieval reports were read as reports, not treated as independent proof-registry clearance. The parked capped-history gaps and denied current registry routes remain parked. No worldwide priority claim is made. These gaps are not needed for the affirmative routine-subsumption objection just proved.

The proper disposition is to preserve the valid arithmetic and counterexample uncredited, with this explicit 2024-body bridge attached. No acceptance, shared ledger change, git operation, public edit, Lean or manuscript investment occurred. Independent checker, exact evidence, URL/date/hash coverage, frozen before/after hashes and separate manifest verifier are included in this directory.
