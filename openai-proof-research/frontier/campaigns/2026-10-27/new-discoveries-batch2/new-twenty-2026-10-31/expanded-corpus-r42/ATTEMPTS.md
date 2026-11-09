# Mathematical investigations (2026-11-01 UTC)

No acceptance recommendation or new Lean endpoint. All 40 cached literal records were read; only four exact IDs received new primary mathematical body review. Reading a statement is not primary review.

## 349648 — full-scope classical bridge; exclude discovery credit

Source: arXiv:2102.02979v2 (PDF header 18 November 2021), §II notation (N even), §IV final Conjecture 1 and (35). The domain is the continuous interval [0,N], not just integer separations. N=2m is a positive even integer. For θ=πd/m define

h(θ)=Σ_{k=1}^{m−1} cos(kθ)/k² + cos(mθ)/(4m²).

This is exactly g(d); the final coefficient is 1/(4m²), not 1/m². Set S_j(θ)=Σ_{k=1}^j sin(kθ)/k and S_0=0. Finite differentiation gives

−h′(θ) = S_{m−1}(θ)+sin(mθ)/(4m) = (3/4)S_{m−1}(θ)+(1/4)S_m(θ).

Classical Fejér–Jackson says S_j≥0 on [0,π]. Thus h is nonincreasing there. Since each frequency is integral, h(2π−θ)=h(θ); consequently h(π)≤h(θ) throughout [0,2π]. This proves the literal continuous global-minimum statement, including m=1 (S_0=0), with no strictness or uniqueness assertion. The derivative change of variable has positive factor π/m. No omitted Fourier-metric bridge is needed for this exact g-minimum conjecture.

Primary corroboration read: Alzer–Kwong, *Inequalities for sine and cosine polynomials*, Riv. Mat. Univ. Parma 12(2021)301–317: equation (1.1), full Theorem 3.1 proof pp307–309, and Remark 3.2 pp309–310, which explicitly deduces Fejér–Jackson through Lemma 2.6. The proof splits into five intervals/parity cases using Lemmas 2.1–2.5; this pass did not independently reconstruct all those auxiliary estimates. Theorem 3.1's λ=0 case invokes the classical result; Remark 3.2 also derives it from the proved λ=2 case. This is a full-scope explicit classical subsumption bridge, not a claim that these authors discussed MathDB349648. No Lean investment: known/routine consequences are ineligible under the assignment. No universal novelty claim.

## 349674 — exact later published-preprint proof; exclude

Original arXiv:2102.04126, §4.1 Theorem 4 and Conjecture 1; Ω=[−1,1], nodes cos(jπ/n), j=0,…,n−1 (the n+1 Chebyshev–Lobatto nodes with −1 removed). Literal Lagrange products and endpoint value read. Follow-up arXiv:2305.03370, §7 Theorem 3 explicitly proves Λ=2n−1 for the same nodes. Full proof pp10–12 read: decrease below smallest retained node; compare with full CL Lebesgue function; bound the removed endpoint cardinal polynomial; obtain the upper bound on the remaining interval. Apparent prose slip 'tangent is strictly decreasing' occurs in the proof where monotonic increase is the intended elementary fact; this does not create a new research target. Small n needs separate treatment where the printed strict inequality 2n−2<2n−1 is applied after a factor n−2; no new result claimed from such presentation details. The follow-up is an exact matching prior proof body, not just its abstract. Publisher version not independently fetched. No formalization or credit.

## 349713 — sustained exact-source route, unresolved

Primary source and lawful institutional published 2021 Res. Number Theory 7:67 PDF both read at §4 Theorem 4.1, its recurrence proof, Theorem 4.5/proof, and Conjecture 4.6. P_a(x) counts unordered partitions into parts {1,2,a}, equivalently nonnegative triples u+2v+az=x; positive x,y and all 3≤a<b are required. No substitution of P_k counting all parts ≤k.

The exact direct-count formula is P_a(x)=Σ_{z=0}^{⌊x/a⌋}(⌊(x−az)/2⌋+1). On x=2an+i, 0≤i<2a, the source's quasipolynomials are a n²+B_a(i)n+C_a(i), where C_a(i)=P_a(i), and
* even a: B_a(i)=a/2+2+2⌊i/2⌋;
* odd a: B_a(i)=(a+3)/2+i.

For i=j=0, C_a=C_b=1. Put A=B_a(0), B=B_b(0). Completing squares transforms equality into

b(2an+A)² − a(2bm+B)² = bA²−aB².

Multiplying by b gives U²−ab V²=b²A²−abB², with U=b(2an+A), V=2bm+B. The integer seed (bA,B) is available. If ab is nonsquare, positive Pell units can act by (U,V)↦(rU+ab sV,sU+rV). A power congruent to identity modulo 2ab preserves the seed congruences and hence integral n,m. The positive seed and expanding positive unit imply unbounded positive n,m. This is a concrete proof mechanism; it needs a rigorous unit-existence/modular-power argument and a formal unboundedness proof, not numerical enumeration. This pass has not made a complete ordinary/formal endpoint, and does not claim this partial class as a new discovery.

When ab is square, the Pell mechanism degenerates. Write a=g u²,b=g v² with gcd(u,v)=1 (g=gcd(a,b)). For any residues with equal completed constants C_a−B_a²/(4a)=C_b−B_b²/(4b), the positive line is

2av n−2bu m = u B_b−v B_a.

It has integral solutions iff gcd(2av,2bu) divides its right side, after which the positive direction gives infinitely many n,m. The first diagnostic searched equal constants, then a second checked this necessary congruence too. Both tested 3≤a≤100, a<b≤200, square ab, using exact Fractions. Every tested pair has compatible lines. Five values of n were checked against direct counting for each displayed residue polynomial; that sanity check is not a proof of the quasipolynomial. Scripts and untruncated outputs retained. No exponential search or solver.

A useful subcase derivation: if a,b are both odd with ab square, then a≡b mod4. Taking i=(a−3)/2 and j=(b−3)/2 gives B_a=a, B_b=b and the same completed constant +1/4 for a≡3 mod4 or −1/4 for a≡1 mod4. The line u(2n+1)=v(2m+1) is solvable because u,v are odd. This suggests a full parity classification, but the mixed even/odd and differing 2-adic cases remain without a uniform residue construction in this pass. No bounded result is promoted to a theorem.

Precise remaining mathematics: prove the source quasipolynomial from the triple-count bijection/recurrence; close nonsquare-product Pell/congruence/unboundedness; prove compatible residue existence uniformly for square-product pairs in every parity case (or find an actual obstruction); complete all source semantics in Lean; investigate general conic/partition prior art more deeply before significance qualification. No Lean source was created to mask these gaps. Source Theorem4.5 is a partial prior result and receives no credit. Its displayed parametrization has apparent missing t terms in denominators; use the verified completed-square identity rather than trusting that transcription.

## 349425 — public counterexample body read; exclude

New primary review: source arXiv:2101.06180 definitions, Theorem4.6/proof, Corollary4.7, Theorem4.11/proof, Theorem4.12, Theorem5.3/proof and Conjecture5.4. New public proof-body read: ProbXiv page with timestamp 17 August 2026. It uses t disjoint 5-vertex wheels at k=2t, t≥3. Minimum F₂ rank is 2t and complementation number 2t+1; deleting a vertex changes a wheel to a 4-cycle or diamond with complementation number equal to rank2, so the whole deletion has number2t. Order5t exceeds4t+2. The source component theorem provides the exact full-scope bridge. This is prior public mathematical content regardless of its AI attribution or lack of human referee. No novelty clearance or formalization investment. The full forbidden-list proof and rank-factorization auxiliary literature were not independently audited.

## Scope and access discipline

All other records remain cached-literal/source-definition holds, except the inherited 1-2-3 family lead, which was found in expanded-corpus-r38 under 345998. No hard problem is asserted open today merely because the cached record says open. No source gaps are treated as clearance. No denied MathDB/Palomar route retried, and no browser tab, git, upload, external message, shared edit or child agent used.
