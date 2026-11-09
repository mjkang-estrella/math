# Lower intermediate spectra: full question unresolved

Nicolas Angelini, *Attainable forms of intermediate dimensions of complementary sets*, arXiv:2610.35834v1, Further Work, Question 1, pp28–29. Actual latest PDF and current abstract were retrieved and frozen before extraction or body reading. Abstract history lists only v1, submitted 26 October 2026 at 17:52:03 UTC. DOI alias: 10.48550/arXiv.2610.35834. No journal version authenticated. Exact URLs, execution UTC, body lengths and SHA256 are in http.jsonl; originals and independently written working copies are sources/ and frozen/. Execution clock is 30 October UTC, later than the initial environment calendar.

For EVERY positive non-increasing sequence a=(a_i) with sum 1, put x_m=Σ_{i≥m}a_i and s_n=2^(-n)x_(2^n). Assume 2<inf_n s_n/s_(n+1)≤sup_n s_n/s_(n+1)<∞. Let C_a be ALL closed subsets E of [0,1] whose complementary open intervals have exactly these lengths, including multiplicities. Let B be the common LOWER box dimension of these sets. The question is whether

{θ↦lower_dim_θ E : E∈C_a} = {h∈H(0,1):h(1)=B}.

Here H(0,1) consists of non-decreasing h:[0,1]→[0,1], continuous on (0,1], with upper right Dini derivative D⁺h(θ)≤h(θ)(1−h(θ))/θ for every 0<θ<1. No continuity at zero is imposed; h(0) is the Hausdorff dimension. For θ>0, lower_dim uses: for every ε>0 and δ₀>0 there exist 0<δ≤δ₀ and a cover with δ^(1/θ)≤diam U_i≤δ and Σ(diam U_i)^t≤ε. The quantifiers concern ONE set E realizing ALL θ, including 0 and 1, not a different E for each θ. The sequence need not have equal lower and upper box dimensions. The further question about pairs of lower/upper functions is not an additional target.

## Actual closest bodies and the complete available bridge

Read the source's Definitions 2.1, 4.1, Section 3 comparisons, Lemma 4.12 with proof, Lemma 4.14, the combined-scale and gap-allocation Steps 4–6 of Theorem 4.17, Corollary 4.18, and the full Further Work question. The mountain/connector construction was inspected for its scale-selection mechanism; no independent audit of every Dini-derivative detail is claimed.

Read actual Banaji–Rutar, *Attainable forms of intermediate dimensions*, Annales Fennici Mathematici 47 (2022), 939–960, DOI 10.54330/afm.120529, publisher PDF, Theorem B, the cover-conversion proof passages of Theorem 2.6, full Theorem 3.11 construction/proof and Corollary 3.13. Received 4 December 2021, revised 4 April 2022, accepted 27 April 2022, published 4 July 2022. The source bibliography incorrectly prints the last page as 506; the actual publisher body ends at 960. Their result constructs arbitrary compact perfect subsets of the line with prescribed lower and upper spectra, but does not prescribe the multiset of complementary intervals.

The full necessity adaptation is classical: for any E∈C_a, apply Banaji–Rutar Theorem B with λ=dim_L E and α=dim_A E. Then h∈H(λ,α). If λ<α, write u=h−λ and v=α−h. Its derivative bound is θ^(-1)uv/(u+v), which is increasing in each nonnegative argument. Since u≤h and v≤1−h, this is at most θ^(-1)h(1−h). If λ=α, h is constant and satisfies the same bound. Endpoint θ=1 is lower box dimension by the definition, which is B for every complementary set. Thus the left side is contained in the right side for every allowed a. This proves only necessity. The general Moran converse does not give the required a; it is not a complete exclusion bridge.

Closest gap-preserving predecessor: Angelini–Molter, *Intermediate dimensions of complementary sets*, latest actual arXiv:2412.12999v3 body, Sections 6 and Further Work, especially Theorem 6.1 and its separate lower-dimension covering argument pp15–16. Current abstract chronology: v1 17 December 2024 15:23:54 UTC; v2 30 October 2025 19:55:02 UTC; v3 16 November 2025 07:19:42 UTC. Bibliography/current metadata list published online 2026, DOI 10.1017/prm.2026.10162. Actual journal body was not separately obtained: preprint/journal identity remains qualified. The theorem constructs a gap subsequence with s_n(b) comparable to s_n(a)^r and joins its Cantor set to the remaining countable tail. Its lower proof explicitly synchronizes both covers at a subsequence of scales. It supplies every value at each fixed θ; that existential quantifier does not provide one set for an arbitrary function of θ.

## Sustained route: exact gluing and a universal obstruction to the existing construction

For a bounded F define C_t(F,δ,θ) as the infimum of t-cost over admissible covers. For any bounded M,D,

max(C_t(M,δ,θ),C_t(D,δ,θ)) ≤ C_t(M∪D,δ,θ) ≤ C_t(M,δ,θ)+C_t(D,δ,θ).

The first inequalities follow by restricting a cover, and the second by combining covers and approximating infima. Therefore a common sequence δ_j→0 on which BOTH costs tend to zero suffices to cover the union. Conversely a vanishing union cost forces both costs to vanish at the same scales. Separate liminf-zero assertions cannot be combined. This is an exact equivalence about costs, not a numerical heuristic.

For D={Σ_{i≥k}a'_i:k≥1}∪{0}, where a' is a subsequence rearranged decreasingly, choose k≥1. Cover the first k points by intervals of diameter δ^(1/θ); the remaining tail lies in an interval of length at most x_(k+1)(a), and can be covered by at most x_(k+1)(a)/δ+1 intervals of diameter δ. Hence

C_t(D,δ,θ) ≤ k δ^(t/θ)+x_(k+1)(a)δ^(t−1)+δ^t.

Here a'_i≤a_i termwise follows directly from order statistics; no asymptotic substitution is needed. To complete the full question by gap allocation, it would suffice to construct, for EVERY a and h, a gap-subsequence Cantor set M with lower spectrum at least h, Hausdorff dimension h(0), and, for EVERY θ>0 and t>h(θ), common δ_j↓0,k_j with C_t(M,δ_j,θ)→0 and both displayed tail terms tending to zero. Adjoining all remaining gaps then gives E∈C_a, the upper bound by common covers and the lower bound by inclusion. This precise sufficient lemma is UNPROVED. Rational θ and rational t would suffice using monotonicity and continuity. Banaji–Rutar's inhomogeneous phase branches plausibly provide persistent lower bounds; allocation of actual gaps and the simultaneous tail estimates are the missing universal parts.

The source's existing homogeneous construction cannot by itself supply arbitrary lower spectra. Here is a full adaptation, not an inference from shortness. Fix the allowed sequence

a_(2^k+i)=(3/4)8^(−k), 0≤i<2^k, k≥0.

Its sum is (3/4)Σ4^(−k)=1, s_n=8^(−n), and the decreasing Cantor set has Hausdorff and both box dimensions B=1/3. The admissible profile h(θ)=θ/(1+2θ), including h(0)=0, has h(1)=1/3, derivative 1/(1+2θ)^2≤(1+θ)/(1+2θ)^2=h(1−h)/θ, and h≤1/3. It is therefore realized as an UPPER spectrum by source Corollary 4.18. Its Step 5 set M is homogeneous and, by Lemma 4.12, dim_H M=lower_dim_B M=h(0)=0. The sandwich dim_H≤lower_dim_θ≤lower_dim_B gives lower_dim_θ M=0 for every θ. The remainder D has upper spectrum φ_(B')(θ)=θB'/(1−(1−θ)B'), with B'≤B, by the actual source's countable-sequence formula. For each t>φ_B(θ), D has vanishing t-cost at ALL sufficiently small scales, while M has vanishing t-cost along some sequence. The gluing inequalities imply lower_dim_θ(M∪D)≤φ_B(θ). The general complementary-set lower bound gives the reverse inequality, so this construction has lower spectrum exactly φ_B(θ)=θ/(2+θ). For 0<θ<1,

h(θ)−φ_B(θ)=θ(1−θ)/((1+2θ)(2+θ))>0.

Thus even this uniform-scale sequence needs an inhomogeneous replacement for the known upper construction. This is a proof-route obstruction, NOT a counterexample to Question 1: a different E could realize h. No source statement is refuted and no fresh theorem is nominated.

## Screening and limitations

Qualified original index refreshed from r204's existing canonical index plus new immediate lane reports: 1,541 paths, nine changed/new snapshots. Separately refreshed 2,576 inherited original-path aliases without promoting copied histories or inferring provenance from byte equality. Actual r111–113 report paths remain in these layers. Direct ancestor and batch instructions, all requested root DECISION files and r202–204 summaries were read first. All changed/new reports were inspected; r205 is independently pursuing apolar algebras and is not reused.

Exact title, author, arXiv, DOI and statement aliases have no matches in the bounded qualified or inherited screens. This does not clear all history. Current arXiv title search returns the new source and its predecessor. The stale pinned public registry catalog/tree at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb has no exact relevant aliases, but current complete registry heads/bodies/history remain unauthenticated. No denied GitHub routes, ScienceDirect, Google challenges, parked history intervals or browser were reopened. No worldwide priority or current unresolvedness certification.

Cosine-correlation and convex-order leads hit r190/r195 and are excluded as duplicate reconnaissance; the unnecessary refreshed PDFs remain unread here. Lian–Xue's actual Mahler-consequences body was read and supplies public proofs/conditional implications, not a fresh unresolved target. Siburg's monotone-rank paper and Islas's V-sequence extension supplied already public result passages; they were reconnaissance only, with no full independent proof audit or shortness exclusion. The survey PDF is retained as unused reconnaissance, not relied on mathematically.

Exact runnable controls in checks.py verify only rational algebra and finite gap-allocation arithmetic. Universal statements above rest on the written arguments and cited actual bodies, not those checks. No full source proof/refutation, PROOF.md, Lean or manuscript. Zero nominations; root alone adjudicates counts 9 additional / 39 total, next 40.
