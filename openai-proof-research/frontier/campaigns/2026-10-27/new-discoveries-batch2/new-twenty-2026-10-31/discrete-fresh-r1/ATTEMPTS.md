# Exact statements and attempts

All three IDs were previously held after cached-record-only review in `../lane-3/results.json`, not cleared for novelty. That previous depth is not counted again. Current work reads actual primary bodies. No acceptance or full formalization is claimed.

## 321549 — finite simple graphs, arbitrary order

Stolee, arXiv:1105.1764, introduction and Conjecture 1.2: write Φ(G) for the number of perfect matchings of a finite **simple** graph and c(G)=|E(G)|−|V(G)|²/4. For positive integer p, c_p is the largest excess over **all** graphs with Φ(G)=p. The eventual formula f(n,p)=n²/4+c_p holds for sufficiently large even n; the introduction's extension lemma makes every graph's excess a lower bound for c_p. “p-extremal” here means attaining this global constant, rather than merely maximizing edges at one fixed order. The earlier HSWY manuscript uses fixed-order terminology, but its Conjecture 8.2 concerns the same c_p.

For p≥1 there are unique t≥1 and 1≤k≤2t with k(2t−1)!!≤p<(k+1)(2t−1)!!. Set C(p)=t²−t+k−1. The exact graphwise endpoint equivalent to the upper bound is

    ∀ G finite simple, ∀ p≥1, Φ(G)=p ⇒ |E(G)|−|V(G)|²/4 ≤ C(p).

Equivalently clear denominators by multiplying by four. A graph refutation needs no extremality proof: an actual graph above C(p) suffices, provided its exact perfect-matching count and excess are established. No multigraph, odd-order, zero-matching, or matching-covered-only replacement is admissible.

The primary original manuscript, Section 8, Lemma 8.1, gives the sharp boundary construction K_(2t+2) with a star of 2t+1−k edges removed. Section 9 and Stolee's later full body already compute small p; reproducing those is excluded. Current targeted searches located no later full resolution. This is a bounded negative search, not clearance.

### Structural route beyond the finite sweep

For G=K_(2m)\F with d=|F|, each forbidden edge belongs to (2m−3)!! perfect matchings. The union bound proves

    Φ(G) ≥ (2m−1−d)(2m−3)!!.

For 1≤d≤2m−2 this implies C(Φ(G))≥m²−m−d=c(G), since the step function C is nondecreasing and at the displayed boundary equals that excess. The case d=0 is the complete-graph boundary. This gives an ordinary full proof for that restricted near-complete class, but is routine from the source's star-removal mechanism and receives no credit. When d≥2m−1 the lower bound is nonpositive. Positive excess allows as many as m²−m missing edges, so this leaves most of the possible extremal region untreated. Overlaps of forbidden-edge matching events are precisely the missing issue; claiming star deletion minimizes matching count for arbitrary d would assume the essential extremal assertion.

A second possible induction uses Φ(G)=Σ_(w~v) Φ(G−v−w). For a summand, c(G−v−w)=c(G)+n−deg(v)−deg(w). Thus no uniform lower bound at the original excess follows just from this recurrence; the missing degree/overlap argument is structural. Cathedral decomposition also requires controlling excess under tower composition and matching-count products. Neither a full induction invariant nor a complete structural comparison was obtained.

`diagnostics.py` checks the exact least-remaining-vertex recurrence, with at most 2^n memo entries per graph. It enumerates all labelled deletions of ≤6 edges from K6 (9,949 graphs) and ≤4 from K8 (24,158); separately samples 5,000 dense graphs at each order 8,10,12,14, fixed seed 321549. Maximum observed c(G)−C(Φ(G)) is zero in every group. These are diagnostics, not a universal proof, nor searches over all p-extremal graphs. No graph counterexample was found.

## 321583 — concentration at zero and a zero-credit endpoint refutation

Arratia–DeSalvo, arXiv:1105.2834v2, equation (6), Definition 3, Theorem 5, Conjecture 3 (p.13). A partition λ=(λ₁≥⋯≥λ_k>0) has positive integer parts, gcd one, exactly k parts. With independent uniform ε_i∈{−1,1},

    r_λ = Pr(Σ λ_i ε_i=0) = 2^(−k) #{ε:Σ λ_i ε_i=0}.

This is **not** sup_x Pr(Σ λ_i ε_i=x). Sorting removes permutation equivalence and gcd one removes scaling; the conjecture is over all such partitions, not just “novel” partitions. It asserts a unique runner-up 2²1^(k−2) for even k≥4, and a unique runner-up 2³1^(k−3) for odd k≥7; the largest odd value at 2·1^(k−1) is already Theorem 5. Proving that leader again would be excluded.

The literal uniqueness assertion fails at k=4. For any distinct coprime positive integers a,b, λ=(a,a,b,b), sorted, has four zero sign vectors: each equal pair must carry opposite signs. Indeed a(ε₁+ε₂)=−b(ε₃+ε₄); both bracketed expressions belong to {−2,0,2}, and nonzero equality would force a=b. Thus r_λ=4/16=1/4. In particular (3,3,1,1) is distinct from (2,2,1,1), primitive, and ties its probability. Theorem 5 bounds every unequal four-part partition by four zero vectors; (1,1,1,1) has six. Consequently this is the actual second-largest value and its uniqueness fails, rather than merely an arbitrary equality of low probabilities.

This is an elementary endpoint correction, explicitly excluded by the user's substantive credit standard. It is not a new mathematically significant candidate, and was not formalized. The family has infinitely many coefficient choices but all are the same k=4 endpoint defect; disguising it as an infinite family does not change that assessment. The intended even k≥6 and odd k≥7 questions remain unproved here.

Beyond that failure, the exact subset generating function ∏(1+x^λ_i) gives zero-count coefficient at half the total weight (zero if odd). Exhaustive **bounded** primitive partition checks with every part ≤8, k=4 and k=6,…,12 tested respectively 289,1624,3303,6260,11209,19150,31447,49919 partitions. No other runner-up ties or nonleader probabilities above the proposed runner-up were found for k≥6. Coefficient arrays have length ≤4k+1, not size exponential in λ_i. The bounded cap cannot imply arbitrary-coefficient uniqueness. The four-antichain proof of Theorem 5 supplies only the first-place upper bound; improving it to the runner-up gap and classifying equality is the unresolved proof step. No all-k stability/equality theorem was obtained.

Publisher page DOI 10.1007/s00026-013-0176-7 is accessible but supplies the abstract, not the conjecture body. Its abstract still mentions the first-place/runners-up conjecture; this is not evidence about its present resolution. The v2 primary body, dated May 22, 2012, retains k≥4. No known-literal-uniqueness novelty claim is made.

## 321278 — parity determinant and the unproved knot bridges

Kaestner–Kauffman, arXiv:1103.2825, Section 2.1; published primary body downloaded from IMPAN, Conjecture 2.5 retains the exact span bound. Gaussian crossing parity is determined by the number of Gauss-code encounters between a crossing's two appearances, modulo two. The source's crossing switches are

    B = [[0,s],[t,1−st]],     P₃ = [[0,z],[z⁻¹,0]]

over Z[s±1,t±1,z±1]. Assign arc generators and impose the crossing relations, including inverse relations at negative crossings. The determinant of the resulting 2N×2N presentation matrix supplies the polynomial, with the source's writhe/unit normalization. Section 1 Example 1.1 illustrates the arc-order construction; Lemma 2.1 asserts invariance of the parity biquandle. Section 1 explicitly defers well-definedness of the determinant to its cited biquandle literature; module invariance alone is not a complete polynomial normalization proof.

For each virtual-knot class K for which the polynomial is nonzero, let e_max and e_min be the largest/smallest supported z-exponents. Let n=min_D realCrossings(D), over **every** diagram representing K. Conjecture 2.5 is e_max−e_min≤n. A nonzero qualifier is implicit in existence of the two extrema; taking the unknot's zero polynomial and arbitrary extrema is an excluded domain repair. One fixed diagram would suffice for a refutation if its invariant span exceeds that diagram's crossing count, since n is no larger; a universal proof must work on a crossing-minimizing diagram with invariance established.

Theorem 2.3's determinant argument gives each exponent in [−o,o], with o the number of odd crossings of a diagram. Therefore its direct support consequence is span≤2o, not span≤N. This proves only diagrams with 2o≤N and does not settle the full problem (o may be close to N). Corollary 2.4 bounds max(|e_max|,|e_min|), a different quantity; doubling it is again too weak.

I also pursued elimination along the oriented Gauss circuit. Odd crossings transport labels by monomial z or z⁻¹; even overpasses transport by s or s⁻¹. Retaining even underpass generators reduces to a sparse matrix with an identity term, predecessor transport and one overpass coupling per row. The resulting determinant still requires a global support/equality argument tied to Gaussian parity. Rowwise support estimates can add contributions from both occurrences of odd crossings and do not give the desired N bound. No valid cancellation theorem was proved.

`parity_probe.py` is explicitly an exploratory specialized model at s=3,t=2, not a certified virtual-knot invariant implementation. It reproduces source Example 2.1's polynomial up to sign: (5/6)(1−z⁻²). Fixed-seed sampling of 200 signed over/under Gauss words at each N=6,7,8,9,10,12 found specialized spans at most 4,6,8,6,8,8. A specialization may cancel endpoint coefficients, so these are only lower bounds on the generic polynomial span and negative tests prove nothing universally. The first check had a transcription error reading the nested 1/(st) fraction; the source-example assertion caught it and it was corrected before the random run. No putative knot counterexample is claimed.

A Lean determinant-support helper would leave all of: Gauss-diagram realization, parity preservation, signed crossing relations, presentation determinant correspondence, unit/writhe normalization, Reidemeister invariance, and minimization over diagrams. No full bridge chain or full support theorem was obtained, so no helper-only formalization was pursued.
