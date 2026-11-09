# Mathematical handback — no accepted credit

## 348760: twelve-vertex counterexample in ordinary mathematics (rank 1)

Target: arXiv2011.11187v1, Definition10(i)–(iv), Lemmas11–12 and Conjecture20. The latest retrieved version renumbers the matching definition to13 and omits Conjecture20. Its omission is not evidence of either resolution or novelty. The primary definitions of nu, lambda, mu were also read in2005.00671. In particular mu is NOT the saturation number suggested by the MathDB paraphrase: it is the maximum size of one member of a maximum-size pair of disjoint matchings. No claim about saturation number is being made.

Let the vertices be0,...,11 and let the edge labels0,...,11 be

0:01, 1:02, 2:23, 3:34, 4:45, 5:06, 6:67, 7:18, 8:89, 9:1-10, 10:10-11, 11:47.

These twelve distinct unordered pairs define a simple connected graph. The edges0,...,10 already form a spanning tree. A bipartition is {0,3,5,7,8,10} and {1,2,4,6,9,11}. (Check each edge against these sets; do not inherit the ten-vertex coloring.)

Set M={0,2,4,6,8,10}, H={2,4,5,8,9}, H'={1,3,6,7,10}. These are matchings and H,H' are edge-disjoint.

**Maximum matching.** M is perfect, of size6. It is the unique perfect matching: leaves5,9,11 force edges4,8,10; then vertex3 forces2; then vertex7 forces6 because its other neighbor4 is used; finally0 forces0. Every matching has at most6 edges. The complement F=E minus M is {1,3,5,7,9,11}; {0,1,4} is a vertex cover of F, hence every matching in F has at most3 edges.

**Lambda and mu.** If one matching has size6, it is M, and an edge-disjoint matching has at most3 edges by the cover of F. Otherwise both matchings have size at most5. Thus every disjoint pair has total size at most10. H,H' attain10, so lambda=10. A pair attaining10 cannot contain a matching of size6, so mu=5. Thus mu/nu=5/6<1.

**First nested overlap.** Let U=A union B for two edge-disjoint matchings with total size10. Every vertex has U-degree at most2. The vertices of E-degree3 are exactly0,1,4. The two omitted edges must cover these three vertices. The only edge joining two of them is edge0. Consequently E minus U={0,x}, with x in {3,4,11}. Conversely, each such deletion leaves disjoint paths of even length and admits a balanced two-coloring. Since M contains0 and4, M intersect U has size4 for x=4 and size5 for x=3 or11. Thus5 is the maximum overlap. Our H,H' omit0 and11 and attain5.

**Second nested overlap.** For x=11, the two path components of U are
5-4-3-2-0-6-7 and9-8-1-10-11, of lengths6 and4. On the first path the M-edges are labels4,2,6; two have one alternating parity and one has the other. On the second path the M-edges8,10 have opposite parities. Thus either color class has at most3 M-edges. For x=3, the first component is3-2-0-6-7-4-5, with the same parity distribution of M-edges2,6,4; the second component is unchanged. Therefore among all triples satisfying(i)–(iii), |M intersect A|<=3. Our H attains3. This proves all four nested optimality conditions without an appeal to unchecked computation.

**Violation.** The symmetric difference M triangle H is the path7-6-0-1-10-11, with edge labels6,5,0,9,10 alternating M,H,M,H,M. No other edge of M triangle H is incident to any of its vertices, so it is a maximal M-H alternating path. Vertex7 is an endpoint and has graph-degree2, adjacent to6 and4; it is not a leaf. It is also an endpoint of the even maximal H-H' path5-4-3-2-0-6-7. This refutes the exact leaf-end assertion using the intended primary-source parameters.

**Independent diagnostic.** Direct powerset enumeration (different from the recursive matching generation used to find the witness) finds256 matchings, twelve triples before overlap optimization and four triples after both overlap optimizations; see leaf-independent.json. Neither enumeration is a Lean proof. No minimality claim.

**Formal status and remaining lemmas.** MatchingCertificate.lean is a failed certificate-layer experiment, NOT an endpoint. It encodes edge-index matchings and attempts to prove completeness of a256-element catalog by reducing all4096 subsets in the kernel. Importing all Mathlib first failed because a cached private olean is missing. Restricting imports avoided that dependency error, but the kernel reduction terminated with bad_alloc under an8GiB address-space cap, Lean6GB internal cap,150CPU/170wall-second budget. No clean build, axiom audit or strict replay is claimed. The better next approach is the structural proof above: (1) formalize the cover-of-F matching bound; (2) prove every ten-edge two-matching union omits0 and one of3/4/11; (3) classify the two path colorings; (4) bridge the finite edge indexing to actual unordered graph edges, graph matching parameters and maximal alternating paths. These bridges remain unproved in Lean. Do not nominate the catalog theorem or any finite bound as the MathDB endpoint.

**Literature limits.** Original and updated source definitions and selected proofs read; predecessor main matching definitions and spanner discussion inspected. Live OpenAI and Omega registry heads checked before this route. A closest Omega filename RedundantLeafMatching was fetched; its definition slice concerns inclusion-maximal matchings under a redundant-leaf fold, not this maximum-disjoint-pair question. No full registry-body or citing-literature clearance. No author contact. Original journal version and reasons for deleting the conjecture in the successor remain unread. Root should obtain independent fidelity, ordinary-math, novelty/significance and full Lean review before any acceptance. Zero credit here.

## 348827: coefficient structure (rank 2; unresolved)

Primary2011.14502, Section1 Eq1.0.11, Conjecture1.0.4, Section2 generating product and fixed-part-count theorem/proof context. Exact coefficients are c_j(k)=[q^(jk)] product(i=1..j)(1+q^(2i-1)), for INTEGER1<=k<j. The nonintegral-index examples explicitly excluded by the authors are not counterexamples to this question. The generating polynomial is symmetric about exponent j²/2 by complementing the selected odd integers, so c_j(k)=c_j(j-k).

The carry-free exact-integer diagnostic checks3<=j<=180. Base2^(j+1) exceeds every coefficient (bounded by2^j), so multiplication by1+q^odd is reproduced exactly by integer shifts and addition without cross-digit carries. No more than two plateau peaks occurred; j=6 has [1,3,2,3,1] and is the only two-peak instance in this range. This is not a proof at larger j or a formal semantic certificate.

A second mechanism decomposes by part count h:
product(i=1..j)(1+y q^(2i-1)) = sum(h=0..j) y^h q^(h²) [j choose h]_(q²).
The target sums coefficients at jk over h; terms can contribute only when h≡jk mod2. The source's fixed-h unimodality is centered at k=h, not at the common center j/2. Hence summing those unimodal rows does not justify total unimodality. Pairing rows h and j-h recovers symmetry but does not control the number of modes. A uniform injection/variation bound for these parity-filtered Gaussian-binomial mixtures is missing. An asymptotic central-limit heuristic also cannot exclude tiny secondary peaks or cover all j. Parked, no theorem or counterexample.

## 349048: analytic branch comparison (rank 3; unresolved)

Primary2012.07409 Definitions1.1,1.2,1.5; Theorems1.3,1.4 and its proof; Section3 comparison setup; Conjecture1.6. Inner degree is the gcd of all positive Taylor exponents. The actual target counts components of the global maximum-modulus set near zero, not all local stationary curves. Theorem1.4 constructs one local branch in each leading sector, but only the subset J wins globally.

For f=exp(g), maximizing modulus is maximizing Re(g) on circles; this suggests perturbing g=z^k+bz^m. At leading roots of unity, the first symmetry-breaking term compares cos(m omega_j+arg b). If g0=gcd(k,m), the values form a regular(k/g0)-gon of cosine samples, whose maximum has one or two positions; each is repeated g0 times. This family gives at most2g0 winning branches at first order, consistent with the conjecture. Rotational composition f(z)=p(z^d) multiplies both branch count and inner degree and cannot refute the ratio. A higher coefficient can affect previously tied branches after their angles move; ignoring this movement is invalid. A full all-orders rigidity theorem, or an explicitly tuned persistent three-way tie without rotational degree, remains missing. No finite radial sample is evidence for a permanent analytic tie. Parked.

## Routine/known and scope exclusions

348420: source explicitly identifies G2(d) as path P_(d+1), but incorrectly asserts a2(2k+1)=2. A maximum independent set in P_(2k+2) is an increasing sequence of k+1 nonconsecutive positions. Subtracting0,1,...,k gives an arbitrary(k+1)-subset of{1,...,k+2}; hence there are k+2 such sets. Counts at odd degrees are unbounded, ruling out eventual2-periodicity. This is a routine known path enumeration with an explicit bridge, not campaign credit.

348620/348979: same literal connected-subgraph removal family; source2011.03929 Theorem1.2 explicitly attributes to Mader the stronger path-removal result at delta>=floor(3k/2)+m-1. The original Mader proof body was not retrieved; this is primary attribution plus theorem-text review, not independent proof verification. Both parked from discovery as already attributed, not self-proved.

348939:2012.02882 ConjectureB is followed immediately by attribution of a counterexample to Jaramillo–Villarreal, The v-number of edge ideals, JCTA177(2021)105310. Original counterexample proof body unread. No new exclusion theorem claimed; existing attribution blocks rediscovery investment.

349115:2207.14253 Section3, definitions of admissible Boolean chains and Theorem3.6, full proof through dimension count read. It explicitly proves Heuer–Striker Conjecture5.25 in arbitrary m,n, including face dimension. A second independent Black–Sanyal proof is attributed but unread. Published versions not separately audited.

349150:2012.11177 Conjecture1.3 has the same displayed strengthened inequality but the sentence says “3<=k<=n-2 edges”; its source Amaro et al. is not recovered. Complete-graph versus fixed sparse H comparisons would exploit missing scope. No paraphrase refutation nominated.
