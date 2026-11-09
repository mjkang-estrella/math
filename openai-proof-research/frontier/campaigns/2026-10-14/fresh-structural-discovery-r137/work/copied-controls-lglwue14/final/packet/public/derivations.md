# r137: nondiscarding paired splitting and exact base repair

2026-10-20. Codex / GPT-6 Astra / high / default service tier.
**PREFREEZE/no nominee.** These are author research derivations, not independently reviewed results. No viable full theorem was frozen. The supporting statements below are not substitute nominees. Source proof operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true.

## 1. Unchanged full question and credited inputs

For every finite connected loopless undirected multigraph G with labelled edges, and every real x in its spanning-tree polytope, does an absolute A permit a convex decomposition of x into trees T with

    |T ∩ δ(S)| ≤ A x(δ(S))  for every nontrivial S?

The one-vertex graph is trivial. We work with at least two vertices. The universal statement is unresolved here. No rational-only or restricted replacement is proposed.

The authenticated r136 packet remains author support. We retain, without presenting them as discoveries: the exact separating-cost equivalence; source K-cost/cut rounding and its K-inflated marginals; the failure of signed-cost shifting to remove K; both halves of source matrix splitting; fair-half marginals on the extracted union; exact swap-rounding marginals and product moments; aligned-laminar exact-cost rounding and its marginal consequence; the changed point in general alignment; source logdet normalization; the difference between containing a packing and partitioning all edges; and the summable-product implication for an exact bisection. The K4, triangle, cactus, full-support-star and one-vertex-gluing diagnostics are also retained, without reusing them as nominees.

The new work in this round concerns (i) making the vector split respect prescribed pairs and hence original tight-rank equations, (ii) quantifying exact complementary-base repair, and (iii) testing that repair on an all-order family already close on every cut. No part of this work settles the full question.

## 2. An actual nondiscarding paired matrix split

Here is a complete supporting operation, obtained from the stipulated random-vector theorem, not an assumption of the desired base-compatible bisection.

Let E be a finite even set partitioned into pairs, let w_e be real vectors in R^d, and suppose

    Σ = Σ_{e∈E} w_e w_eᵀ ≤ 2I,       ||w_e||² ≤ ε,       ε>0.

There exists A⊆E taking exactly one member of every pair such that, with

    τ = 2√(2ε)+2ε,

both

    -τI ≤ Σ_{e∈A} w_e w_eᵀ - Σ/2 ≤ τI                       (2.1)

and the corresponding inequality for E\A hold. No index is discarded. Zero vectors and coincident vectors are allowed. A fair choice between this A and its complement gives every labelled index probability exactly 1/2. It is this last two-point law, rather than conditioning an initially independent law on success, that supplies the marginal statement.

**Derivation.** For each pair {a,b}, independently use the four equally likely vectors

    (w_a,w_b), (w_a,-w_b), (w_b,w_a), (w_b,-w_a) ∈ R^{2d}.

Each outcome has squared norm ||w_a||²+||w_b||²≤2ε. The expectation of its outer product is

    diag((w_aw_aᵀ+w_bw_bᵀ)/2, (w_aw_aᵀ+w_bw_bᵀ)/2).

The cross blocks cancel because of the auxiliary sign. Independence is across pairs; no independence of the two selected edge indicators within a pair is asserted. The total expected covariance is M=diag(Σ/2,Σ/2)≤I. Diagonalize I-M. Split each positive eigenvalue λ into ceil(λ/(2ε)) identical deterministic rank-one columns, each with squared norm at most 2ε. These finitely many deterministic vectors are independent of the pair variables, their sum of outer products is exactly I-M, and the enlarged expectation is exactly I.

Apply source existence `mss.tex`, thm:mss (the MSS random-vector theorem with expected squared norm bound 2ε). Some outcome has total outer-product sum at most (1+√(2ε))² I. Subtract the deterministic padding. Its two diagonal principal blocks give

    S_A ≤ Σ/2+τI,             S_{E\A} ≤ Σ/2+τI.

Since S_A+S_{E\A}=Σ, each upper inequality supplies the other lower inequality. Cross blocks of the selected random vectors need not vanish; they are retained until taking principal blocks. This proves (2.1). If d=0 or E is empty the claim is immediate. If all vectors are zero the claim also holds with zero error, without padding.

This operation enforces pairs exactly without adding one coordinate for each edge. It is a standard type of MSS lifting argument; no literature novelty or substantial-contribution assertion is made. The source's finite-bit signing algorithm is not claimed to implement this constrained random-support construction. Only existence is used.

## 3. Exact preservation of every original tight-rank equation

Let H have edge set E partitioned into q=2k spanning trees, n≥2. Write r(F) for its graphic rank, so r(F)=n-components(V,F). Then |F|≤q r(F), and |E|=q(n-1). A set F is tight when equality holds.

Tight sets are closed under union and intersection: modularity of cardinality, submodularity of r, and the inequalities |F|≤q r(F) force equality throughout the usual uncrossing chain. Choose a maximal strictly increasing chain of tight sets

    ∅=F_0 ⊂ F_1 ⊂ ... ⊂ F_t=E,

and let D_i=F_i\F_{i-1}. Every tight S is a union of the D_i. Indeed, if S partially cuts D_i, then F_{i-1}∪(S∩F_i) is a tight set strictly between the consecutive chain members, a contradiction. Also

    |D_i| = q [r(F_i)-r(F_{i-1})]

is even. Pair edges arbitrarily within each D_i and apply §2. Every resulting half satisfies, exactly,

    |A∩F| = k r(F)  for every original tight F,               (3.1)
    |A| = k(n-1).

The complement satisfies the same equations. This is the original minimal-face information, not a dynamically changing face after arbitrary rounding.

The tight-chain fact is classical. A late authenticated read found this very chain-span proof in the pinned common-integer-polymatroid paper, `polyhedra.tex`, lem:polyhedral-controls. It is credited there, not claimed as a new rank-face theorem. The additional construction here is its explicit compatibility with paired vector splitting.

**Stacked cut/rank implementation and its precise conditional input.** Suppose in addition that a matrix X on 1-perp is positive definite and satisfies

    X ≥ L_H,       1_SᵀX1_S ≤ C_X |δ_H(S)| for all cuts,
    b_eᵀX^{-1}b_e ≤ δ for EVERY e∈E.

The every-edge hypothesis is not supplied here by the source extraction theorem. Use source lem:auxiliary-representation on the whole union E, with any ρ>0, to obtain z_e with Σz_ez_eᵀ=I, ||z_e||²≤(1+ρ)/q and exact rank preservation. Set w_e=(X^{-1/2}b_e,z_e). Then Σw_ew_eᵀ≤2I by block Cauchy–Schwarz, and ε=δ+(1+ρ)/q is valid. Sections 2–3 give one nondiscarding split preserving (3.1), with

    || Σ_{e∈A}z_ez_eᵀ - I/2 || ≤ τ,
    -τX ≤ L_A-L_H/2 ≤ τX,
    ||δ_A(S)|-|δ_H(S)|/2| ≤ C_X τ |δ_H(S)|.                 (3.2)

For τ<1/2, the source's projected-trace lemma gives a packing of at least

    floor((1/2-τ)q/(1+ρ))

trees inside each side. This is the strongest currently justified conclusion of the integrated construction. It is not an exact k-tree partition of those sides.

All statements are about labelled edges; parallel labels are paired separately. The rank frame uses strictly positive weights and preserves parallel dependencies. For an original x with zero coordinates, a dyadic expansion simply creates no copies of those coordinates. The existing r136 compactness argument would cover arbitrary real x after a uniform exact base-compatible operation were proved; no such operation is established here, so no real-x conclusion is inferred.

## 4. Exact complementary-base repair and its dual

Let M be the graphic matroid of H and let N be the union of k copies of M. A set is independent in N exactly when it partitions into k forests. The source algorithm's matroid-union interface is credited. Since H partitions into 2k trees, r_N(E)=b=k(n-1), and |E|=2b.

A subset R partitions into k trees, with E\R also partitioning into k trees, exactly when R is a common base of N and its dual N*. To check this, bases of N have size b and decompose into k forests; each forest has size at most n-1, so every one is a tree. Bases of N* are complements of bases of N. Conversely, any exact split clearly gives a common base. In particular such splits exist by grouping the given trees, without a cut estimate.

Equivalently, an integral indicator y=1_R has total b and satisfies

    |F|-k r(F) ≤ y(F) ≤ k r(F)  (F⊆E),        0≤y_e≤1.    (4.1)

The upper system is the k-forest-union criterion; the lower system is the same criterion for the complement. The corresponding real polytope is the common-base polytope B(N)∩B(N*). The standard union-rank formula, r_N(F)=min_{J⊆F}(|F\J|+k r(J)), verifies the equivalence with the base-polytope rank inequalities under y≤1. Its integrality is already paid by matroid intersection, also included in the pinned polyhedral-controls lemma. Thus it is possible to repair to an exact split by linear optimization. What is missing is a uniform bound on the cut damage of that repair.

A useful precise comparison uses the actual weight-splitting proof of András Frank, *A quick proof for the matroid intersection weight-splitting theorem*, EGRES QP-2008-03, Theorem 4. Its complete three-page body was read. For an integer nonnegative edge weight w, let A be any initial subset and put

    c_e = -w_e (e∈A),       c_e = w_e (e∉A).

For every R,

    w(R△A) = w(A)+c(R).

Negating Frank's maximum-weight identity gives the exact formula

    min_{R common base} w(R△A)
      = w(A)+ max_{c_1+c_2=c, integral}
          [min_{B base of N} c_1(B)
           + c_2(E)-max_{B base of N} c_2(B)].               (4.2)

Both inner optimizations are ordinary weighted matroid-base optimizations. Complementation gives the second term. A common base exists, so the min-max applies. Rational weights follow by clearing denominators. For arbitrary real w, minima over the finite common-base family are continuous; rational approximations therefore evaluate the limiting optimum, without an assertion here about attaining a real split by the integral proof.

For completeness, Frank's identity also proves the polytope intersection assertion needed above: for integer c, every y∈B(N)∩B(N*) has c·y at most every split sum of the two maximum-base values, hence at most the maximum common-base value. If y were outside the convex hull of common bases, strict separation could be approximated by a rational functional and scaled to an integer one, a contradiction. This credits the full weighted operation, not only unweighted feasibility.

Taking w to be a cut indicator minimizes damage on that cut. Taking w to be a nonnegative sum of cut indicators minimizes the corresponding weighted damage. Neither supplies a single repair good on every cut. Even a distribution with small expected damage on each cut would be weaker than a support bound. The original midpoint y=1_E/2 is already feasible in (4.1); fractional feasibility alone is not the unresolved step.

## 5. A long exact repair with small cut damage, at every packing scale

This all-parameter example arose from the new repair search. It is not the r136 K4 example and not a counterexample to the full question. It distinguishes the number of edits from their cut cost while retaining near-half cut balance and near-full packings.

Fix any even integer N≥2 and any integer k≥1. On vertices 0,...,N, put k labelled copies of each edge type

    a_i={0,i},       b_i={i-1,i}       (1≤i≤N).

At i=1 the two types are parallel but their labels remain distinct. The graph H has 2kN edges and is the union of k spoke-star trees and k path trees. Thus q=2k, with no leftover edges.

Set h=floor((k-1)/2), t=k-1-h. Distinguish one last copy of every a_i,b_i. Define A to contain h ordinary copies of every a_i, t ordinary copies of every b_i, and both distinguished copies at each even i. Its complement contains t ordinary a_i copies, h ordinary b_i copies, and both distinguished copies at each odd i. The ordinary copies can be assigned disjoint labels to realize these multiplicities.

**Packings and cardinalities.** A is exactly k trees: h star trees, t path trees, and the distinguished tree joining each odd vertex 2j-1 to 2j and then to 0. The complement contains k-1 trees from its ordinary copies. Its last vertex N has degree k-1, so it contains no k edge-disjoint spanning trees. Both sides have kN edges. When k=1 the complement's distinguished component on {0,1} has a parallel cycle, and N is isolated; its graphic rank is N-1. Thus at k=1 the two graphic rank defects are zero and one.

**Near-half all-cut estimate before repair.** In A, each a_i-type has multiplicity h or h+1, and each b_i-type t or t+1. Each differs from k/2 by at most 1 (at most 1/2 if k is odd). For every cut, summing these differences over the edge types it crosses gives

    ||δ_A(S)|-|δ_H(S)|/2| ≤ |δ_H(S)|/k,                     (5.1)

with the improved coefficient 1/(2k) for odd k. Counting the two parallel types separately at i=1 is valid. The complement has the same discrepancy. In particular this family already has decaying relative discrepancy as q grows.

**Every exact repair changes at least N labels.** Put U_i={0,...,i}. Its internal edge set has exactly 2ki edges, hence is tight for the q-tree union. Any exact split R must have exactly ki edges inside U_i: each of its k trees has at most i such edges, and the complementary k trees have the same bound, whose sum is attained. Subtracting consecutive equalities shows that R takes exactly k labels from the incoming group {a_i copies,b_i copies} for every i. A takes k+1 in an even group and k-1 in an odd group. Every group therefore requires at least one changed label. The groups are disjoint, giving |R△A|≥N, or at least N/2 cardinality-preserving swaps. N is unbounded even at fixed k, although only one tree is missing from the complementary packing.

**An exact repair attaining N edits and a small all-cut cost.** Toggle the distinguished b_i at every i: remove it from A when i is even, add it when i is odd. The resulting R and its complement each take exactly k edges in every incoming group. Arbitrarily assign each group's k edges to k tree slots. In every slot, each vertex i>0 has exactly one edge to a smaller vertex. Following these parent edges strictly decreases the vertex label and ends at 0, so each slot is a spanning tree. This proves both exact partitions without an assumed bisection theorem.

The set of changed labels is one copy of the path b_1,...,b_N. Since H contains k copies of that path,

    |(R△A)∩δ_H(S)| ≤ |δ_H(S)|/k  for every cut S.           (5.2)

Together with (5.1), R has relative half-discrepancy at most 2/k. Fair choice of R or E\R preserves every label with probability 1/2. Thus this particular long repair is compatible with every desired invariant, including small all-cut damage. It cannot be used as an impossibility argument against cut-cheap repairs. Its role is to reject a bound on the *total* number of swaps depending only on q and the number of lost bases, and to identify cut load as the useful quantity. The raw A violates original tight equations; it is therefore not an example of the residual nontight defect after §3, and supplies no lower bound for repairing the outcomes of that construction.

## 6. Pairing test and the parallel-label correction

We also tested the assertion that *every* transversal of some fixed pairing is base-compatible. The attempted all-scale obstruction failed, as follows. Let H_k contain k labelled copies of each of the six edges of K4. It is a union of q=2k trees: each K4 copy partitions into two complementary spanning paths.

Consider any perfect pairing of its 6k labels. For each of the four triangles C, let p_C be the number of pairs entirely inside its 3k labels. A pair of parallel labels lies in exactly two triangles; a pair of nonparallel adjacent labels lies in exactly one; a pair of opposite-edge labels lies in none. Consequently

    Σ_C p_C ≤ 6k,

not 3k. This corrects the provisional checkpoint calculation, which mistakenly treated parallel pairs as belonging to at most one triangle. The earlier proposed universal pairing obstruction therefore does NOT follow at k>1. Indeed for even k, pair parallel copies within every edge type. Every transversal then has k/2 copies of every K4 edge and is an exact k-tree union, with an exact complementary union. This is a successful nondiscarding special-case pairing, not a counterexample.

For k=1, no parallel labels exist. Then Σ_C p_C≤3, so some triangle contains no internal pair. Taking all its edges produces a transversal that is a triangle, not a tree. This proves the limited k=1 assertion only. It adds no unbounded negative family and is not nominated.

This correction was made before any freeze or seal. It illustrates why finite-label multiplicities must be retained in the combinatorics. The actual full-scope issue remains selecting a good outcome in general, not making every outcome of every pairing good. The paired lemma does not claim the latter.

## 7. Strongest integrated attempt, late evidence, and exact remainder

The new paired operation pays exact cardinality and all original tight-rank equalities on the same subset that satisfies the two-sided stacked matrix bound. It does not repair the two remaining losses:

1. Source extraction guarantees small-resistance edges on a near-full selected packing. It does not, at the interface used here, furnish the every-original-edge hypothesis of §3. Applying our pairing to that extracted union still leaves its discarded labels unpaid.
2. Even with every-edge small resistance, (3.1)–(3.2) give contained near-full packings, not exact forest-union upper bounds on every nontight F. Formula (4.2) gives exact linear-cost repair, but no bound uniform over all cuts on the same repair has been established.

The complete omitted algorithmic tree geometry and signing appendix were read, along with the source's full random-vector proof. Geometry gives a single response on a nested partition chain with a bounded exceptional fraction. The signing descent uses endpoint/coordinate moves and a drift; imposing rank equalities on its covariance alone would not make its drift tangent or its endpoint moves feasible. The paired construction circumvents that issue for fixed pair equations but does not claim a constrained version of the whole descent.

A late actual-history hit led to the pinned common-integer-polymatroid paper. Its full polyhedral controls, near-tight partitions/refinement bodies, and root-direction difference-count proof were read. They already provide exact intersection integrality, the tight-chain span, dimension-dependent distance control, and nearby-slice/count operations. Their distance estimate is not a dimension-free all-cut repair bound. Their two rank systems may be refined separately; replacing the fixed midpoint by a feasible center or contracting slices does not by itself preserve the original cut comparison. No absence claim is made about unread transitive counting machinery.

The previously unread Klein–Olver–Yeoh polygon-cover interior was also read. It pays a laminar cover of near-minimum cuts by at most eight cuts, including inside atoms. That cover is not an equality for signed cut discrepancy: covering edges does not preserve cancellation. Nor do arbitrary near-tight rank inequalities of (4.1) automatically become near-minimum bipartitions of the original graph. An additional compatible reduction would be needed to use that operation here. It is not dismissed as incompatible in principle.

The r107 full directed target and its full-stack obstruction were read on the pairing/head-constraint overlap. That target is unchanged and is not being resumed. r54's actual all-metric scope and derivation were read and left unchanged. No family-180 route was restarted.

No universal exact split, cost-factor-one all-cut tree theorem, or unbounded separating-cost family has been derived. The exact unpaid obligation remains a nondiscarding choice satisfying both full base systems and a summably small all-cut discrepancy, or another full-scope construction/counterexample for the original real-x question. The supporting paired split and explicit repair family are concrete progress in this derivation, not acceptance evidence, exhaustion, impossibility, correctness, contribution, or priority verdicts.
