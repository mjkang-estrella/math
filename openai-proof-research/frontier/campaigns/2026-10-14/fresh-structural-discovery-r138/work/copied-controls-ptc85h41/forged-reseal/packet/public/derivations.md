# r138 — joint repair duals and a residual nontight family

Codex / GPT-6 Astra / high / default service tier. 2026-10-20.
**PREFREEZE/no nominee.** No full theorem became proof-feasible and no scope was frozen. The arguments below are author research support, not independent correctness/contribution findings, a substitute target, or a counterexample to the full question.

## 1. Unchanged question and retained operations

Does an absolute A work for every finite connected loopless undirected labelled multigraph G and every real x in its spanning-tree polytope, so that x is a convex combination of spanning trees T obeying |T∩δ(S)|≤A x(δ(S)) for every nontrivial S? Equivalently, for every nonnegative cost c, the SAME A-thin family must contain a tree of cost at most c·x, with factor ONE. One vertex is trivial. No rational-only, generic, assumed-split, laminar, cactus, or bounded-size version replaces this question.

The authenticated r136/r137 support is retained: K-cost/cut rounding and its inflated marginals; the inability of the signed-cost shift to remove K; both-sided source splitting and fair-complement marginals on the extracted union; exact swap-rounding marginals and tails; cost-one aligned-laminar rounding with its changed x under general alignment; the distinction between a contained near-full packing and an exact partition; the already-paid summable exact-bisection implication and real-x limit. r137's four-outcome paired MSS lift, original-tight-chain atom construction, stacked rank/cut frames, and Frank repair dual remain compatible operations. They are not accepted findings.

All source statements AND operative proof operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. We inspect applicability, not upstream truth. The all-scale K4 pairing obstruction in r137 was false: parallel pairs belong to two triangles. That correction is retained throughout, including §6 below.

## 2. The joint all-cut repair game, with its exact quantifiers

Let H be an exact union of q=2k spanning trees on n≥2 vertices, E its labelled edge set, b=k(n−1), and a=1_A an arbitrary half of size b. Let N be the union of k copies of the graphic matroid. Write C for the common bases of N and N*, and P=conv{1_R:R∈C}. The paid union/intersection operations identify

    P = { y∈[0,1]^E : y(E)=b,
          |F|−k r(F) ≤ y(F) ≤ k r(F) for every F⊆E }.

Thus all ranks, both sides, cardinality, and the individual labelled coordinates are included. C is nonempty by grouping the original trees. P contains 1/2. For each nontrivial cut S, write h_S=|δ_H(S)|>0 and define

    d_S(y)= [Σ_{e∈δ(S)} (a_e+(1−2a_e)y_e)] / h_S.

Because a is binary and 0≤y≤1, the numerator is exactly Σ_{δ(S)}|y_e−a_e|. On a base indicator it is |(R△A)∩δ(S)|. Define

    v_mix = min_{y∈P} max_S d_S(y),
    v_pure = min_{R∈C} max_S d_S(1_R).

These quantities are different optimization problems. Finite-dimensional convex separation gives the exact identity

    v_mix = max_{λ_S≥0, Σλ_S=1} min_{R∈C} Σ_S λ_S d_S(1_R).       (2.1)

Here is a short proof paying the quantifiers. The compact convex set of load vectors {d(y):y∈P}, plus the nonnegative orthant, is closed and convex. For t<v_mix it excludes the constant vector t·1. A strict separating functional is nonnegative by the upward closure; normalize its coordinates to sum one. Its minimum on the load set exceeds t. The reverse inequality follows by taking any convex combination of coordinates below their maximum. Let t increase to v_mix, and use compactness of the multiplier simplex to attain the maximum. A point y∈P decomposes into common-base indicators, and affinity of each d_S identifies d_S(y) with the expected load in that distribution. This proves (2.1), including the simultaneous EXPECTATION on every cut. It does not replace the expectation with a support bound.

For a multiplier λ put

    w_e=Σ_{S:e∈δ(S)} λ_S/h_S,       Σ_e w_e=1,
    c_e=(1−2a_e)w_e.

Then the inner minimum in (2.1) is

    w(A)+min_{R∈C} c(R) = min_{R∈C} w(R△A).                       (2.2)

Frank's Theorem 4 evaluates this minimum by the paid weight-splitting dual. For rational w, clear denominators and negate his maximum identity:

    w(A)+max_{c1+c2=c} [min_{B∈Bases(N)}c1(B)
                       +c2(E)−max_{B∈Bases(N)}c2(B)].             (2.3)

The split is integral after scaling. Arbitrary real w are covered by continuity of the minimum of finitely many linear functions and rational approximation; we do not need an unproved real integral-split assertion. This is an actual joint dual, beyond choosing a different unconnected witness for each cut. Its output remains v_mix, not v_pure. Section 4 computes a strict gap inside the relevant graph/base setting.

## 3. Where the source metric really composes

Let c_S=1_S−(|S|/n)1 and set

    Z_λ=Σ_S (λ_S/h_S)c_S c_S^T.

It is centered and PSD. Its squared distances are d_λ(u,v)=Σ_S(λ_S/h_S)|1_S(u)−1_S(v)|, a nonnegative sum of cut pseudometrics, so they satisfy every triangle inequality. Thus Z_λ belongs to the source metric test cone N. Moreover

    b_e^T Z_λ b_e=w_e,
    tr(L_H Z_λ)=1,
    tr(L_{R△A} Z_λ)=w(R△A).                                     (3.1)

There is NO cone incompatibility at this point. In particular every source response Y∈K_H has tr(YZ_λ)≤3. These identities use actual labelled edges, so all parallel copies contribute separately.

What is still needed to compose the operations is an estimate on the exact repair selected in (2.2). The source partition-chain response controls a large fraction of crossing edges of a nested chain, and extraction controls a near-full contained packing. It does not specify an R∈C whose CHANGED edges obey L_{R△A}≼ηY, or even tr(L_{R△A}Z_λ)≤η for this λ. Such an estimate, if uniformly proved for every λ, would pay v_mix≤η; another operation would still be needed for v_pure.

The intermediate signed optimization c=(1−2a)w is not itself necessarily a metric cost. For example, on K4 use equal w on all six edge types (a sum of singleton cut metrics), and let A be the path 01,12,23. Adding the smallest common shift to make c nonnegative gives zero on that path and a positive value on 02, violating the 0–1–2 triangle inequality. Larger shifts or other representations are not forbidden; they must pay their objective after subtracting the fixed-cardinality shift. This example is only a warning against identifying c directly with Z_λ. Formula (3.1) already avoids that identification by keeping the unsigned changed-edge objective.

Every-edge normalization alone also fails to estimate that objective: b_e b_e^T≼δY for each changed label implies only L_{R△A}≼δ|R△A|Y. r137's fan family has unbounded necessary edit count but cheap cut load. No dimension-dependent edit bound is being converted into a uniform cut estimate here. Its raw split violated original tight equations; the next family instead exhibits the residual NONTIGHT defect.

## 4. A new all-scale family: all geometric hypotheses paid, one nontight rank unpaid

Fix an integer t≥1 and put k=3t+1, q=2k. On vertices 0,1,2,3 give each spoke 0i multiplicity s=2t+1, and each triangle edge ij among 1,2,3 multiplicity m=4t+1. Every copy has its own label. Let H_t be this graph. Define A by choosing t labels of each spoke type and 2t+1 labels of each triangle type. Choices of which labels are immaterial, but are fixed.

### 4.1 All ranks and tight faces

H_t has 3s+3m=18t+6=6k=q(4−1) edges. For a two-vertex set the internal count is at most m<q. For the triple {1,2,3} it is 3m=12t+3<2q=12t+4. For any other triple it is m+2s=8t+3<2q. These inequalities imply |F|≤q r(F) for every edge subset F: split F into its nontrivial connected vertex components U and bound each |F[U]| by |E_H(U)|≤q(|U|−1). If F is spanning and connected but proper, its size is strictly below |E|=3q. Therefore only ∅ and E are tight. Matroid union now partitions ALL labels into q forests, which are trees because the total size is 3q. No extraction is used.

A and E\A have 3k labels each. But

    |A[{1,2,3}]|=6t+3=2k+1,

so A violates the k-forest rank bound by one on an originally nontight set. Its complement has 2t labels per triangle type and t+1 per spoke. Checking pairs and triples as above shows it is exactly k spanning trees. A contains exactly k−1 edge-disjoint spanning trees: retain 2t per triangle and t per spoke, whose 9t=3(k−1) edges meet every (k−1)-forest bound. No larger packing is possible because deg_A(0)=3t=k−1.

Thus the same near-full-packing defect survives at arbitrarily large q while EVERY original tight equality and total cardinality are exact. There is a single original tight-chain atom, E. Pair each label of A with a distinct label of E\A: A is a legitimate transversal of an original-atom pairing. This is a statement about a permitted outcome, not that MSS must select it.

### 4.2 Every original edge is geometrically small

Take X=L_H on 1-perp. It has cut comparison constant one. Parallel copies alone give b_e^T X^{-1}b_e≤1/s, for EVERY label. More exactly, ordinary resistances are

    R_triangle=1/(7t+2),
    R_spoke=k/[(2t+1)(7t+2)].                                  (4.1)

We can also exhibit an exact positive-weight rank frame with uniform norms, avoiding a limiting normalization. Give each spoke label weight 1 and each triangle label weight s. Let L_w be the weighted Laplacian and z_e=√w_e L_w^{-1/2}b_e on 1-perp. Then Σ_e z_e z_e^T=I and every subset has its original graphic rank. The common invertible map and positive scalings preserve parallel dependencies.

To verify norms explicitly, write p=m s for total conductance of each triangle type and r=s for each spoke type. The weighted Laplacian has eigenvalue 3p+r=4sk on the two-dimensional subspace of leaf coordinates summing to zero, and eigenvalue 4r on the complementary centered direction. A triangle incidence vector has squared length 2 in the first subspace. A spoke incidence vector has squared projection lengths 2/3 and 4/3 on the first and second subspaces. Thus its resistance is

    1/(3r)+2/[3(3p+r)].

Multiplying by the label weights gives, for BOTH kinds of label,

    ||z_e||²=1/(2k)=1/q.                                      (4.2)

The same eigenspace calculation with p=m,r=s proves (4.1).

Let u_e=X^{-1/2}b_e and w_e=(u_e,z_e), choosing the same orientation for every label of a type. Then Σ=Σ_e w_e w_e^T≼2I, and

    ||w_e||²≤1/s+1/q=:ε_t →0.

This includes the cross blocks; we do not drop them.

### 4.3 Full stacked discrepancy and every cut

Within each parallel type w_e is identical. A takes half that type's multiplicity minus 1/2 on spokes and plus 1/2 on triangle types. If W_j=w_j w_j^T for one label of type j, then

    Δ=Σ_{e∈A}w_e w_e^T−Σ/2
      =(1/2)(Σ_triangle W_j−Σ_spoke W_j).

Since every type multiplicity is at least s,

    −Σ/(2s)≼Δ≼Σ/(2s),        ||Δ||≤1/s.                       (4.3)

Both complementary halves have this bound. It is O(1/q), smaller than the r137 paired-MSS tolerance 2√(2ε_t)+2ε_t. Indeed ε_t≥1/q and 1/s≤2√(2/q). The construction therefore satisfies the actual tolerance with an actual faithful normalized rank frame and an every-edge cut frame. It still violates the nontight rank inequality in §4.1. We do not assert an auxiliary-sign realization making the entire four-outcome lifted random-vector sum satisfy its MSS upper bound. The countercheck concerns the resulting half-covariance certificates; it is not a statement that every feature of the MSS selection mechanism permits this bad choice.

All cut counts can also be written explicitly. H's cut at 0 has size 6t+3, at any other single vertex size 10t+3, and at any two-vertex side size 12t+4. The absolute half-discrepancies of A are respectively 3/2, 1/2, and zero. Hence

    max_S ||δ_A(S)|−|δ_H(S)|/2| / |δ_H(S)| = 1/(4t+2).        (4.4)

This does not refute the paired lemma, the source, or a strategy choosing a different good outcome. It demonstrates that even after paying the every-edge condition, the listed matrix/tight/cardinality certificates alone do not logically imply the missing nontight ranks.

### 4.4 Exact cheap repair and exact pure/mixed values

Delete one selected triangle label ij and add one unselected spoke label 0ℓ, with {i,j,ℓ}={1,2,3}. These two types are disjoint edges. Call the result R. R has 2k triangle labels; its complement has 2k−1. Each individual type count on either side is at most 2t+1≤k. Each other triple has at most 4t+3≤2k, the last inequality using t≥1. Both sides have 3k labels. The full forest-union criterion therefore makes both exact unions of k trees. This checks all rank systems, not just the violated triangle.

The changed two labels cross a singleton at most once and a two-side cut at most twice. Some two-side cut crosses both. Consequently this one repair has

    max_S |(R△A)∩δ(S)|/|δ_H(S)| = 1/(6t+2).                 (4.5)

This is also the optimal pure value. In any exact repair the triangle loses at least one selected label, and the degree of 0 increases from k−1 to at least k, so some triangle label is deleted and some spoke label is added. If those two edges are disjoint, a two-side cut crosses both, forcing damage at least 2/(12t+4). If they are incident, their common leaf has cut size 10t+3 and sees at least two changes, forcing a still larger ratio. Extra changes cannot lower unsigned damage. Thus

    v_pure=1/(6t+2).

For a mixed repair every outcome must change at least one spoke label, so the expected load of δ(0) is at least 1/(6t+3). Mix equally the three repairs of opposite triangle/spoke types. Each of the six types is changed with probability 1/3. Its expected normalized loads are 1/(6t+3) at 0, 1/(10t+3) at the other vertices, and 1/(9t+3) at two-side cuts. Therefore

    v_mix=1/(6t+3) < v_pure=1/(6t+2).                       (4.6)

This proves a strict failure of replacing the mixed dual by an equal-valued pure conclusion even at unbounded packing scales and with all the preceding geometric/tight constraints. The ratio tends to ONE; neither it nor this family is an unbounded separating-cost obstruction. The explicit pure repair already costs O(1/q) on every cut. Combining (4.4) and (4.5) gives a repaired relative half-discrepancy at most 1/(4t+2)+1/(6t+2). A fair choice of R and E\R gives every labelled edge exact marginal 1/2.

The family is supporting work only. It is not a restricted solution offered in place of the full question.

## 5. A precise all-edge normalization dual

A second integrated attempt isolates the nondiscarding geometric obligation itself, without appealing to extracted edges. Let N be the source cone of centered PSD matrices whose squared distances satisfy triangle inequalities (this N is a cone, not the matroid of §2). Define

    β(H)=inf_{D≻0; tr(DZ)≤tr(L_H Z) ∀Z∈N}
                         max_{e∈E} b_e^T D^{-1}b_e.

The exact specialization of the source conic-dual proof to single-edge tests gives

    β(H)=sup_{λ∈Δ(E), 0≠Z∈N}
       [tr sqrt(Z^(1/2)(Σ_e λ_e b_e b_e^T)Z^(1/2))]^2
          / tr(L_H Z).                                   (5.1)

For completeness, strict feasibility is supplied by D=δI with 0<δ<λ_min(L_H). Separate the epigraph as in source tg:dual: the max-resistance multipliers are λ≥0 with Σλ=1, and the conic multiplier is Z∈N. The matrix infimum is

    inf_{D≻0} [tr(B_λ D^{-1})+tr(ZD)]
       =2 tr sqrt(Z^(1/2)B_λ Z^(1/2)).

The source's regularization argument handles singular B_λ or Z. Optimizing the scale of nonzero Z gives (5.1); connectivity makes the denominator positive. This invokes the stipulated strong-duality proof operation with its strict-feasibility conditions verified, not an assumption of an optimizer D.

Represent Z by Euclidean points p_v and pad the ambient dimension with zero coordinates if necessary. Nuclear-norm duality, sign changes of the orthonormal rows, and maximization over λ give the equivalent form

    β(H)=sup_{p,U}
       [Σ_{e=uv} |⟨u_e,p_u−p_v⟩|²]
           / [Σ_{e=uv} ||p_u−p_v||²],                    (5.2)

where the rows u_e are orthonormal and the squared distances of the p_v satisfy triangle inequalities. To see the maximization step, for fixed p,U put a_e=|⟨u_e,p_u−p_v⟩|. The nuclear norm is maximized by Σ_e√λ_e a_e; its squared maximum over the simplex is Σ_e a_e², by Cauchy–Schwarz, attained at λ_e proportional to a_e² when nonzero. Maxima over λ and the row system can be interchanged, being two suprema. Zero systems contribute zero. No dimension-dependent factor was suppressed.

This dual pays the exact missing metric hypothesis up to a constant. Let γ(H)=inf_{X∈K_H}max_e b_e^T X^{-1}b_e. For any feasible D, X=L_H+D belongs to K_H and inverse order gives γ≤β after taking limits. Conversely X∈K_H makes D=X/3 feasible, giving β≤3γ. Thus

    β(H)/3 ≤ γ(H) ≤ β(H).                                (5.3)

A decaying uniform estimate for (5.2) on q-tree unions would therefore pay every-edge normalization with no extraction. It is not proved here.

One tempting shortcut can be resolved exactly. For λ concentrated on a single edge uv, the numerator of (5.1) is d(u,v). Each of the q disjoint spanning trees contains a u–v path, and the metric triangle inequality makes each path's total d-length at least d(u,v). Therefore the denominator is at least q d(u,v), so every such singleton test has ratio ≤1/q. This does NOT bound the mixed nuclear-norm numerator: a concave square-root expression can maximize in the interior. Even for orthogonal abstract rank-one matrices, mixing r equal directions can multiply the squared trace-root value by r relative to a vertex. That algebra example is not asserted to arise from these graph metrics or to refute a uniform decaying bound.

The source hierarchy estimate controls boundary-average expressions (Σ_{e∈O}a_e)^2/|O| under local-connectivity and boundary hypotheses. Formula (5.2) instead asks for the sum of individual squares on every original edge. A bound passing from one to the other, without discarding rare labels or paying a dimension factor, has not been derived. The r137 repair and this dual now specify exactly which simultaneous estimates would compose; separate existence of D and of a common base still does not close the construction.

## 6. A distinct coupling attempt after the joint operation stalled

We also examined whether common-base counting, exponential tilting, or a general finite-response sampler can select the required distribution directly. The actual common-polymatroid source counts common integer bases and provides polyhedral/shift/refinement operations; it does not assert that their full-support generating polynomial is stable. The newly inspected geometry interiors contract expanded cells toward separate witnesses with explicit powers of dimension. They pay all ranks in that comparison, but no uniform original-cut damage estimate is asserted.

There is a simple all-scale reason not to import ordinary matroid-base stability for the exact-half family. Let H have k labelled copies of every K4 edge, so it is 2k trees. Let P consist of all copies of 01,02,13, and Q of all copies of 01,03,12. Each and each complement is k repeated spanning paths. Pick a label e of 02 in P\Q. Any f∈Q\P has type 03 or 12. For type 03, P−e+f has degree k−1 at vertex 2, so is not k spanning trees. For type 12, its complement has degree k−1 at vertex 1, so is not k spanning trees. Thus the family of exact halves fails the ordinary matroid basis-exchange axiom for every k≥1.

Choe–Oxley–Sokal–Wagner, arXiv:math/0202034v2, Theorem 7.1 (and the full displayed proof of its stronger Theorem 7.2), says that the support of a nonzero homogeneous multiaffine half-plane polynomial is a matroid base family. Consequently a polynomial with positive coefficients on ALL exact halves of this H cannot have that property. For real homogeneous polynomials the upper and right half-plane conventions differ by a common rotation of the variables. This applies to uniform or positive external-field full-support laws; it rules out this particular stability shortcut, not general dependent sampling.

This is NOT r137's withdrawn pairing claim. For even k, pair parallel labels within each type. Every transversal has k/2 labels of each type and is an exact half, and the independent pair law is a stable law supported on those transversals. The correction and a successful special-case coupling both remain intact. Nothing here precludes a selected good MSS outcome.

The strongest source sampler is broader still. We followed the actual r124 history hit and read the complete source231 decoder and strongly-Rayleigh sections. Its Brownian sampler accepts ANY target law whose finite-tilt means have a common finite sup-norm Lipschitz constant, not just strongly Rayleigh laws. For any law on m finite binary coordinates, the derivative of a tilted mean is a covariance, of absolute value at most 1/4 by Cauchy–Schwarz. Hence L=m/4 always suffices: the source can sample an already specified finite common-base law. It does not thereby give a law supported on the desired thin exact halves.

Nor do fair-complement marginals supply a uniform response estimate. In the fair law on an exact R and its complement, write X_e=(1+s_e B)/2 with s_e=±1 and B a fair sign. At zero field Cov(X_e,X_f)=s_e s_f/4, so every absolute covariance row sum is m/4. This is the source decoder's own two-point response phenomenon with complemented coordinates; it is credited, not nominated. A different carefully chosen law might have a better response. Non-stability alone does not exclude such a law, as r124's actual complemented-law calculation already showed.

No count, sampling, stability or marginal operation examined here supplied a supportwise all-cut bound. No old canonical-sampler, ordered-coupling, all-metric, or directed-arborescence scope is resumed or weakened. This distinct coupling attempt adds a specific all-scale exchange diagnostic and checks the broader available sampler, rather than stopping at a false SR-only limitation.

## 7. Exact unresolved compatibility and limits

The new work since r137 is (a) the joint all-cut repair game with its genuinely compatible cut-cone response metric; (b) the all-scale nontight family, explicit exact radial frame, full stacked estimate, exact repair, and pure/mixed optima; (c) the nondiscarding all-edge conic dual and its factor-three equivalence with the source response domain; and (d) the separate common-base coupling/response attempt above. These are supporting derivations and diagnostics, not a full result nomination.

The unresolved operation is still a uniform nondiscarding choice or repair that enforces BOTH complete rank systems and cardinality while giving summably small discrepancy on EVERY cut of the SAME outcome, with fair-complement marginals, or a different full construction/unbounded separating-cost family. The normalization dual has not been uniformly bounded at the required scale. The repair game has no uniform pure-outcome theorem; the strict gap example is small in ratio and does not prove one impossible.

Labelled parallel edges were retained in every count and covariance. Original tight faces were not replaced by generic perturbations. Zero coordinates of an eventual x would correspond to absent labels; they cannot be reintroduced by a repair. Our formulas do not prove the needed operation on every such support. Real costs in the repair dual were handled by finite-polytope continuity, but this is not the real-x conclusion for the main question. That conclusion would use the already-paid r136 compactness argument only AFTER a uniform exact construction; it is not re-proved or claimed here.

No theorem was frozen, no independent gate was assigned, and no exhaustion, impossibility, current-world-open status, or priority assertion follows. Parent alone integrates, reviews and counts. Publication remains stopped.

forged
