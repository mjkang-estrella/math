# Source330: retained mathematical work, no frozen nominee

All spaces and operators in this note are real. These are full supporting derivations and feasibility calculations, not a manuscript, formalization, contribution grade, or acceptance request. No substantial research theorem was frozen. In particular, the finite-core criterion below was developed as a feasibility calculation and is retained to rule out a proposed geometric direction; it is not retrospectively declared a frozen target.

## 1. What the source and original construction already buy

At the stipulated pin, Source330 constructs a bounded infinite block M_p, a finite anchor set A_p containing o, and a globally 1-separated shortest-path vertex metric. It fixes

    L=10p, R=30p, K=10p(R+1), D=K+2L+5,
    B=4R+D=300p²+150p+5, V=1+4pB,
    Δ even, Δ≥4, V/Δ<1/20,
    Q=Δ^(2L+1), H=Δ^(D+1), k>2ΔQH, ρ=ΔQH/k<1/2.

Its finite graph sequence is fixed before the operator. Graph incidences, including reversed loop incidences and parallel edges, are distinct. Labels are capped color distances and globally 1-Lipschitz. Attachment distance is exactly R. Balls of radius 2L have at most Q points, and at most H coordinates of any label are below D. Source lemmas give affine mass-one signed measures, TV≤V, bump integral≥3L/4, rare matched walks, continuation records, scalar extensions and the averaged contradiction. The conclusion concerns every bounded finite-rank operator of norm≤p, with error≥1/2 at some fixed anchor. Finite rank is not finite coordinate support; the source perturbs range basis vectors in operator norm to obtain the latter.

The bounded-block coefficient estimate is (1/2)||c||₁≤||Σc_xδ_x||≤B||c||₁. Thus the block itself has 2B-BAP. The metric wedge, with cross distances d_p(x,o)+d_q(y,o), has AP and no finite BAP bound. It has a single global separation constant 1; it is countable, complete, unbounded, nonproper, and has neither bounded geometry at every radius nor doubling. These facts, quantitative ℓ¹ renormings and failure of nonlinear approximability are already supplied in the source. No rebranding of them is proposed here.

The original I90 construction is a stronger comparison than the original source's finite support count. It uses pairwise bad states, a dominating positive measure ν, and a clipped observable on colored local types. For λ-bounded edge pairings its exact inequality is

    ν(S)(H/k)ρ^n + Vτ_m(n) ≥ 3/8 − λ/(4L) − V/Δ.                 (1)

For a rank-r operator, the augmented measure range lies in a subspace E of ℓ¹ of dimension≤r+1. An Auerbach basis gives a positive envelope ν_E of mass dim E such that |u(j)|≤||u||₁ν_E(j). Take ν=Vν_E. At τ_m(n)≤1/(40V), λ≤2p and anchor error<1, I90 obtains

    rank(T)+1 > kρ^(−n)/(4VH),  rank(T) ≥ kρ^(−n)/(8VH).

Its original full scope includes maps from the inherited finite truncation X_m into either X_m or the entire block. This is an operative prior proof, not an unresolved bridge and not an r206 target. No old verdict or count was used as a mathematical premise.

## 2. A complete finite-core cutoff calculation

Let G be a countable connected undirected graph. Parallel edges and loops are allowed. Every edge has a finite length at least 1. Take only the vertex set M as points and give it the path-infimum metric d. Let S be a nonempty finite set of vertices containing the basepoint o. Suppose that after deleting S and its incident edges, the graph H is locally finite: every remaining vertex is incident with finitely many remaining edges. No bound on the degrees, graph diameter, edge lengths from above, number of H components, or the number of edges incident to S is imposed.

For X=F(M), identify F(S) isometrically as a subspace of X. Suppose P:X→F(S) is a bounded linear projection, and put C=||P|| and A=max(1,C). The calculation proves A-BAP, with the following stronger intermediate assertion:

For every finite E⊂M and ε>0, a finite-rank T:X→X fixes every δ_x for x∈E∪S and has norm at most A+ε. Its range has finite coordinate support. In particular X has max(1,|S|−1)-BAP, and has MAP when |S|≤2.

This is a supporting lemma, not a nominated substantial theorem. The exact bound in terms of P incorporates any stronger known extension/projection construction on the core; the elementary cardinality bound is only one substitution.

### Metric and support details

Connectivity makes d finite. For distinct vertices every connecting path uses at least one edge and so has length≥1. Hence d(x,y)≥1; it is a metric, rather than a pseudometric. Reversal and concatenation prove symmetry and the triangle inequality even if shortest paths are not attained. Every d-Cauchy sequence is eventually constant. Thus M is complete and globally uniformly discrete. It need not be proper: an infinite unit-edge star is included.

Use the internal weighted path distance d_H inside H, taking +∞ between its components. This is generally larger than the restriction of d, since paths through S are excluded. Each d_H-ball of finite radius has finitely many vertices. Indeed any path of length≤r+1 has at most floor(r+1) edges; local finiteness gives a finite combinatorial ball. The same observation applies to vertices of d_H-distance≤r if the infimum is not attained, by approximating paths of length<r+1. This justifies finite support without falsely declaring M proper.

Remove S from E. If the resulting set is empty, T=P already fixes the required evaluations and has norm≤A. Otherwise choose

    D₀≥max(1,max_{e∈E} d(e,S)),   t(x)=inf_{e∈E}d_H(x,e), x∈H.

A finite set has a distance minimum for d(e,S); for t it is harmless to use infima. Set t=∞ in H components disjoint from E. For t(x)<∞, the triangle inequality along H paths gives

    d(x,S)≤D₀+t(x).                                                   (2)

For an edge x–y in H of length l, either both t values are infinite, or both are finite and |t(x)−t(y)|≤l. No such assertion for an edge incident to S is used.

Put η=ε/(1+C), and define

    φ(x)=max(0,1−η log(1+t(x)/D₀))  if t(x)<∞,
    φ(x)=0                         if t(x)=∞.

Then φ(e)=1 at every e∈E. It vanishes unless

    t(x)<D₀(exp(1/η)−1).

Only finitely many H components meet E, and their bounded internal balls are finite; consequently U={x∈H:φ(x)>0} is finite.

### The explicit Banach-valued map and all edge cases

Define

    f(a)=δ_a                           (a∈S),
    f(x)=Pδ_x+φ(x)(I−P)δ_x             (x∈H).

It is pointed: f(o)=δ_o=0. Since P fixes F(S), the definitions agree with the identity on E∪S. Its range lies in F(S∪U), a finite-dimensional space. This fact comes from the explicit formula; no range sparsification theorem is being assumed.

If x,y∈H are joined by an edge of length l and both t values are infinite, f(x)−f(y)=P(δ_x−δ_y), of norm≤Cl. If the t values are finite, orient the unordered pair so t(x)≤t(y). Then φ(x)≥φ(y), and

    f(x)−f(y)=[φ(y)I+(1−φ(y))P](δ_x−δ_y)
              +(φ(x)−φ(y))(I−P)δ_x.                                (3)

The first term has norm≤Al, since convex combinations of I and P have norm≤A. For each a∈S, (I−P)δ_a=0, so

    ||(I−P)δ_x||≤(1+C)d(x,a),
    ||(I−P)δ_x||≤(1+C)(D₀+t(x)).                                    (4)

Clipping cannot increase the difference of the decreasing logarithmic cutoff, hence

    0≤φ(x)−φ(y)
      ≤η log((D₀+t(y))/(D₀+t(x)))
      ≤η(t(y)−t(x))/(D₀+t(x)).                                      (5)

Equations (3)–(5) give ||f(x)−f(y)||≤(A+ε)l. This also covers clipping through zero. A loop has equal endpoint values and causes no issue.

For an edge from x∈H to a∈S of length l, no cutoff continuity across the core is needed. Instead,

    f(x)−δ_a=[φ(x)I+(1−φ(x))P](δ_x−δ_a),

of norm≤Al. Edges within S have endpoint difference of norm d(a,b)≤l. Summing these estimates along any finite path and then taking its infimum gives

    ||f(x)−f(y)||≤(A+ε)d(x,y) for all x,y∈M.                         (6)

The cancellation (I−P)δ_a=0 is the reason this works even when infinitely many edges meet the finite core. A direct cutoff of δ_x that ignored that term would not have the same bound.

### Linearization, compact sets, and the exact BAP constant

For a finite combination u=Σc_xδ_x define T u=Σc_x f(x). To verify boundedness without an unproved Banach-valued extension, compose f with any norm-one functional z* on X. The scalar function z*∘f vanishes at o and has Lipschitz norm≤A+ε by (6). Therefore

    |z*(Σc_x f(x))|≤(A+ε)||Σc_xδ_x||.

Taking the supremum over z* proves well-definedness and the norm bound; completion gives T:X→X. It fixes the indicated evaluations and its range is contained in F(S∪U), so it is finite rank.

For clarity, this first gives norms A+ε with exact fixing; the final A-BAP claim needs another step. Given compact K⊂X and accuracy δ>0, take a finite δ/[4(A+2)]-net {u_i} of K and finite evaluation combinations v_i with ||u_i−v_i||<δ/[4(A+2)]. Let E contain all their supports. With 0<ε≤1 choose the above T, and put W=A T/(A+ε). Then ||W||≤A and

    ||Wv_i−v_i||= ε||v_i||/(A+ε).

Choose ε so small that this is<δ/2 for every i. For u∈K choose its net point u_i; then ||u−v_i||<δ/[2(A+2)] and

    ||Wu−u||≤(A+1)||u−v_i||+||Wv_i−v_i||<δ.

This proves the precise compact-set A-BAP quantifiers. The empty compact set imposes no condition. The unscaled operators T need not be projections, and no commuting approximation or FDD is asserted.

Since M is countable, an exhaustion of its vertices and choices ε_n↓0 give a sequence T_n, uniformly bounded by A+1, fixing longer and longer finite evaluation spans. Density gives T_n u→u for all u; compact convergence follows by finite nets. Scaling gives a sequence with norm≤A. This sequencing uses the proved uniform bound; it is not a claim that AP alone implies a single convergent sequence of finite-rank operators.

Finally F(S) has dimension |S|−1. Independence follows by prescribing scalar values at its finitely many distinct points and extending scalar Lipschitz functions; no two evaluation coordinates coincide. Choose an Auerbach basis v_1,…,v_m of F(S) and extend its norm-one coordinate functionals to X by Hahn–Banach. Then P x=Σφ_i(x)v_i is a projection with ||P||≤m. The zero-dimensional case is P=0. This proves the stated cardinality bound. Any better projection norm, equivalently any better linear extension operation on the finite core, enters (2)–(6) unchanged.

### Consequences and exact scope limits

A countable weighted graph with edge lengths bounded below and finitely many infinite-valence vertices has BAP in its real free space: include those vertices and the basepoint in S. If there are none, choose S={o}. Therefore a vertex-graph realization of an AP/no-BAP space of Source330 type cannot put all infinite valence into finitely many vertices while preserving a positive lower edge-length bound. The criterion allows nonproper spaces, including an infinite star and an infinite two-hub graph; those particular examples have MAP.

The criterion does not assert that every uniformly discrete metric has such a graph presentation. The complete weighted graph presentation has infinite valence everywhere. It does not allow edge lengths tending to zero, and it does not assert properness of H in the inherited metric. It proves no metric retraction onto S, and no inverse or section of a quotient is inferred. Nor does it prove a universal bound independent of |S| or of the actual core projection norm. Source330's finite blocks have finitely many anchors and individually have BAP, so this calculation is fully compatible with the stipulated source; its whole wedge has infinitely many anchors.

## 3. The strongest compatible graph realization

Source330's edge lengths are positive integers. Subdivide each non-loop edge of length m into m unit edges, with new interiors disjoint for different edge instances; a loop can be discarded without changing vertex distances. The resulting graph vertex set is countable and globally 1-separated. Every route between original vertices decomposes into original weighted edges after removing excursions that return to the same endpoint, so the original metric is preserved. Conversely each original weighted route is realized by its subdivision. Triangle inequalities are supplied by the unit path metric, not by a separately prescribed cross-block distance.

There is a contractive map from these vertices to F(M): the vertex at position j on a subdivided edge u–v of length m is sent to (1−j/m)δ_u+(j/m)δ_v. Adjacent values differ by (δ_v−δ_u)/m, whose norm is d(u,v)/m≤1. Linearization gives a norm≤1 projection from the new free space onto the isometric original free subspace, fixing each original evaluation. This is a Banach-valued interpolation, not a Lipschitz retract to M.

The new vertex metric is uniformly discrete, so Kalton's actual Proposition 4.4 supplies AP. If it had λ-BAP, compression by the contractive inclusion and projection would give λ-BAP for the original wedge; hence it has no BAP. This completes that construction, with all norm and metric interfaces. It is the standard subdivision/interpolation/complemented-transfer composition, and is not nominated. Brudnyi–Brudnyi's actual Lemma 10.6 already supplies much stronger finite degree-reduction gadgets for prescribed-range extension obstructions; that does not turn a proper bounded-degree graph into a no-BAP example. Their obstruction is to extension onto a prescribed subspace, while a finite graph's identity still has rank finite and norm one.

## 4. Why tuning the source's scales cannot give a linear diameter bound by this certificate

Retain the specific one-step comparison design: operator allowance q, attachment length R, bump height L, bump slope L/K, anchor error e≥0, and a certified bump integral at least aL with 0<a<1. To obtain that certification solely by the source's operator/anchor triangle estimate requires

    (qR+e)/K≤1−a.                                                    (7)

To keep the full 2L-state balls inside their source graphs by the source's short-path argument requires R>2L. Even with exceptional losses optimistically set to zero, the averaged test contradiction requires 2aL>q. Finally the source's cap/diameter design has B≥D≥K. Consequently

    B≥K≥qR/(1−a)>2qL/(1−a)>q²/[a(1−a)]≥4q².                        (8)

This is a lower bound on these sufficient certification inequalities, not on every possible Lipschitz-free obstruction and not on the optimal BAP constant of every bounded metric. It explains why merely optimizing L,R,K or the paid block schedule cannot certify diameter O(q). Removing it requires an operation that changes one of (7), short-path isolation, or the scalar-edge height comparison; no such operation is proved here.

There is also a concrete failure when trying very short attachments. If 2R+1≤2L, then along every source edge x–y the attached anchors satisfy d(a(x),a(y))≤2R+1≤2L using the route a(x),x,y,a(y). Thus the finite support S=A matches every nonbacktracking source walk via j_i=a(x_i), with exactly matching labels. Every root is bad for all walk lengths. Pairwise weighting and clipping from I90 do not remove that deterministic matching path.

## 5. Strongest-reduction assessment and unresolved research operation

The completed finite-core calculation uses classical finite-dimensional complementation and the logarithmic multiplier estimate already present in Kalton 2004, now measured in the graph with its core deleted. Godefroy 2024 Proposition 2.1 identifies the full compatible extension/projection operation, and its Proposition 2.2 records the stronger general finite-set extension bound. Thus it would be misleading to market the elementary |S|−1 bound alone as a substantial contribution. The calculation is retained because it settles a geometric feasibility issue and supplies the exact cancellation and constant, not because a literature-wide novelty claim has been established.

The remaining research opportunity is a distinct construction or comparison that survives this finite-core cutoff obstruction and the paid source/I90 operations. The scale calculation isolates an exact missing operation for a linear-diameter direction, but there is no proposed or frozen theorem asserting that such a construction exists. No closed target has been renamed or reopened. There is no unresolved proof step in the supporting finite-core calculation; the round has not produced a substantial full-scope nominee. The final disposition is PREFREEZE/no nominee.
