# Author-side conditional global assembly for the full094 target

This is a complementary author contribution, not independent review and not a separate counted result. It proves the global assembly conditional on the precise local theorem below. The structural author owns that theorem's proof and the full candidate. The whole ambient space, every fixed 1<p<∞ with p≠2, every D>1 and one common scale are retained.

## Local input L(p,R,η)

For each fixed p>1, R≥1, η>0 there is a finite exponent A=A(p,R,η)≥0 with the following property. For every real Lp space X, every collection a_1,…,a_N in X with ||a_i||≤R, and every subset U of the closed unit ball of X, there is an actual subset U_0⊂U of cardinality at most (2N+2)^A such that

    ∀u∈U ∃v∈U_0  max_i | ||u−a_i||−||v−a_i|| | ≤η.          (L)

No compactness, closure, measurability or regularity of U is assumed. Empty U permits U_0 empty. The exponent is independent of the space, N, centers and U. Increasing A if needed, assume A≥1. This is exactly the interface communicated by the structural author; it is **assumed here**, not proved here.

## Finite enrichment and extension lemma

Fix 0<κ≤1/4. Put

    R=1+2/κ,   η=κ/(1+κ),
    M=ceil(log(κ^(−2))/log(1+κ)),   A=A(p,R,η).

For every n-point terminal set T={t_1,…,t_n}⊂X, n≥2, there is a finite set E⊂X containing T, with

    |E| ≤ n+n(n−1)M(2n+2)^A,                               (5)

having the following property. If f:E→ℓ_p^d satisfies

    ||u−v|| ≤ ||f(u)−f(v)|| ≤ (1+κ)||u−v||  (u,v∈E),        (6)

then there exists F:X→ℓ_p^{d+1}, agreeing with (f,0) on E, such that for every t∈T and x∈X,

    (1−κ)||x−t|| ≤ ||F(x)−F(t)||
                 ≤ [(1+2κ)/(1−κ)] ||x−t||.                 (7)

The size bound has no aspect-ratio or ambient-dimension dependence. The lemma concerns the enriched set E; it does not assert an extension for an arbitrary previously prescribed map on T.

### Constructing E

For each ordered pair i≠j write d_ij=||t_i−t_j||>0. Use the M radii

    ρ_ijk=κ d_ij (1+κ)^k,       k=1,…,M.

Their closed bins [ρ_ijk/(1+κ),ρ_ijk] cover [κd_ij,d_ij/κ]. Endpoint overlap is harmless. This follows since the left endpoint of the first bin is κd_ij, adjacent endpoints coincide, and (1+κ)^M≥κ^(−2).

For every resulting index (i,j,k), abbreviate ρ=ρ_ijk. Let

    I(i,ρ)={h: ||t_h−t_i||≤Rρ},
    a_h=(t_h−t_i)/ρ  (h∈I(i,ρ)),
    U(i,ρ)={u∈X: 1/(1+κ)≤||u||≤1,
                    ||u||≤||u−(t_h−t_i)/ρ|| for every h=1,…,n}.

The centers a_h satisfy the required bound R, and I(i,ρ) contains i. The constraints defining U say that t_i is a nearest terminal to t_i+ρu, while its distance to that terminal lies in the bin. Apply (L) to these centers and this entire possibly noncompact U. For every selected v∈U_0(i,ρ), retain the original-space point y=t_i+ρv. Let E be T together with all retained points. Formula(5) follows by counting n(n−1)M nets, each of size at most (2n+2)^A. Coincidences only reduce the size. If U is empty there are no representatives. No representative is a terminal: its norm is positive and the nearest-terminal constraints would fail at another terminal.

### Defining the extension

First set F(y)=(f(y),0) for every y∈E. This includes all terminals. For x∉E choose a nearest terminal t_i, breaking ties by index, and put r=||x−t_i||>0. Thus ||x−t_h||≥r for every h.

Call x active if

    r∈⋃_{j≠i}[κd_ij,d_ij/κ].                              (8)

If x is active, choose any covered bin ρ/(1+κ)≤r≤ρ. Then u=(x−t_i)/ρ belongs to U(i,ρ). Choose a representative v supplied by (L), put y=t_i+ρv∈E, and define F(x)=(f(y),0). Fix finite orders on all bins and representatives to make these choices into a map if desired.

If x is not active, define

    F(x)=(f(t_i),r).                                       (9)

All inactive queries use the **same single extra coordinate**. No comparison of two nonterminal queries is required, so they do not need distinct heights or orthogonal directions. This defines F on the entire ambient X. No continuity or measurability is asserted or needed.

### Active-query estimate

Let b_h=||x−t_h|| and b'_h=||y−t_h||. For h∈I(i,ρ), (L) gives

    |b'_h−b_h|≤ηρ≤η(1+κ)r=κr≤κb_h.                       (10)

For h∉I(i,ρ), d_ih>Rρ. Since r≤ρ and ||y−t_i||≤ρ,

    b_h≥d_ih−r>(R−1)ρ=2ρ/κ,
    |b'_h−b_h|≤||x−y||≤r+ρ≤2ρ<κb_h.                       (11)

Consequently (1−κ)b_h≤b'_h≤(1+κ)b_h for all h. Applying (6), because y,t_h∈E, proves

    (1−κ)b_h≤||F(x)−F(t_h)||≤(1+κ)^2 b_h.                 (12)

The upper factor in(12) is at most (1+2κ)/(1−κ): multiply by 1−κ to obtain 1+κ−κ²−κ³≤1+2κ. This proves(7) for active x.

### Inactive-query estimate, including all scale gaps

For h≠i, failure of(8) implies the dichotomy

    d_ih<κr   or   d_ih>r/κ.                               (13)

We can use non-strict inequalities in the ensuing bounds. For h=i the near case d_ii=0 applies. Write d=d_ih, a=||f(t_h)−f(t_i)||, b=||x−t_h|| and

    c=||F(x)−F(t_h)||=(a^p+r^p)^(1/p).

By(6), d≤a≤(1+κ)d. For p≥1, max(a,r)≤c≤a+r.

If d≤κr, then b≤(1+κ)r and b≥(1−κ)r, while

    r≤c≤[1+(1+κ)κ]r.

Hence c/b≥1/(1+κ)≥1−κ and

    c/b≤[1+κ+κ²]/(1−κ)≤(1+2κ)/(1−κ).

If d≥r/κ, then (1−κ)d≤b≤(1+κ)d, and

    d≤c≤(1+κ)d+r≤(1+2κ)d.

The same lower and upper factors follow. This proves(7) for every inactive query, including arbitrarily small radii, arbitrarily large radii, and arbitrarily large intermediate gaps between terminal scales. No geometric grid across those gaps was used.

Finally, if x∈E, (6) directly proves(7). Defining F there first avoids any incompatibility if the active-query rule would have selected a different representative. The finite enrichment lemma is proved.

## Application to pinned094 and the original full scope

Fix p∈(1,∞), p≠2, and D>1. Choose

    κ=min{1/4,(D−1)/8}.

The pinned094 main theorem, applied **once** to E with finite-set distortion 1+κ, supplies a finite map and common scale s_0>0. Divide its coordinates by s_0 to obtain(6). Let γ(p)=2−p for p<2 and γ(p)=1−2/p for p>2. Its dimension obeys

    d≤exp(C_{p,1+κ}(log|E|)^γ(p)).

Since 2n+2≤3n for n≥2, (5) gives |E|≤(1+M3^A)n^{A+2}. Therefore log|E|≤B_{p,κ}log n for a constant B independent of X,T and aspect ratio. The extension dimension is

    d+1≤exp(C'_{p,D}(log n)^γ(p))=n^{o(1)},                 (14)

after enlarging the constant to absorb +1 for n≥2.

Set the final common scale s=1−κ for this normalized map. The ratio of the upper to lower factors in(7) is

    (1+2κ)/(1−κ)²
      =1+(4κ−κ²)/(1−κ)² ≤1+8κ≤D.                          (15)

The first inequality uses κ≤1/4, so (4κ−κ²)/(1−κ)²≤(64/9)κ≤8κ. If κ=1/4, its selection also implies D≥3=1+8κ. Thus(7) is exactly

    s||x−t||≤||F(x)−F(t)||≤Ds||x−t||,

simultaneously for every x∈X and t∈T, in the dimension(14). Equivalently, multiply the whole map by(1−κ)^(−1) to make the final lower scale1. This is a single global rescaling, not a query-dependent one.

This proves the original full094 terminal conclusion **conditional on (L)**. The p=2 case, efficiency, continuity, measurability and query-query distortion are not asserted as new results. No condition on aspect ratio, finite ambient dimension, separability, or a finite query set has entered.

## Attribution and limits

The structural author and root independently suggested the interterminal-distance bands and common height before this detailed proof was written. The proof above is joint author-side assembly with those suggestions credited, not an independent gate or separate novelty claim. The local entropy theorem is proved in the separate author note `../fresh-structural-discovery-r39/profile-cover.md`; it is assumed here and has not been independently reviewed by this author. The finite source embedding is stipulated; only its applicability and size substitution are checked here. The tetrahedron objection to arbitrary finite-map outer extension is bypassed by choosing a map on E after enrichment; it is not disputed.

The generic enrichment method is prior work: Elkin–Neiman, *Near Isometric Terminal Embeddings for Doubling Metrics* (SoCG2018), §§2.3–3.2, explicitly applies a finite embedding to an enriched set, adds one shared height coordinate, and uses a close/far terminal dichotomy in unrepresented scale gaps. These operations are credited to that paper, not claimed new here. Their construction uses actual metric nets and doubling to bound the enrichment. Here the assumed input covers only terminal-distance profiles, so active queries are sent directly to their representative image; closeness to the representative is neither proved nor needed. The O(n²) collection of interterminal bands is sufficient because a polynomial enrichment, rather than a linear one, preserves the pinned subpolynomial dimension. This adaptation is supporting assembly for the full candidate; its contribution status is for independent review, not this note to decide.
