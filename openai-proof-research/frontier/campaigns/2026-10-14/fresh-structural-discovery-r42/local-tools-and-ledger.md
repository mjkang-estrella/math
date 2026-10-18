# Local-palette tools and their exact limits

Write t(P)=max_{p∈P}|D_p(P)| and M=1+t(P). The full frozen target is t(P)≥c_d N^{2/d}; none of the tools below proves it. Let B=N^{1/d}, A=B². In a hypothetical least failing dimension, M/A→0 along a sequence. All lower-dimensional target statements with dimension≥3 may then be used by induction; they are not independently asserted here.

## 1. Radial interpolation is already paid

For each p let R_p=D_p(P), and set

    s_p(x)=∏_{ρ∈R_p} (Σ_j(x_j−p_j)²−ρ²)/(−ρ²).

This complex polynomial has degree≤2(M−1), is1 at p, and is0 at every other sample point. This is the literal proof of source poly:separators with the individual palette substituted; no global palette is needed. For a pure u-dimensional complex variety V of degree a, it gives |P∩V|≤C_d aM^u: for irreducible positive-dimensional V containing p, s_p is nonzero on V and cuts all other sample points in degree≤2Ma; induction on dimension and Bézout prove the bound. Summing over components handles reducible V. The source's isolation system

    1−Σ_p s_p(x),    (x_j−p_j)s_p(x)

has common zero set exactly P and degree≤2M+1. At a common zero the first equation forces some s_p≠0, and the coordinate equations force x=p.

These operations are technical source adaptations. No new polynomial-separator contribution is claimed. Nozaki–Shinohara's actual locally-k-distance terminology and spherical Fisher bounds confirm that local palettes themselves are a classical object; the paper's fixed-k/spherical results do not provide the frozen asymptotic Euclidean bound.

## 2. Proper-flat inputs: precise replacement of the planar cap

A line or circle containing sample points has at most2M points by measuring distances from one of its sample points (for a line one can improve this using an extreme point). A u-flat with3≤u<d has O_u(M^{u/2}) points under the least-failing-dimension pinned induction: its intrinsic pinned distances are subsets of the original ones.

The source's bound C M log(2M) for a plane uses GLOBAL planar distances and cannot be reused with t(P). The actual weak-pinned planar companion cor:pins instead gives: for each fixed ε∈(0,1), all sufficiently large planar sets of size s have a pin with at least s^{1−ε} distances. Therefore every planar subset here has

    s≤C_ε M^{1/(1−ε)}.

In particular, when M≤B² and B→∞, s≤B^{2+o(1)}: taking limsup of log s/log B gives at most2/(1−ε) for every ε>0, hence at most2. This is an asymptotic statement uniform over the chosen sequence, not a bound C M logM and not an effective decay rate. It yields o(N) proper-flat occupancy with a fixed power saving for every d≥3. Source secants250–330 was read: its line-plane-product b h_H≤CM² uses at most M radii separately from each of b axis centers and therefore remains valid. Its term N B^{2+o(1)}log²N is o(N²). Its other term N²M²/A² remains o(N²). These statements justify those specified uses only; they are not a proof that every profile/depth/sparse-cone argument has been transferred.

The parent independently checked the same limited input and recorded it in expanded-target-2026-10-17/parent-r42-planar-support.json. That is author-side assistance, not an independent proof gate. This packet relies on its own pinned companion receipt and direct reading.

## 3. Global pair-flat concentration survives locally; the edge count does not

For the pair-flat parameters of source reduction.tex, products s_p s_q give positive-degree homogeneous separators of degreeO(M), after its stated affine substitution/homogenization. The same source calculation shows that a maximal isotropic parameter plane contains at most N physical pairs: equality of Gram distances makes the first physical coordinate injective. With M≤A, N≤A^{d−1} and total N²=A^d. Consequently the hypotheses of the source's GLOBAL concentration theorem are available with the same scale A. This assertion concerns that exact family, not the diagonal subfamily at a newly reduced scale.

The source's rich-motion statement in dimension3 explicitly proves a stronger two-cloud theorem requiring only that every line contain≤2A points. The local line cap above supplies that condition. Thus that stated motion estimate is paid without a global distance palette. It still supplies ∑_{k_g≥CA} k_g²=O(N⁴/A), not a common-pin isosceles bound of sizeN³/A.

Source red:directions also uses individual radii in its double count. Its sphere/projection fibers require lower-dimensional PINNED induction when using M, including the planar correction above. The sparse-cones theorem is stated under the original global-M contradiction regime; its full adaptation has NOT been proved here. Independent star selection is conditional on that step. No argument below assumes it for free.

## 4. The two different energies

Let k(p,ρ)=|{q≠p:|q−p|=ρ}| and s(ρ)=Σ_p k(p,ρ). Define

    T(P)=Σ_{p,ρ} k(p,ρ)²,
    Q(P)=Σ_ρ s(ρ)².

T counts ordered isosceles triples (p,q,r), allowing q=r. Q counts ordered pairs of ordered positive-distance edges having equal length. Cauchy–Schwarz at each pin gives

    T(P)≥N(N−1)²/M.

A GLOBAL palette of G distances gives Q≥N²(N−1)²/G. A local palette bound M does not replace G in this second inequality. For example, P={2^i e_1:0≤i<N} in fixed R³ has every unordered positive distance distinct: the2-adic valuation of2^j−2^i identifies i, then j. Thus M=N, T=N(N−1), and Q=2N(N−1), whereas N⁴/M=N³. This refutes the unconditioned palette substitution, not the frozen target or the special hypothetical regime M=o(N^{2/3}). The example itself has many pinned distances.

Nor can an unrestricted upper bound T≤C_d N^{3−2/d} be used. In R⁴ take m points on each of two unit circles in mutually orthogonal planes, N=2m. Every cross-circle distance is√2. Each pin has at least m neighbors in one class, so T≥N m²=N³/4. Its within-circle distances make the frozen target plausible, not false. A successful energy approach must discard or charge concentration while retaining enough relevant pairs, rather than postulate the raw energy bound for every point set.

A stronger sufficient pruning statement would be: retain a directed graph of≥cN² positive-distance pairs with its selected-fiber energy≤C N³/A. Indeed, Cauchy–Schwarz across all nonempty selected pin/radius classes gives at least c' N A such classes, so some actual pin sees≥c'A distances. This would prove the full target, but is NOT established here; it is stronger than merely finding one good pin and cannot be inferred from the source's unpinned conclusion.

## 5. Known recurrence and conditional energy tests

The actual proofs of Solymosi–Vu Theorems2.1–2.2 were read. Their common-cell pair/triple counts retain the maximum occupancy m_h of codimension-one/two affine flats. For codimension one the bound is t(P)≥c N/m_h^{(d−1)/d}. Even granting sharp lower-dimensional pinned induction m_h≤C M^{(d−1)/2} (when d−1≥3), solving this gives only

    M≥c N^{2d/(d²+1)}.

For codimension two the bound is t(P)≥c N^{(d+1)/(2d)}/m_h^{(d−1)/(2d)}. With d−2≥3 and m_h≤C M^{(d−2)/2}, it yields only

    M≥c N^{2(d+1)/(d²+d+2)}.

Both exponents are strictly below2/d. Lower-dimensional1/2 cases require their actual separate bounds; no formula using a false one-dimensional square-root exponent is asserted. The planar weak-pinned theorem similarly feeds an exponent approaching3/5 in dimension3 through the first recurrence, not2/3. These are operation comparisons, not new nominations.

One can also quantify what an additional unit-distance input would pay. Suppose, conditionally, that every support cloud of n points in R³ has at most C n^α ordered pairs at any fixed positive distance,1<α<2. Put q=1/α. Since each point belongs to at most M nonempty distance-support graphs, Σ_ρ |support(ρ)|≤NM, hence Σ_ρ s(ρ)^q≤C^q NM. Hölder gives

    Q≥(N(N−1))^((2−q)/(1−q)) /(C^q NM)^(1/(1−q)).

At α=3/2 this is only a constant multiple of N⁵/M³; at α=4/3 it is a constant multiple of N⁶/M⁴. The latter would be ω(N^(10/3)) when M=o(N^(2/3)), supplying the total-energy scale needed by the source's final graph argument, PROVIDED its other local-palette adaptations were completed. No α=4/3 unit-distance theorem is assumed or proved. The calculation diagnoses another substantial missing input rather than solving it by renaming it.
