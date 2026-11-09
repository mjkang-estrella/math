# MathDB316253 — ordinary reduction of the literal outward-tree claim

Research audit, zero credit. This is an ordinary proof using published structural theorems, not a Lean certificate or a claim of priority. Tree means a finite nonempty connected undirected tree, with a chosen root r and every edge oriented away from r. Degree below is undirected degree. All vertices are observed.

## Exact model, lattice, and cone

Use Sullivant 0704.0918v1/v2 §2, Proposition 2.3, Corollary 2.4, and §5, Theorem 5.1, Corollaries 5.2–5.3. Let R=C[σ_ij: i≤j]. For the unique simple path P_ij, let t_ij be its top (the least common ancestor). Define

φ(σ_ij)=a_(t_ij) ∏_(e∈P_ij) λ_e,
A_ij=e_(t_ij)+∑_(e∈P_ij) f_e ∈ Z^V⊕Z^E,
S=∑_(i≤j) N A_ij, C=R_≥0 S, I_T=ker φ.

The empty path gives A_ii=e_i. For a directed edge u→v, A_uv=e_u+f_uv. Consequently gp(S)=Z^V⊕Z^E: each f_uv=A_uv−A_uu. There is NO index-two condition or parity constraint in these coordinates. This statement concerns the group, not the assertion that these differences belong to S. They need not.

The first isomorphism theorem identifies R/I_T with im φ=C[S] as C-algebras. This uses exactly the variance parameters a_i of the source, not independent noise variances, not a shortest-trek approximation, not a hidden-leaf model.

Write b_j=y_(parent(j),j) if j≠r, and b_r=0; m_j is the number of children. Theorem 5.1 gives the cone inequalities

x_j≥0; y_e≥0; L_jk=x_j+b_j−y_jk≥0; N_j=2x_j+b_j−∑_(k child j)y_jk≥0.

To justify passing from the source polytope ∑x=1 to this cone: if ∑x=0, positivity forces x=0. Starting at the root, L and y≥0 then force every y=0. Any other feasible point has ∑x>0 and rescales into the source polytope. Thus this is the actual exponent cone. It is pointed, full-dimensional, and rational: the columns e_i and e_u+f_uv span, and C is in the nonnegative orthant. The source's normality theorem implies S=C∩gp(S)=C∩Z^(2n−1).

## Exact irredundant primitive facets (n≥2)

The complete list of primitive support forms is:

* x_j, for every j≠r;
* y_e, for every edge e;
* L_jk, for every directed edge j→k;
* N_j, for j≠r with m_j≥2, and for j=r with m_r≥3.

Equivalently the last family is exactly the vertices of undirected degree at least three.

Here are proofs both that omitted inequalities are implied and that every retained one is a facet. Root x_r is implied by x_r=L_rk+y_rk for any root child. For a nonroot leaf N_j=2x_j+b_j is redundant; for a nonroot with one child N_j=x_j+L_jk. At the root, m=1 gives N_r=x_r+L_rk, while m=2 gives N_r=L_rk1+L_rk2. These include all omitted inequalities. The root cannot have m=0 when n≥2.

For irredundancy it suffices to give, for each retained form h, a real point with h=0 and every other retained form positive. A finite positive system has an open neighborhood within h=0 at such a point; the exposed face therefore has codimension one. The following local constructions give those points. All edges not specified are assigned y=1. All other vertex coordinates are assigned a common sufficiently large M>0. Since each vertex's constraints involve only its own x, the incoming edge and outgoing edges, M can make every other vertex's L and N strictly positive without modifying the chosen local data. All unspecified x_j (j≠r) are positive.

1. For y_e: set y_e=0, all other y=1, and every x=M large. Every other retained inequality is strict.
2. For x_j, j≠r: set x_j=0, b_j=1, and each child edge y=ε>0 with m_j ε<1 (if m=0 there are no child edges). Then L_jk=1−ε>0 and N_j=1−m_j ε>0 whenever retained. All other local coordinates are positive.
3. For L_jk: set x_j=2 and b_j=2 if j≠r. Set y_jk=x_j+b_j; all sibling edges have value ε>0 with their sum <1. At j every other L is positive and N_j=2−(sibling sum)>0. The same formula works at the root with b_r=0, y_rk=2. This also works with no siblings.
4. For retained N_j with j≠r: set x_j=b_j=1 and each child edge y=3/m_j. Then N_j=0 and L_jk=2−3/m_j>0 since m_j≥2. For the root set x_r=1 and each child edge y=2/m_r. Then N_r=0 and L_rk=1−2/m_r>0 since m_r≥3.

The other vertices in each construction are completed by the M rule. The rooted-tree hypothesis ensures no edge is simultaneously the incoming and outgoing edge of the same vertex; no completion conflict occurs. Thus all listed inequalities and only those are facets. Distinct forms are not positive scalar multiples, as is also certified by these witnesses. Completeness follows because the finite retained halfspace intersection is C; a facet of a full-dimensional finite halfspace intersection is supported by at least one defining hyperplane.

Primitivity is in gp(S), now proved to be the full coordinate lattice. Every retained form has a coefficient +1 or −1. In particular each retained N has an edge coefficient −1. Therefore no division by 2 is appropriate. For n=1 the only primitive facet form is x_r, not 2x_r.

This facet lemma is the concrete completion missing from r270. Its proof is a local strict-inequality construction, not an enumeration or solver result.

## Classical criterion with its actual ring meaning

For a finite positive normal affine semigroup S=C∩G spanning its lattice, the Danilov–Stanley theorem identifies the canonical module of K[S] with the monomial ideal with exponent set int(C)∩G. It is a Cohen–Macaulay ring (Hochster). It is Gorenstein iff

int(C)∩G=c+S for some c∈G.

This is the ordinary ring-theoretic Gorenstein property (all prime localizations), not a newly defined cone surrogate. Applicable standard graded form: grade each A_ij by ∑x=1, so degree zero is K, each graded piece is finite, and the ring is a finite-type quotient of a polynomial ring. The canonical module is finite and finely G-graded. At the homogeneous maximal ideal, type one is equivalent to one minimal generator; the fine grading permits choosing that generator to be a monomial. Graded Nakayama gives the displayed exponent translation. Conversely this translation makes the canonical module a free rank-one graded module, giving the Gorenstein property. Standard graded/local canonical-module equivalences are classical inputs, not newly proved commutative algebra here.

A primary proof of the canonical ideal theorem was read in Barile–Bruns, arXiv:2505.11402, §5 Theorem 5.1 and proof. A precise statement of the Gorenstein translation criterion appears in Manon, arXiv:1206.2535, §6 Proposition 4, citing Bruns–Herzog Corollary 6.3.8. Sullivant's own normality/CM proof is the source of normality for this model.

For clarity, translation is equivalent to h(c)=1 for all irredundant primitive integral support forms h of C. If these equations hold, integer strict positivity means h(u)≥1, so h(u−c)≥0 and u−c∈C∩G=S; the reverse inclusion is immediate. Conversely the minimum of each h on int(C)∩G is 1. Indeed primitivity gives z∈G with h(z)=1. Choose an integral point w in the relative interior of its rational facet (scale a rational relative-interior point). Every other support form is positive on w; hence z+tw is interior for all sufficiently large integers t and still has h=1. If int(C)∩G=c+S, its minimum h is h(c), since min_S h=0. Thus h(c)=1.

## Forced point and both directions

For n≥2, the x_j facets force c_xj=1 for j≠r; the y facets force c_ye=1 for every edge. Any root L facet forces c_xr−1=1, hence c_xr=2. Therefore there is only one possible translation point:

c=(x_r=2, x_j=1 for j≠r; y_e=1).

Every L has value 1: at a nonroot parent it is 1+1−1; at the root it is 2−1. Every retained N has value 4−deg(j): at a nonroot it is 3−m_j=4−(m_j+1), at the root it is 4−m_r. These are facet values in the actual primitive lattice, not rescaled slacks.

If all degrees are ≤3, each retained N is at a degree-three vertex and has value 1. All facets therefore have value 1 at c. In particular c∈int(C)∩G⊂S by normality. The criterion gives C[S], hence R/I_T, Gorenstein.

If some vertex has degree ≥4, its N is a retained primitive facet, and the forced point has value ≤0 there instead of 1. There is no alternative c because the x,y,L facets already force every coordinate. The criterion gives R/I_T not Gorenstein. This proves necessity, rather than merely rejecting one guessed point.

For n=1, S=N e_r, R/I_T=C[σ_rr] is a polynomial ring and is Gorenstein; the degree is 0 and the translation point is e_r. For n=2, the facet list is x_child,y,L_root and the ring is polynomial in its three covariance coordinates. Paths and roots with one or two children need no N-distance equations at low degree; the general argument covers all those cases. The source's nonempty connected-tree convention does not include forests or an empty graph; neither is needed for this endpoint.

## Scope and qualification

Thus the full ordinary endpoint follows from the source cone/normality and the classical semigroup canonical-module criterion, with the explicit local facet lemma above. No claimed new general canonical-module theorem, no model replacement, and no parity assumption is needed. The novel-to-r270 work is the witness-based irredundancy check and forcing argument. Those are routine finite local consequences of the source inequality description; this is an explicit source/criterion reduction, not an exclusion based merely on short proof length. Under the campaign's no-routine-corollary rule the recommendation is EXCLUDE_ROUTINE_SOURCE_CRITERION_BRIDGE, zero credit. This qualification does not assert the literal characterization was already printed elsewhere. Journal and broad citing-body clearance are incomplete; that is a separate limitation and not grounds for a novelty claim.
