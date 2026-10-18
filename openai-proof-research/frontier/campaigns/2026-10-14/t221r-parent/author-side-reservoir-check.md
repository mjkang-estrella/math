# Parent author-side reservoir check for T221R

This is author assistance, not an independent proof or contribution gate. The full scope in `../fresh-analytic-discovery-r44/original-scope.txt` is unchanged. The parent read the current proposed `proof.md` in full, and checked the matching arguments in Sections 2–4. The source's localized perturbation/decorrelation bodies have not yet been read by the parent in this continuation. No acceptance or count follows.

## Exact bond normalization

Fix n labelled vertices of degree d, a specified set A of q distinct deficient vertices, and one specified missing port at each vertex of A. Put N=dn−q, assumed even. The remaining N ports have a uniform perfect matching. Let M_d count sets of d nonloop edges with pairwise disjoint endpoints, all outside A. Parallel edges are distinguished by their ports.

If n−q>=2d, then

    E M_d = binom(n−q,2d) (2d−1)!! d^(2d)
            / [(N−1)(N−3)...(N−2d+1)].

Choose the 2d full vertices, a perfect matching of their vertices, and one of d ports at every endpoint. These choices identify precisely one possible d-edge set. Every such set is present with the reciprocal of the displayed pairing denominator. Linearity of expectation proves the formula without an independence assumption between these events. For fixed d and q=o(n), this is asymptotic to d^d n^d/(2^d d!), and in particular is bounded below by a positive constant times n^d.

Every inverse history of bond completion corresponds to exactly one counted edge set: delete that set, declare its 2d endpoint ports missing, and retain the q original missing ports. Uniform missing-port choices make the history probabilities equal. Thus the density relative to the q-cavity configuration law is exactly M_d/E M_d, conditional on A and its marks. It is not a uniform completed matching without this tilt.

## A sharper elementary internal-edge variance

For any fixed h-element set of ports in a uniform matching of N>=4 ports, let U count pairs contained in that set. Then

    E U = h(h−1)/(2(N−1)),
    E[U(U−1)] = h(h−1)(h−2)(h−3)/(4(N−1)(N−3)),
    Var U = h(h−1)(N−h)(N−h−1)/(2(N−1)^2(N−3)).

For the first two identities, count one candidate pair or an ordered pair of disjoint candidate pairs, respectively. Distinct overlapping pairs cannot both occur. Subtracting (E U)^2 and adding E U gives the variance formula. The formulas cover h=0,1,N−1,N as well.

Apply this with h=q(d−1) to the cavity-cavity edge count E_hh. When q=o(n), Var E_hh=O_d(q^2/n). The number L_ff of loops on full vertices has bounded second moment, by the same one- and two-prescribed-pair counts. Thus the exact identity

    E = (dn−q)/2 − q(d−1) + E_hh − L_ff

for the number E of nonloop full-full edges gives Var E=O_d(q^2/n+1). Since

    M_d = E^d/d! + R,  |R|<=C_d n^(d−1),

the independent-copy variance identity and the Lipschitz bound for x^d on [0,dn/2] imply

    Var(M_d/E M_d) = O_d(q^2/n^3 + n^−2).

Consequently any extensive statistic X with Var X=O(n) satisfies

    |E[(M_d/E M_d)X]−E X| = O_d(q/n+n^−1/2).

This sharper rate is optional: the author's O(sqrt((q+1)/n)) estimate already tends to zero for the chosen q. Both are elementary matching estimates; neither alone establishes a substantial contribution or the full spin-glass theorem.

## Star coupling and limits checked

At the j-th new port, after freezing j−1 legal pairs, there are exactly d(n−q−j+1) legal partners: ports on old full vertices not previously used as neighbors. Previously used vertices are excluded in their entirety. This number is independent of the particular previous choices. For a target matching containing a legal new edge, the unchanged preimage and the one switched preimage for each illegal partner have total weight independent of the target. Sequential conditional resampling therefore produces the law conditioned on all new neighbors being distinct old full vertices. At fixed d the expected number of switches is O_d((q+1)/n).

The parent also checked the use of the root-log variance, rather than multiplying a total-variation error by an extensive O(n) bound. Graph-first exposure can couple iid couplings on common edges while resampling them on changed edges. Conditional means given the cavity set and missing ports agree by vertex/port exchangeability.

One precision item was sent to the author: the thermal-variance estimate in Section 5 uses m_1=1/L. Its constants must be allowed to depend on fixed L if the source bound contains m_1^−1. This does not obstruct limits taken first in n at each fixed L, but uniformity in L must not be asserted without evidence.

These are direct mathematical checks of the specified matching interfaces. No exhaustive proof audit, primary-literature clearance, formal theorem certificate, or independent review is claimed. Original prose Myeongjin Kang, CC BY 4.0; no third-party body is copied here.
