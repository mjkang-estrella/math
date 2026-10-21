# Prefreeze calculation: a single osculating parameter replaces exponential avoidance

This is an explicit primary/classical construction inside SOURCE001, not a frozen theorem or contribution assertion. Huang–Sottile–Zelenko arXiv1609.06793v1, §§2.1–2.3, supplies the Wronski evaluation/projection mechanism and the Lagrangian relation for the self-adjoint differential operator d^(2m)/dt^(2m). The calculation below makes its coefficient and field-degree implications explicit. The cyclic construction in the next note gives a sharper bound over a field containing the required roots of unity; its total cost over the original field is compared separately.

Let k have characteristic zero, m>=1, n=2m−1, and V=k[t]_(<=n). On monomials put

    B(t^i,t^j)=0 (i+j != n),
    B(t^i,t^(n−i))=(-1)^i / binom(n,i).

The form is alternating and nondegenerate because n is odd and its anti-diagonal entries are nonzero. Differentiation is infinitesimally skew-adjoint: if i+j=n+1,

    i (-1)^(i−1)/binom(n,i−1) + j (-1)^i/binom(n,i)=0,

and all other pairings vanish. Consequently translation f(t)->f(t−theta), its finite exponential, preserves B over any extension. The subspace t^m k[t]_(<m) is isotropic: the degrees of two monomials there sum to at least2m>n. It has dimension m, so is Lagrangian. Thus

    L_theta=(t−theta)^m K[t]_(<m) subset V_K

is Lagrangian for every theta in an extension K/k.

Take any k-subspace W of dimension a<=m. Choose a basis f_1,...,f_a of distinct increasing degrees d_1<...<d_a<=2m−1 by row reduction. Their Wronskian has leading coefficient

    (product leading_coeff(f_j)) product_(i<j)(d_j−d_i),

up to the consistent determinant sign, and degree sum d_j−a(a−1)/2. It is nonzero in characteristic zero and its degree is at most a(2m−a)<=m². If [k(theta):k]>m², this polynomial cannot vanish at theta. The first a jet evaluations are therefore injective on W_K. Since belonging to L_theta means all first m jets vanish, L_theta cap W_K=0.

For a>m choose an m-dimensional k-subspace W0 of W. The m-jet map has rank m on W0_K, hence on W_K, and its kernel on W_K has dimension a−m. This proves, for EVERY k-subspace W simultaneously,

    dim_K(L_theta cap W_K)=max(0,dim_k W−m).             (O1)

No countability of the subspaces is used. The coefficients of the Wronskians are in the fixed field k; the assertion is false with arbitrary K-subspaces replacing k-subspaces.

For several symplectic blocks with half-dimensions m_i, transport this model by k-rational symplectic isometries. One theta of degree>max_i m_i² suffices for all blocks. Unlike the source's independent coordinate substitution, the block choices are correlated along one curve; the Wronskian calculation proves that this correlation does not lose the universal transversality needed.

In SOURCE001 write k=K0 H, where H/Q_p is finite and carries the split endomorphism data and symplectic bases. A uniformizer pi of H remains a uniformizer of k: H over its maximal unramified subfield is totally ramified and its Eisenstein polynomial remains Eisenstein after extending the unramified field to K0. Choose d=max_i m_i²+1 and theta^d=pi. Then [k(theta):k]=d by Eisenstein, and theta is algebraic over Q_p. All flags are defined over H(theta), so finite local-field descent is preserved, even when p divides d.

Opposite blocks are still assigned by u. All source stable-subobject slope inequalities and the largest-maximizer argument apply unchanged. This closes a quadratic relative-degree construction of the flag, without giving any bound on the later abelian realization, marking, quasi-isogeny or cycle denominator. Its determinant and symplectic operations are already classical/primary; no substantial-contribution assertion is made.
