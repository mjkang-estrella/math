# OA057: virtual abelianity for finite SNC root orbifolds

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Author proof for independent review, not an acceptance or a priority certification.

## 1. Original full target and stipulated input

Let X be a connected smooth projective complex variety of dimension n. Let D_1,...,D_s be distinct smooth irreducible divisors with simple normal crossing union D, and let m_1,...,m_s be arbitrary integers at least two. Write R for the simultaneous root orbifold with charts z_i=w_i^{m_i} along the components through a point. A line bundle on R means compatible equivariant holomorphic lines on these charts. The orbifold is special if no nonzero map L -> Omega_R^p has kappa(L)=p for 1<=p<=n, with Iitaka dimension computed from equivariant plurisections.

**Theorem OA057.** If R is special, then the entire discrete group

    G = pi_1(X minus D) / << gamma_i^{m_i} : 1<=i<=s >>

is virtually abelian. Empty boundary and n=0 are included. No finite uniformization, residual finiteness, linearity, positivity, dimension bound, prime-order restriction, or disjoint-boundary assumption is imposed. No uniform index bound is asserted.

The stipulated input is the full manifold abelianity theorem, `thm:abelianity` of the pinned family057 manifold paper at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb: every special connected smooth compact Kähler manifold has virtually abelian entire fundamental group. No upstream theorem is audited. The order-two fourfold companion supplies antecedent transfer and cover operations; those are credited in Section 9.

We prove a stronger construction statement independent of this input: every R above admits a dominant map f:Y->R from a connected smooth projective manifold, with connected abelian-variety general fibre, local submersive lifts over the general point of every base prime divisor, and g^*D_i divisible by m_i as an integral Cartier divisor, where g:Y->X is the coarse map. These properties transfer specialness and give a surjection pi_1(Y)->G.

If s=0, take Y=X and apply the stipulated theorem. If n=0, X is a point and s=0. Henceforth n>=1 and s>=1.

## 2. A finite affine action for every modulus

Put M=lcm(m_1,...,m_s), N=n+1 and r=sN. Index the r coordinates by I={(i,j):1<=i<=s,1<=j<=N}; give I any total order. Let A=(Z/M)^I with generators e_a. Choose an elliptic curve E and a point c of exact order M. Let W=E^{Z/M}, let R_0 be the cyclic shift

    (R_0 x)_k=x_{k+1},

and let C=(c,...,c). The shift fixes C. For each ordered pair a<b of indices, take a factor W_ab and let e_a act there by R_0, e_b by R_0^{-1}+C, and every other generator by the identity. These actions commute, and both displayed generators have Mth power identity. They therefore define an algebraic action of A on the abelian variety

    F=product_(a<b) W_ab,     dim F=M binom(r,2).

For h=(h_a) in A its action on W_ab is exactly

    x |-> R_0^{h_a-h_b}x + h_b C.                         (2.1)

This formula is independent of representative integers because R_0^M=1 and MC=0. In particular, if h_a=h_b=t !=0 in Z/M, its action on that factor is the nonzero translation tC and has no fixed point. Thus:

**Repeated-coordinate criterion.** Any h with two equal nonzero coordinates in A acts without fixed points on F.

Each individual generator e_a, on the other hand, has a fixed point on F. The shift R_0 fixes the zero vector. The map R_0^{-1}+C fixes the vector x_k=k c, since x_{k-1}+c=x_k, including the wraparound by Mc=0. Choose these points independently on all factors involving e_a, and arbitrary points on the others. No simultaneous fixed point for distinct generators is claimed or needed. Nor is it claimed that every element with support at least two acts freely: (2.1) only gives the repeated-coordinate criterion. The distinction is essential for composite M and for the resolution step below.

## 3. A smooth auxiliary Kummer cover with all boundary orders retained

Set d_i=M/m_i. Choose line bundles H_i so positive that H_i^M(-d_iD_i) is very ample. Choose, for each i, N general members B_ij of this linear system. They may be taken nonempty, reduced, smooth, with no common prime components, and with D+sum B_ij SNC. For n>=2 these members may also be irreducible. For n=1 they are generally disconnected reduced sets of points; irreducibility is neither assumed nor used. Sequential Bertini and avoidance of the finitely many strata give the SNC requirement in every positive dimension.

Adjoin Mth roots

    y_ij^M=s_(D_i)^{d_i} s_(B_ij),                       (3.1)

where y_ij is valued in H_i, and normalize. The resulting cover pi:S->X is connected and Galois with group A. Indeed, in rational frames any multiplicative relation among the right-hand sides modulo Mth powers has exponent zero modulo M at a prime component of each B_ij, since that component occurs in only that factor and with coefficient one. Their classes form a copy of (Z/M)^r in C(X)^*/C(X)^{*M}; the elementary Kummer correspondence over C(X), which contains all Mth roots of unity, gives degree M^r and group A. S is finite and projective over X.

Here is its entire local normalization, including simultaneous intersections. At a point x, let J be the set of i with x in D_i and let K be the set of labels a=(i,j) with x in B_ij. The SNC condition implies |J|+|K|<=n. After shrinking analytically, take all roots of nonvanishing units. If i is not in J, the passing equations from its block simply introduce independent Mth roots of the corresponding B_ij coordinates; its other roots distinguish sheets.

If i is in J, at least two labels (i,j) are absent from K: N=n+1 and |K|<=n-1. Choose one such label j_0. Its local equation is y_ij0^M=z_i^{d_i}. Each irreducible local component has normalization w_i^{m_i}=z_i, with y_ij0 a constant root-of-unity multiple of w_i. After adjusting that constant, every passing B_ij introduces a coordinate v_ij=y_ij/w_i satisfying v_ij^M=t_ij. Absent B_ij give constant root-of-unity multiples of w_i and distinguish components. These independent-root charts are smooth, finite over the base, and have exactly the generic sheets of (3.1), so they are the normalization. Performing this in all disjoint blocks gives smooth S.

The stabilizer of a point of S above x is precisely

    H_x = < tau_i (i in J), e_a (a in K) >,
    tau_i = d_i sum_(j=1)^N e_(i,j),                    (3.2)

where tau_i has order m_i and changes only w_i by a primitive m_i-th root. The e_(i,j) with (i,j) in K change only v_ij by a primitive Mth root. These generators are independent: in each boundary block a missing coordinate forces a putative coefficient of tau_i to vanish, and then the auxiliary coefficients vanish. Thus (3.2) is a product of the specified cyclic factors, not just a generating list. Also pi^*D_i=m_i R_i with R_i a reduced Cartier divisor on S.

## 4. Eliminate the boundary inertia while retaining auxiliary sections

Let V=S x F with diagonal A action and let Z=V/A be its projective coarse quotient. V and Z are connected, and Z is normal. Projectivity follows, for example, by taking the tensor product of the translates of an ample bundle, a sufficiently divisible linearized power, and the invariant section ring. Write h:Z->X for the induced map.

Fix a point of V over x. Its stabilizer H is a subgroup of H_x. Express an element of H_x uniquely as

    sum_(i in J) a_i tau_i + sum_(b in K) b_b e_b,
    a_i in Z/m_i, b_b in Z/M.                           (4.1)

If some a_i is nonzero, choose two distinct missing auxiliary labels in block i. The corresponding coordinates of (4.1) are both d_i a_i, a nonzero element of Z/M. By the repeated-coordinate criterion this element has no fixed point on F. Consequently every actual point stabilizer H has every a_i=0. In other words:

    all point stabilizers of V act trivially on every boundary root w_i.  (4.2)

They may have complicated auxiliary isotropy. We do not assume they are cyclic or that the coarse quotient is smooth.

The line bundle O_S(R_i), its canonical section, and the equivariant identity O_S(R_i)^m_i=pi^*O_X(D_i) pull back to V. The stabilizer acts trivially on its fibre at every point. At a zero of the section its character is the character of the local root w_i (or its inverse according to frame convention), which is trivial by (4.2). Off that zero locus the invariant nowhere-zero section trivializes the fibre equivariantly.

We use the elementary finite-quotient descent fact: a linearized line bundle descends to the coarse quotient if every point stabilizer acts trivially on its fibre. Locally analytically, choose a small invariant neighbourhood of one orbit point and a section nonzero there. Average it over its stabilizer; the averaged value at the point remains nonzero because that stabilizer acts trivially. Shrink again to obtain an invariant nowhere-zero frame. On the disjoint translates of the neighbourhood these frames give a quotient frame. Invariant transition functions descend and glue. This proves descent of the line, its equivariant sections, and equivariant tensor identities. The resulting coherent line bundles and maps on projective Z algebraize by GAGA.

We therefore obtain lines T_i on Z with sections t_i and identities

    T_i^{m_i}=h^*O_X(D_i),     t_i^{m_i}=h^*s_(D_i).     (4.3)

They define a map Z->R, even though Z may be singular. Choose a projective resolution rho:Y->Z that is an isomorphism over the smooth locus of Z. Then Y is connected smooth projective, g=h rho is surjective, and pulling back (4.3) gives a genuine map f:Y->R. In particular

    g^*D_i=m_i E_i                                         (4.4)

for an effective integral Cartier divisor E_i on Y, including every exceptional component. No divisibility on X itself is required.

Over U=X minus (D union all B_ij), the cover S->X is an étale A torsor. Thus Z|_U=(S|_U x F)/A is an étale-locally trivial F bundle and is smooth. The resolution changes nothing there. General fibres of g are connected copies of the abelian variety F and have trivial cotangent bundle.

## 5. Divisorial submersions survive arbitrary quotient resolution

We check every base prime divisor, not merely a selected good open.

For a boundary component D_i, take a general point outside every other D_k and B_kl. Its inertia on S is <tau_i>. Every nonidentity element has at least two equal nonzero coordinates, so acts freely on F. Consequently the diagonal action is free over this locus, the quotient Z is smooth there, and rho is an isomorphism. Locally, a quotient neighbourhood is isomorphic to a neighbourhood in S x F. Projection to the root coordinates (w_i, the other base coordinates) is a submersion. This is a submersive local lift of f over the general point of D_i.

For a prime component P of some B_a, take a general point outside all D_i and the other auxiliary divisors. The local cover has inertia <e_a> and equation w^M=t, with the remaining base coordinates unchanged. Choose a point v of F fixed by e_a, whose existence was proved in Section 2. The map w |-> (w,v), with the remaining base coordinates unchanged, is equivariant and descends to a local analytic section

    sigma:U_P -> Z,     h sigma=id_(U_P),                  (5.1)

over a small base neighbourhood. Away from P this section lies in the smooth locus of Z, where rho is an isomorphism.

We recall why (5.1) lifts near a general point of P under any proper resolution that is an isomorphism off its singular locus. Over U_P minus P, take its unique lift to Y. The closure of the graph is a proper bimeromorphic analytic space over U_P; equivalently it is the dominating component of U_P x_Z Y, with its reduced structure and normalization. Its projection is an isomorphism off P. A proper bimeromorphic morphism to a smooth space is an isomorphism over the general point of every prime divisor of that target. One proof is to localize at the generic point, where the target is a DVR: the inverse rational map extends by properness, and its extension agrees with the inverse on the dense open; after spreading out it is an inverse on a neighbourhood of that generic point. In the analytic setting the same local statement is the codimension-at-least-two indeterminacy of a meromorphic map from a smooth space to a proper space. Thus a holomorphic lift of sigma exists after removing a proper analytic subset of P.

At such a point the identity g sigma_tilde=id differentiates to dg d(sigma_tilde)=id. Hence g is submersive at the lifted section point. The image of the algebraic smooth locus of g is Zariski open, so obtaining such a point over P implies that such points exist over a nonempty Zariski open subset of P. This proves the required ordinary submersion over a general point of P. It is crucial that the fixed point was chosen before quotienting and that resolution is proper; merely resolving a cyclic quotient does not assert a submersion at every exceptional point.

Every other prime divisor has its general point in U, where g is smooth. These cases exhaust the divisorial tests. No claim of a globally smooth fibration is made.

## 6. Specialness transfer at full SNC scope

For completeness we reproduce the source companion's differential-line transfer, with only the explicitly constructed all-order SNC charts substituted. This transfer is credited antecedent machinery, not a separately proposed contribution.

Suppose that Y is not special. There are p>=1, a line bundle L, a nonzero i:L->Omega_Y^p and kappa(L)=p. The classical closed-form argument gives sections s_0,...,s_p of a common positive tensor power L^q with algebraically independent ratios u_a=s_a/s_0 and generic image line

    i(L)=span(du_1 wedge ... wedge du_p).                   (6.1)

Here is that argument: take a finite cover adjoining qth roots of these sections and resolve it. Their images are holomorphic p-forms on a smooth projective manifold and hence closed. Dividing by the first form shows d(u_a) wedge i(L)=0. Independent ratio differentials force p to be their maximal possible number by exterior algebra, and when there are p, their wedge spans the line. This also proves kappa(L)<=p for any nonzero line map to p-forms.

On a smooth general fibre F of g, the cotangent sequence filters Omega_Y^p|_F by bundles with trivial graded pieces, since both Omega_F^1 and the horizontal cotangent bundle are trivial. Choose F so i|_F and s_0|_F are nonzero. The first nonzero graded projection of i|_F, followed by a coordinate projection, gives a nonzero t in H^0(F,L^{-1}|_F). The product t^q s_0|_F is a nonzero holomorphic function on compact connected F, hence a nonzero constant. Therefore t and s_0 have no zeros on F, and each u_a is constant on F. Connected-fibre rational descent gives u_a=g^*v_a for v_a in C(X). The v_a remain algebraically independent, so p<=n and sigma=dv_1 wedge ... wedge dv_p is nonzero.

Write

    i^{tensor q}(s_a)=h_a (g^*sigma)^{tensor q}.             (6.2)

Over a smooth base open where sigma is holomorphic and nowhere zero, g^*sigma is nowhere zero on the entire inverse image. The h_a are holomorphic there, and compact connected fibres force them to descend to b_a in C(X). The ratios b_a/b_0 are v_a. Let K->Omega_R^p be the saturated root-chart meromorphic line spanned by the pullback of sigma. This is an orbifold line bundle: in each smooth factorial chart, clear denominators and divide the coefficient vector by its common height-one factors. A meromorphic multiple is holomorphic exactly when its scalar is holomorphic. The same statement holds for every tensor power, and the construction is equivariant and glues.

The tensors b_a sigma^{tensor q}, interpreted on root charts, pull back holomorphically by f, by (6.2). At every ordinary prime divisor and every boundary prime, Section 5 supplies a submersive local lift and hence a local analytic section. Pulling back by that section excludes poles in the original tensor at the general point of that root-chart divisor. All polar divisors have a base divisor as finite image. Thus all divisorial poles vanish; Hartogs extension across codimension at least two in the smooth charts makes the tensors holomorphic everywhere, including multiple-boundary intersections. They are sections of K^q by saturation. Their ratios give kappa(K)>=p.

Conversely f^*K has a nonzero differential map to Omega_Y^p, and pullback by this dominant map preserves independent section ratios. The preceding closed-form bound gives kappa(K)<=kappa(f^*K)<=p. Hence kappa(K)=p, contradicting specialness of R. This proves Y special.

## 7. The full group quotient, including exceptional meridians

Let Y^circ=Y minus g^{-1}(D) and X^circ=X minus D. Map pi_1(Y^circ) to pi_1(X^circ) and then to G. The inclusion Y^circ->Y is surjective on fundamental groups, with kernel normally generated by small meridians about every prime component of g^{-1}(D). This follows by perturbing loops and null-homotopy disks transversely to the smooth divisor strata and avoiding higher-codimension strata.

Consider a prime Q of g^{-1}(D), possibly exceptional and possibly mapping into an intersection of several D_i. Near a general point of its image, choose SNC local equations z_i for the passing D_i. On a small transverse disk to Q, each z_i pulled back has vanishing order a_i=ord_Q(g^*D_i), and all remaining base coordinates stay in a contractible neighbourhood. The image meridian in the local complement group is therefore product_i gamma_i^{a_i}; the local meridians commute. By (4.4), each a_i is divisible by m_i, so this local product dies in G. The same remains true after basepoint transport, which only conjugates it. Thus every killed meridian dies and we obtain pi_1(Y)->G.

This map is onto. Over the nonempty U from Section 4, g is proper smooth with connected fibre F. The homotopy exact sequence gives pi_1(g^{-1}U)->pi_1(U) onto. Removing further divisors from a smooth complex manifold does not obstruct representing loops, so pi_1(U)->pi_1(X^circ) is onto. Their composite is onto G and factors through pi_1(Y). No residual-finiteness or uniformization argument is involved.

Since Y is connected smooth projective and special, stipulated manifold abelianity makes pi_1(Y) virtually abelian. An epimorphic image of a finite-index abelian subgroup is finite-index abelian. Thus G is virtually abelian, proving OA057 with its original quantifiers.

## 8. Adversarial interfaces and scope controls

1. Root orders are arbitrary, including mixed and composite orders. The exact-M torsion point is essential: replacing it by torsion of a proper divisor would miss some nonzero powers of diagonal inertia.
2. The fixed-point-free criterion is equal nonzero coordinates, not arbitrary support size. The construction guarantees two such coordinates for any inertia element with a boundary component, even at all SNC intersections. It does not eliminate all auxiliary stabilizers.
3. Auxiliary divisors need not be irreducible on curves. The Kummer independence proof uses one unique component per auxiliary divisor; local SNC and inertia arguments use its label. This preserves n=1.
4. We descend root lines before resolution. Checking divisibility only on strict transforms would not control exceptional meridians mapping into D_i intersections.
5. Generic smoothness alone would leave some bad base divisor unchecked. Local fixed-point sections and proper resolution provide the missing ordinary submersions over every auxiliary prime.
6. The map Y->R is not claimed étale, finite, a manifold uniformization, or an isomorphism on fundamental groups. General fibre dimension may be large, explicitly M binom(s(n+1),2).
7. General fibres have trivial cotangent bundle because they are copies of the entire abelian variety F. A quotient fibre or a high-genus auxiliary fibre is not substituted.
8. Coefficient-one/logarithmic boundaries are outside the fixed target. Their known nonabelian nilpotent phenomena do not become assertions about this finite-root theorem.
9. The theorem asserts the full group, not just linear or finite images. It asserts virtual abelianity without a dimension-dependent rank or index bound.
10. Supporting finite algebra checks and any later Lean lemmas do not formalize Kummer normalization, quotient descent, resolution, differential specialness, or this full theorem.

## 9. Contribution boundary

The supplied fourfold/order-two paper already proves a general transfer criterion for its root type, auxiliary double-cover normalization, pairwise affine involutions on elliptic curves, scalar-normal blowup smoothing and the final manifold-group quotient argument. Changing fourfold dimension alone, taking more copies, or applying its stated conditional theorem would be technical. These operations are explicitly not claimed as new.

OA057 instead changes the inertia construction to cyclic permutations of arbitrary length on E^M, uses diagonal exact-M torsion to detect all finite boundary orders at once, and deliberately permits uncontrolled auxiliary stabilizers. The standard stabilizer-trivial line descent already appears in the supplied inertia foundations and is not claimed as new. Applying it before a general resolution preserves all exceptional divisibilities; local fixed-point sections give the divisorial submersions without scalar-normal quotient smoothing. The compatible package is proposed as the substantive all-order/SNC extension. Whether this exceeds a technical extension is a required independent contribution decision, not an author verdict. Exact primary proof comparisons and their limits are in reading-and-comparison.md.
