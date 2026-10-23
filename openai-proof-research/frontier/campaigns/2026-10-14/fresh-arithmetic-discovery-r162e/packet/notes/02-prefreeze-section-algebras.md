# Arithmetic162e: full section algebras and specialization

This is a prefreeze feasibility calculation. No theorem is frozen or nominated. It tests the entire all-degree operation formulated in note 01 and records why it fails, together with the stronger classical reduction that explains the failure. It is not an upstream counterexample. All upstream assertions remain stipulated true.

## 1. A prescribed family and its metrics

Fix a complex elliptic curve E with origin and a nonzero holomorphic differential eta. Set B=Pic^0(E), and let P be the normalized Poincaré line on E×B. Denote the projections by q:E×B->B and p:E×B->E. Let

    V = O_(E×B) ⊕ P,
    pi:X=P_(E×B)(V)->E×B,
    f=q pi:X->B.

Use the quotient projectivization convention: pi_*O_X(k)=Sym^k V for k>=0. The total space X and base B are smooth projective; f is smooth projective with connected fibres of dimension two. For t∈B, write P_t=P|_(E×{t}) and X_t=P_E(O_E⊕P_t).

The relative Euler sequence and K_E=O_E, trivialized by eta, give an identity of actual lines

    L=-K_(X/B)=O_X(2)⊗pi^*P^(-1).

Each degree-zero line P_t is unitary flat. One direct analytic reason is that a Hermitian metric can have its curvature killed by solving the Laplace equation on E, whose solvability obstruction is precisely the degree. Its Chern connection is then unitary flat. In unitary flat charts of O⊕P_t, the ordinary Fubini–Study metric on O(1) is invariant under transition functions. It has positive vertical curvature and zero horizontal curvature. Tensor its square with the flat determinant inverse and the fixed base canonical frame. The resulting metric on L_t=-K_(X_t) is smooth and semipositive, of curvature rank one everywhere. Thus every fibre satisfies the actual metric hypothesis of Source068, not merely nefness.

No globally semipositive metric on L over the entire threefold X is asserted. The tested premise is fibrewise smooth semipositivity; a strengthened premise imposing total-space positivity would be a different problem. Projectivity here is immediate from the algebraic projective bundle, rather than inferred from arbitrary suspension representations.

This construction is the ruled case explicitly treated by Chen–Filip–Sun–Tosatti–Zhang. The relative use of the normalized Picard family supplies prescribed parameters; it is not a request for connections or their holomorphic transport.

## 2. Every graded piece and every product on a fibre

For m>=0, projective-bundle pushforward has no higher direct images and gives

    pi_*L^m = Sym^(2m)(O⊕P)⊗P^(-m)
             = direct_sum_(k=-m)^m P^k.                         (2.1)

There are no binomial multiplicities: the two summands have rank one, and each monomial is one line summand. If a degree-zero line Q on E has a nonzero section, its effective divisor has degree zero and is empty, so Q is trivial. Consequently

    h0(E,Q)=h1(E,Q)=1 if Q=O_E,
    h0(E,Q)=h1(E,Q)=0 otherwise.                              (2.2)

The H1 assertion follows from Serre duality with K_E=O_E. Leray for pi gives H2(X_t,L_t^m)=0 and equality of H0 and H1 dimensions.

If P_t is nontorsion, only k=0 contributes to (2.1). If its exact order is N>=1, exactly the multiples of N in [-m,m] contribute. Hence, including m=0,

    h0(X_t,L_t^m)=h1(X_t,L_t^m)=
       1                         when P_t is nontorsion,
       2 floor(m/N)+1            when ord(P_t)=N.             (2.3)

The natural determinant shift -m in (2.1) is essential. Omitting it would compute a different linearized line and a different invariant ring.

Let R_t=direct_sum_(m>=0) H0(X_t,L_t^m). Locally write x,y for the degree-one symbols of O and P before the determinant twist. The balanced monomial xy, together with the inverse determinant and eta frame, defines a global anticanonical section a. It is also obtained from the infinitesimal vertical scaling field wedged with the base tangent direction; changing a lift of that direction adds a vertical vector and does not change the wedge. Thus a is canonical up to the chosen nonzero eta and a scalar. Its divisor is the sum of the two disjoint distinguished sections of X_t->E.

For nontorsion P_t, all sections are powers of a and

    R_t ≅ C[a],                 deg a=1.                      (2.4)

For P_t of order N, choose a trivialization of P_t^N and its inverse compatibly. The unbalanced monomials x^(2N) and y^(2N), with the determinant factors, give b,c of anticanonical degree N. Then

    R_t ≅ C[a,b,c]/(bc-a^(2N)),
    deg a=1, deg b=deg c=N.                                   (2.5)

Here is the full multiplicative argument. A monomial of degree m whose exponent k=j-m equals lN>=0 factors as a^(m-lN)c^l, and the case k=-lN factors as a^(m-lN)b^l. Every contributing monomial therefore lies in the indicated algebra. The displayed relation follows from multiplying the compatible trivializations. Modulo it, every polynomial is a sum of a-powers, a^r b^s and a^r c^s with s>0. In each fixed degree these normal monomials have distinct signed k values and are linearly independent in (2.1). There can be no further relation. This proves the entire ring presentation, not just its Hilbert function.

Both b and c are necessary in degree N: all lower positive-degree pieces are generated by a. For example N=5 gives h0=1 in degrees 1 through 4, h0=3 in degree 5 and h0=5 in degree 10. This is an elementary check of the formula, not a computational gate.

## 3. The actual relative algebra loses the torsion sections

For every nonzero integer k,

    q_*P^k=0.                                                 (3.1)

Indeed multiplication by k on B is nonconstant, and P_t^k is nontrivial away from the finite subgroup B[k]. Over any nonempty open in B a section of P^k would vanish on all those general fibres, hence on a dense subset of E times that open, and consequently everywhere. This proves sheaf vanishing, including at the exceptional parameters; it does not assert fibrewise H0 vanishing there. On the other hand q_*O=O_B.

Combining (2.1) and (3.1), for every m>=0

    f_*L^m=O_B a^m,
    direct_sum_(m>=0) f_*L^m=O_B[a].                          (3.2)

The multiplication in this relative algebra is already finite and completely known. At a point of order N, its degree-m base-change map is

    C a^m -> H0(X_t,L_t^m),                                  (3.3)

with image exactly the balanced line. It is an isomorphism for m<N and has cokernel dimension 2 floor(m/N) for m>=N. In particular local freeness of every f_*L^m does NOT imply that its formation commutes with every specialization.

The stable section a is nonzero on every fibre, and supplies nonvanishing in the same degree one everywhere in the family. The failure is therefore not the absence of a uniform nonvanishing degree. It concerns completeness of the section system and preservation of products and extra sections under specialization. Neither a dimension-only nonvanishing-index obstruction nor a counterexample to the source's invariant construction is claimed.

## 4. Fixed Veronese, finite covers, and finite strata

Fix ANY d>0. The d-th Veronese of (3.2) is O_B[a^d]. At a torsion parameter of order N, its degree-m base-change map fails as soon as dm>=N. Its deficiency is 2 floor(dm/N). There are torsion parameters of arbitrarily large order in B. Thus no choice of d repairs (3.3) simultaneously for all parameters and all degrees.

Let g:B'->B be ANY nonempty finite étale surjective cover. Each connected component maps onto B. Its flat pullback commutes with f_*L^m; equivalently the direct argument for (3.1) still works because [k]g is nonconstant. Thus after this parameter change the relative algebra is O_(B')[a], while its fibres above the same torsion points still have (2.5). No finite étale parameter cover repairs the tested statement. The argument is about a cover of the PARAMETER space. A separate isogeny of E killing one particular torsion P_t changes an individual fibre presentation and depends on N; it is not a simultaneous parameter cover that solves this problem.

Twisting degree one by a base line cannot repair the failure either: projection formula tensors both sides of each map by a one-dimensional fibre, leaving its rank and deficiency unchanged.

A finite algebraic stratification of B cannot make all graded fibre dimensions locally constant. At least one locally closed stratum is dense and contains a nonempty Zariski open U. The complement of U on this projective smooth curve is finite. The open U contains a nontorsion point and a point of exact torsion order N. Taking m>=ceil(N/d) distinguishes their degree-m dimensions for the chosen Veronese. Hence there is no finite stratification controlling every degree. This also works on B' by surjectivity. Finite-degree truncations are different: up to original degree M, only the finite union of B[k], 1<=k<=M, is relevant. Thus finite-degree cohomology-and-base-change theory is respected.

Even disregarding relative pushforward, the generator degrees of all fibre d-Veronese algebras have no common finite bound. Put r=ceil(N/d). Every Veronese degree below r has only a^(dm), while degree r has an off-balanced monomial a^(dr-N)b (and its c counterpart). It cannot be generated from smaller positive degrees, whose products are balanced. Therefore a generator in Veronese degree at least ceil(N/d) is necessary. As N grows this lower bound is unbounded for every fixed d. This argument is intrinsic to the graded pieces; choosing different generators cannot remove the bound.

## 5. The cohomological repair is already classical

After note 01, and before this note, Mukai's published 1981 Section 2 was read for the exact Poincaré transform and its weak-index versus index distinction; page 156 was rendered to recover formulas missing from extracted text. Stacks Project Section 30.22 was also read in full for its finite-perfect-complex and arbitrary derived base-change proof. These are late primary reads, not retroactively claimed in note 01.

The relevant stronger classical identity for the normalized Poincaré bundle on the elliptic curve is

    Rq_*P ≅ C_0[-1].                                         (5.1)

Mukai's Theorem 2.2 proof explicitly uses the corresponding g-dimensional identity and attributes it to Mumford, Abelian Varieties, Section 13. That antecedent book was not newly read here. We can also see the elliptic mechanism directly: near the origin of B, a finite free cohomology complex can be reduced by cancelling invertible blocks to [O --u(t)--> O] in degrees 0 and 1. The first-order deformation of O_E supplied by the Poincaré family is the identity tangent class in H1(E,O_E). The obstruction to extending the section 1 is this nonzero class. Thus u'(0) is nonzero, so u is a parameter times a unit; the complex has H0=0 and H1=C_0. Away from the origin all cohomology vanishes by (2.2). This explains the simple, rather than thickened, support in (5.1).

For k!=0, normalization of P gives P^k=(id_E×[k])^*P. Multiplication [k] on B is finite étale, so flat base change in (5.1) gives

    Rq_*P^k ≅ O_(B[k])[-1].                                  (5.2)

The isomorphism may depend on scalar choices, which do not affect any dimensions or support assertions. The k=0 summand instead has R0q_*O=O_B and R1q_*O=H1(E,O_E)⊗O_B. Hence the complete sheaf-level information in degree m is

    R0 f_*L^m = O_B,
    R1 f_*L^m ≅ O_B ⊕ direct_sum_(0<|k|<=m) O_(B[k]),
    Ri f_*L^m = 0 for i>=2,                                  (5.3)

where a basis of H1(E,O_E) has been chosen to write the free summand as O_B. The direct decomposition by k comes from (2.1); it is not an assertion of a canonical splitting of a multiplicative derived algebra.

At t of exact order N, precisely 2 floor(m/N) of the torsion summands of (5.3) contain t. Over the regular local ring A=O_(B,t), the free perfect complex therefore has the base-change exact sequence

    0 -> (f_*L^m)⊗C_t -> H0(X_t,L_t^m)
      -> Tor_1^A((R1 f_*L^m)_t,C_t) -> 0.                   (5.4)

This also follows directly from tensoring the two-term models. Each reduced skyscraper contributes one Tor dimension. Thus (5.4) recovers exactly the deficiency in (3.3), in every m, and (5.3)⊗C_t recovers the equal H1 jump. The Euler characteristic stays zero throughout, including m=0. The invariant-index polynomial cannot distinguish these equal H0/H1 jumps. For the natural fibre-scaling torus, the balanced weight has H0=H1=1 and all additional torsion sections have nonzero torus weights; the invariant index is zero as well.

There is no missing general derived base-change theorem here: it is classical and applies to each L^m because f is proper and L^m is flat over B. Cup products also exist functorially before taking H0. Merely renaming this as a derived relative nonvanishing theorem would not give a new operation. Nor does (5.3) alone supply a new finite presentation of the whole multiplicative derived object: the support union grows through all torsion subgroups with m. The ordinary all-section specialization target has already been disproved, not left hanging on that presentation question.

## 6. Compatibility with the strongest Source068 reductions

The compact-monodromy description is explicit here: for each t, X_t is the quotient of C×P1 by the elliptic lattice acting through the unitary character of P_t on P1. For nontorsion P_t its closure is a circle; for order N it is the finite cyclic group mu_N. Global anticanonical sections are exactly its fixed monomials, as in Müller's actual unitary construction. Passing to connected closure after an individual finite index changes the lattice by an index that can depend on N. Consequently that source step cannot be silently promoted to a uniform parameter construction.

Averaging over the full fixed circle always selects C[a]. It agrees with the actual relative algebra, but at torsion parameters the actual monodromy group is smaller and has extra fixed monomials. This is a change of the group whose invariants are wanted, not a failure of exactness of invariants for one fixed reductive group. The r12 finite quotient descent operation also requires a fixed action and preserves precisely its invariant sections; it cannot supply the missing torsion eigensections in (3.3).

The endpoint and correction-ring theorems already attain zero valuation on each fixed curvature-null construction; their generator selection cannot be reinterpreted as a common finite generator list as t varies. In the present example every fibre ring is finitely generated, and the relative ring itself is finitely generated, yet both a uniform fibre-generator bound and simultaneous complete specialization fail. Thus even strengthening a naive attempt by granting pointwise finite generation does not close its interface.

An optional geometric view of the null field is consistent with that calculation. For the rank-one Fubini–Study curvature, an effective curve with zero intersection with L is tangent to the horizontal flat foliation at its general point: integrating the nonnegative curvature on its normalization forces its restriction to vanish. If it dominates E, its intersection with a generic P1 fibre is a finite orbit of the character group. Nontorsion monodromy has only the two fixed-point orbits, so null polar divisors are supported on the two distinguished sections. A rational function with poles there is constant: the spaces H0(O(rD0+sDinf)) are one-dimensional, by the same split-bundle monomial computation with the associated determinant twist. Thus the null-polar field is C. For order N, the invariant fibre rational coordinate z^N defines a morphism to P1 whose general fibre is a connected étale elliptic cover; it is a compact horizontal leaf. Every null curve is such a leaf, and a function with only null poles is constant on the general elliptic leaf. The null-polar field is C(z^N). The source's point-base versus positive-base alternatives can therefore themselves jump in this family. This is explanatory geometry of the already computed classical example, not a new source extension.

## 7. Research outcome and precise remaining scope

The full tested positive assertion is false already for this smooth projective surface family with fibrewise smooth semipositivity, common degree-one nonvanishing, and completely known finitely generated fibre rings. Fixed Veronese, finite étale parameter change, base-line twisting, finite stratification and pointwise finite generation do not repair it in their stated all-degree scopes. These are resolved feasibility failures, not conjectures declared impossible in general.

The calculation is a classical composition of the ruled symmetric-power formula, character invariants, Picard torsion and ordinary/derived base change. It is not offered as a substantial nominee. The actual unresolved discovery objective is a DIFFERENT full-scope operation exceeding these paid constructions. For this family, preserving all special sections requires accepting the torsion/Tor data or allowing infinitely many all-degree parameter distinctions; the ordinary uniform operation above cannot provide it. No new positive bridge is claimed, no restriction of an older frozen target is offered, and no global exhaustion or worldwide-priority conclusion follows.
