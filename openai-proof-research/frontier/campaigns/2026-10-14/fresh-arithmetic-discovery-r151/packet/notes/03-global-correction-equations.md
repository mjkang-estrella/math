# Prefreeze: global re-embedding and curvature correction

No theorem is frozen. These calculations specify the operation still unpaid after the source/primary reduction. They are not an author-proof nominee or a claim of novelty for deformation or connection algebra.

## 1. A correction in the fiber-bundle interface

First assume an actual proper holomorphic submersion f:X→Y of compact connected complex manifolds with a holomorphic complement H to V=T_X/Y. In the projective situation Höring Lemma 3.19 makes it an analytic fiber bundle with fixed compact fiber Z. Denote its principal Aut(Z)-bundle by G and its adjoint Lie algebra bundle by g=f_*V. Local trivializations identify g with O_Y⊗H0(Z,T_Z); changes of trivialization are the adjoint action. No such fiber-bundle or adjoint-bundle structure was inferred for every f in note02.

Write h:TY→f_*TX for the horizontal lift. Its curvature and induced connection are

    C(u,v)=[h(u),h(v)]−h([u,v]) ∈ g,
    ∇_u s=[h(u),s].                                    (7)

The brackets on the right are brackets of projectable fields on X. They give C∈H0(Y,Ω²Y⊗g). Jacobi gives, by expanding all three terms,

    (∇_u∇_v−∇_v∇_u−∇_[u,v])s=[C(u,v),s],
    d_∇ C=0.                                          (8)

All other holomorphic complements of V are obtained from a∈H0(Y,Ω¹Y⊗g) by h_a=h+a. This follows both from the affine space of splittings of the Atiyah sequence and directly from the projection formula for Hom(f*TY,V). Expanding the bracket gives

    C_a(u,v)=C(u,v)+∇_u(a(v))−∇_v(a(u))−a([u,v])
                     +[a(u),a(v)].                    (9)

With [a∧a](u,v)=2[a(u),a(v)], the exact equation is

    C+d_∇a+(1/2)[a∧a]=0.                               (10)

There is no complement determinant to check here: every graph over H remains complementary to the fixed V. Its abstract bundle is still f*TY≅H. Equation (10) is NECESSARY AND SUFFICIENT for the new horizontal distribution to be integrable.

It is not legitimate to regard C as an ordinary cohomology class and invoke a linear primitive: d_∇² is the adjoint action of C, so ∇ is not a flat differential unless the needed curvature condition is already satisfied. Nor do the Bianchi identity or vanishing real Chern classes produce a holomorphic solution a. A smooth solution would not suffice either: the replacement splitting must be holomorphic.

In a local trivialization h=d+A, equation (10) becomes

    d(A+a)+(1/2)[(A+a)∧(A+a)]=0.

Local flat trivialisations exist for the trivial product bundle, but their changes on overlaps need not preserve a globally chosen flat connection. The global holomorphic correction is the missing object, not the local formula.

For X=A×P1 from note02, write ω1,ω2 for the invariant forms dual to U,V and A0=Sω1+Tω2. Then dA0=0 and C=Sω1∧ω2. The correction a=−A0 gives C_a=0. Explicitly H_t=span(U+tS,V+tT) has curvature t²Sω1∧ω2 and H_0 is the standard horizontal tangent. Throughout t, the abstract horizontal bundle is O². This confirms that nonzero curvature of the GIVEN connection is not an obstruction to all replacements. It also checks the quadratic term and sign in (9); simply dropping it would give the wrong correction law.

## 2. Strongest available global payment

Müller's Lemma 4.1 supplies a solution indirectly when f is projective, Y is projective klt with c1(Y)=0, the fiber is normal projective with Pic0=0, and the relative tangent sequence splits. In the smooth setting the locally constant fibration gives H'≅f*TY; its difference from H is the a in (10). Thus those hypotheses do not leave an unpaid correction problem. Rationally connected fibers meet Pic0=0.

The construction retains the entire fiber, through a polarization and its homogeneous ideal. It cannot be replaced by the assertion that some associated vector bundle admits some flat connection. The ideal equations must be horizontal for the same tensor-compatible choices. Wang's actual Proposition 1.8 proof supplies that step using numerical flatness and the homogeneous ideal in Sym^m E_1. This is why the primary construction is stronger than solving isolated linear transport equations.

Biswas–Dumitrescu's Theorem 2.3 similarly pays replacement for a connected affine algebraic principal group over a compact Kähler Calabi–Yau base. One may apply it whenever the required principal-bundle reduction is actually supplied. No descent from a finite cover is assumed merely by averaging: (10) is nonlinear, and the quadratic bracket term need not survive an average. No conclusion for a general non-uniruled base, a general non-affine group, or an arbitrary singular quotient follows from this comparison.

Once a holomorphic replacement exists on all of compact Kähler X, V and H' are integrable. The Source052 universal-cover theorem applies with these specified new subbundles. In the fiber-bundle case the classical flat Ehresmann construction already gives the same product. Such a conclusion on the paid subclass is not a substitute nominee.

## 3. Two graph corrections for an arbitrary splitting

Return to T_X=E⊕F on a smooth compact connected X, with projectors P,Q. No fibration is assumed. Let

    α∈H0(X,Hom(E,F)),      β∈H0(X,Hom(F,E)),
    E_α={e+αe},           F_β={βf+f}.

Both graphs are holomorphic subbundles abstractly isomorphic to E,F. They are complementary exactly when

    det(I_E−βα)≠0.                                      (11)

Indeed the block map M(e,f)=(e+βf,αe+f) has determinant det(I_E−βα), equivalently det(I_F−αβ). This is a holomorphic function on compact connected X, hence constant, so nonvanishing at one point is enough.

Define

    K_E(α)(e,e')=(Q−αP)[e+αe,e'+αe'],
    K_F(β)(f,f')=(P−βQ)[βf+f,βf'+f'].                 (12)

The scalar-derivative terms in each bracket are multiples of a vector in its graph; the displayed projection kills them. Thus these are genuine holomorphic tensors in Hom(Λ²E,F) and Hom(Λ²F,E). They vanish if and only if the respective graph is integrable. In particular a complete solution in this graph chart consists of

    K_E(α)=0,  K_F(β)=0,  det(I_E−βα)≠0.                (13)

To display every nonlinear term, put B_E=P_F[e,e'] and B_F=P_E[f,f']. Then

 K_E(α)(e,e') = B_E(e,e')
   +Q([e,αe']+[αe,e'])−αP[e,e']
   +Q[αe,αe']−αP([e,αe']+[αe,e'])
   −αB_F(αe,αe').                                    (14)

The degrees in α are respectively 0,1,2,3. The last term disappears if F is integrable. The formula for K_F is obtained by interchanging E,F and P,Q. An assertion that the correction is always just a flat linear connection omits the last two lines in the general setting.

The spaces of global sections involved are finite dimensional on compact X. Choose bases. Equations (12) are polynomial maps of degree at most three between finite-dimensional complex vector spaces; (11) is one nonvanishing polynomial. Introducing an extra scalar t and requiring t det(I_E−βα)=1 expresses (13) as an algebraic existence problem. This is a characterization, not an algorithm that is known to find a point or a theorem guaranteeing a solution.

This graph chart does not contain every possible replacement. E' abstractly isomorphic to E might fail to be transverse to the ORIGINAL F. Therefore emptiness of (13) alone would not disprove the working question.

## 4. A global chart-free finite-dimensional formulation

Let n=dim X and A range over H0(X,End(T_X)). For each A form its globally defined adjugate adj(A), the polynomial endomorphism satisfying adj(A)A=(det A)I. Define, for i≠j,

    J_i(A)(u,v)=P_j adj(A)[Au,Av],   u,v∈E_i.          (15)

Here E_1=E and E_2=F. The expression is O_X-bilinear even for a singular A: every scalar-derivative error is a multiple of P_j adj(A)Au=(det A)P_j u=0. Thus J_i(A) is a global section of Hom(Λ²E_i,E_j). Its degree in the coefficients of A is at most n+1: the adjugate has degree n−1 and the bracket has degree two. Derivatives of the fixed holomorphic basis sections do not change that coefficient degree.

Since det A is constant on compact connected X, the exact full existence problem is

    J_1(A)=J_2(A)=0,        t det A=1.                 (16)

If (16) holds, A is a holomorphic bundle automorphism and adj(A)=(det A)A^−1, so (15) says precisely that A(E_i) is integrable. Conversely, any pair of complementary integrable subbundles abstractly isomorphic to E,F gives such an A by summing the two chosen bundle isomorphisms. Thus (16) covers ALL replacements of the same abstract summands on X, including those outside the graph chart. No integrability-preserving differential of a biholomorphism is required.

This reduction avoids changing the full working question when a graph chart fails. It pays the exact quantifiers, complementarity and abstract-bundle compatibility, but not nonemptiness of (16). The rational-fiber argument narrows the existing defect on the smooth locus; it does not manufacture the global coefficients of A satisfying (16).

## 5. Exact unpaid obligations and endpoint

For the general recovered question there is no constructed global holomorphic automorphism A solving (16). Even on the fiber-bundle interface, outside the hypotheses already covered by the primary results, there is no global a solving (10). In an MRC reduction one must additionally construct compatible quotients and embeddings across the excluded fibers; none of the calculations establishes a smooth global fibration, constant multiplicities, codimension-one extension, or preservation of complementary subbundles there. These are separate obligations, not proofs of impossibility.

An abstract universal-cover product with pulled-back bundle isomorphisms is weaker than re-embedding on X. No equivalence between those two global tasks is asserted. A lack of a solution to the stronger sufficient operation is not a counterexample to the weaker conjectural product statement.

The paid constructions include the full stipulated RC and integrable-Kähler headlines, ordinary deck bookkeeping, the RC-fiber bracket reduction, the exact deformation equations, and the primary Calabi–Yau replacement cases. No identifiable new full-scope bridge closes after integrating them. The endpoint is PREFREEZE/no nominee. No restricted or conditional theorem is submitted in place of the unfinished operation, and no exhaustion, impossibility, worldwide novelty, correctness grade, contribution grade, acceptance or count is claimed.
