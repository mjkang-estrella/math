# Rational Chow specialization: integrated reduction, not a nominee

PREFREEZE. No statement is frozen or submitted. This note records one sustained investigation of Source001's algebraic specialization of rational Hodge classes, with Source032 as a necessary companion. All pinned statements and operative proofs are stipulated true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The outcome is a source/primary composition, with no identified nonroutine operation. It is not an independent correctness or contribution verdict.

## 1. The operation explored and its precise coefficient scope

Fix Qbar inside C, a prime p, and a p-adic place w of Qbar. Write F=Fbar_p, K0=Frac W(F), and C_w for the completed algebraic closure at w, with the source's comparison embeddings. For an abelian variety A/Qbar with good reduction A0/F, put

    Hdg^r(A)=H^{2r}(A(C),Q(r)) ∩ H^{r,r}.

We investigate whether the source's existence of a cycle representing gamma in Hdg^r(A), for every 0≤r≤dim A, can be organized at the level of rational equivalence: a canonical representative in CH^r(A0)_Q, common to all realizations, respecting products, homomorphisms, correspondence composition, and cohomological idempotents on all finite products and powers. Dimension zero, r=0, r=dim A, and p=2 are included. Nothing integral, effective, degree-bounded, field-uniform over all primes, or on the original generic fiber is requested by this exploratory operation.

This is deliberately an investigation before freezing a new theorem. Its full rational form already follows from the strongest compatible operations below. Neither adding the word canonical nor retaining all correspondences creates a new mathematical primitive here.

## 2. What the actual pinned proofs already supply

Source001, `cor:cm-transport`, provides a CM abelian variety B/Qbar, a class kappa in Hdg^r(B), a positive n, and a quasi-isogeny a:A0^n→B0. With j the first-factor inclusion and b=aj, it proves

    gamma_(0,v)=b^* kappa_(0,v)

in every prime-to-p realization and crystalline cohomology extended to C_w. The relevant proof does not merely choose separate local scalar multiples: preservation of the untwisted polarization tensor gives a^*theta_(B,0)=lambda_v theta_*, and

    lambda_v=deg(a^*theta_(B,0) theta_*^(D−1))/deg(theta_*^D)
            =lambda in Q^×,   D=n dim A.

The trace tensor then scales by lambda^r. Dividing by lambda^r and the fixed trace-field degree gives one rational kappa for all realizations. The zero/top codimensions are supplied separately by unit/point classes.

Source032, `thm:cm`, algebraizes kappa on B_C. Its final assembly uses finite theta expansions on one common projective cover, rational CM-source maps, extraction of a nonzero mixed period, the surface criterion, and four-factor switch composition, then scalar descent on the original CM variety. Those operations are credited source operations. The source proof is not merely an abstract catalogue promise.

Source001, `cor:algebraic-specialization`, moves a finite cycle representative from C to Qbar on connected Hilbert components, descends it to a number field, specializes to a cycle Z0 on B0, and chooses N>0 so h=Nb is an actual homomorphism. It sets

    z_gamma=N^(−2r) h^* Z0 in CH^r(A0)_Q.                 (1)

Pullback here is the graph/refined-intersection pullback between smooth varieties. It needs neither flatness nor separability; p|N is allowed because all coefficients are rational and crystalline cohomology has inverted p. The SAME z_gamma realizes gamma_(0,ell) for every ell≠p and gamma_(0,p) after extension to C_w.

Source001 also gives uniqueness of the cohomological specialization inside a fixed good theory of rational Tate classes, `cor:all-hodge-specialization`. That is not yet uniqueness in the full rational Chow group. Source032, `cc:tate`, supplies full rational Tate for every finite-field abelian variety and numerical=ell-homological equivalence on its geometric rational algebraic cycles. Its proof explicitly uses Milne's implication with the corrected auxiliary-field convention, and averaging descends finite-field invariant classes. We use these stipulated conclusions, not an audit of the corrections.

## 3. The primary section is stronger than separately lifting projectors

Write N^*(X)=CH^*(X)_Q/num. O'Sullivan, *Algebraic cycles on an abelian variety*, arXiv:0908.0626v1 (5 August 2009), Theorems6.1.1/6.2.5 and Corollary6.2.6, gives a section

    s_X:N^*(X)→CH^*(X)_Q.                               (2)

Its image DCH^*(X) consists of the symmetrically distinguished classes. The coefficient field is characteristic zero; the base field may have positive characteristic. This distinction permits applying it at p=2. The theorem is stated more generally for abelian schemes over a nonempty connected separated regular excellent noetherian base of finite Krull dimension.

For a homogeneous cycle alpha, the definition uses every m and the spans V_m(alpha) of pushforwards of products of powers of alpha under signed-coordinate closed immersions X^n→X^m. Numerical projection must be injective on each V_m. This is not mere invariance under [−1], or Beauville weight zero, or verification on finitely many powers. The actual proof upgrades these spans to the generated Chow subtheory (Lemma6.2.4). It uses the even projector on h(X), the rank-one top exterior power of its positive summand, an injective tensor operation, and the contraction identity of Lemma6.2.3. The unique-lifting proof then compares the associated Poincare-duality theories using the Kimura splitting theorem and the unique lift of algebra maps with involution.

The important conclusion is that s is a morphism of Chow theories: it is Q-linear, multiplicative, and compatible with pullback and pushforward along every abelian-variety homomorphism. It respects external products and regular base change. The identity correspondence is distinguished because the diagonal is a homomorphism and its class is the pushforward of the unit. Accordingly the section lifts all algebraic relations simultaneously. Nilpotence can lift an individual numerical projector, but that weaker route is unnecessary; invoking it cannot make simultaneous projector compatibility an unpaid step.

The proof's category and representation-theory foundations are not claimed all freshly read. Actual main proofs and selected internal antecedents were read; the exact extent is recorded in READING.md.

## 4. Retaining the crystalline class

It would be incomplete to replace z_gamma by s([z_gamma]) and only invoke numerical=ell-homological equivalence. That proves the ell-adic equalities but does not, by itself, prove the crystalline equality. The following standard finite-field dimension argument pays the missing compatibility.

Let X/F be an abelian variety of dimension g and fix r. Set n=dim_Q N^r(X). Source032's full Tate and equivalence statement make this finite and identify it with the dimension of the geometric ell-adic Tate space for any ell≠p. Choose a rational numerical basis represented by z_1,...,z_n and complementary rational cycles y_1,...,y_n such that

    M_ij=deg(z_i y_j),   det M≠0.                       (3)

Such dual test cycles exist from the definition of numerical equivalence and finite dimensionality. Descend X and these finitely many cycles to F_q. Enlarge F_q so all Frobenius eigenvalues in H^{2r}_ell whose quotient by q^r is a root of unity become q^r, and so the chosen cycles descend. There are only finitely many eigenvalues, so this can be done. Frobenius on an abelian variety's ell-adic cohomology is semisimple: on H^1 its action comes from a central element of the semisimple isogeny endomorphism algebra over F_q, whose center is a product of number fields, and higher cohomology is its exterior algebra. This argument concerns Frobenius over its field of definition, where it is central.

Consequently n is the algebraic multiplicity of q^r in its degree2r characteristic polynomial. Katz–Messing, *Some consequences of the Riemann hypothesis for varieties over finite fields*, Invent.Math.23 (1974), Theorem1, identifies this polynomial with the crystalline polynomial. Their actual proof uses weak Lefschetz, induction on dimension, the cohomological zeta formula and the distinct absolute values of the three remaining weights. It applies to crystalline cohomology after inverting p.

For a rational cycle z on X, enlarge the same finite field further so z descends. The root-of-unity stabilization remains true after this extension. Let F_q^* denote the LINEAR q-power Frobenius on H_cris^{2r}(X/F_q)[1/p], over Frac W(F_q); this is an iterate of the semilinear p-Frobenius. Both cl_cris(z) and cl_cris(z_i) lie in its q^r-eigenspace V. Therefore

    dim V ≤ multiplicity(q^r)=n.                        (4)

The n classes cl_cris(z_i) are linearly independent: pairing any proposed relation with cl_cris(y_j) gives the same invertible rational matrix M. Hence they are a basis of V. If z is numerically zero, write cl_cris(z)=Σ_i c_i cl_cris(z_i). Pairing with every y_j gives M^t c=0, so c=0. Thus numerical triviality implies crystalline triviality. The reverse implication follows directly from cycle products and traces. Base extension to K0 and then C_w preserves these equalities.

This proof does not assume semisimplicity of crystalline Frobenius, does not identify an F-isocrystal with a vector space of arbitrary coefficients without iteration, and does not infer integral cycle saturation. It is a dimension squeeze on RATIONAL cycle classes. Milne's actual primary §7.4 uses a related semisimple dimension comparison to prove numerical=ell-homological; Remark7.6(c) expressly credits the crystalline analogue under the same CM-Hodge hypothesis. Thus even this last compatibility is already anticipated by the primary, not a new discovery claim.

If n=0, (4) gives V=0 directly. All arguments work for every codimension and every finite product of abelian varieties. Nothing compares integral lattices across varying primes.

## 5. The integrated rational assignment

Define

    S_w,A(gamma)=s_A0([z_gamma]_num).                    (5)

This does not depend on the choice in (1): two representatives with the same ell-adic class have numerically equal difference, since a zero cohomology class has zero intersection with every complementary cycle. By (2), the distinguished representative of that numerical class is unique. By Source032 and §4, it has exactly the SAME classes as z_gamma in every ell-adic realization and in crystalline cohomology. Canonicity is relative to the fixed place, good-reduction identifications and zero sections; it is not uniqueness among all Chow representatives.

Additivity, Q-linearity and multiplicativity can be checked first in one ell-adic realization. For example z_gamma z_eta represents the specialization of gamma eta, so

    [z_(gamma eta)]_num=[z_gamma z_eta]_num.

Applying the multiplicative section proves S(gamma eta)=S(gamma)S(eta) in CH, with no correction terms. The unit is preserved. Homomorphism pullback and pushforward commute with specialization of absolute Hodge classes and with s. External products are products of projection pullbacks, so are also preserved. A homomorphism of good-reduction abelian varieties extends over a suitable common abelian-scheme model; all statements refer to those good reductions. Boundary codimensions outside the geometric range have zero groups.

The assignment is injective on rational Hodge classes: if S(gamma)=0, its ell-adic specialization is zero, smooth proper comparison returns the zero generic ell-adic realization, and Betti comparison after Q→Q_ell gives gamma=0. No claim of surjectivity onto DCH is made; a reduction can have additional algebraic classes and endomorphisms.

## 6. Correspondences and all relation compatibility

Use the correspondence convention

    Corr^d(A,B)=Hdg^{a+d}(A×B),   a=dim A.

For alpha∈Corr^d(A,B), beta∈Corr^e(B,C), define

    beta∘alpha=(p_13)_*(p_12^*alpha · p_23^*beta).

The projections are homomorphisms of abelian varieties and the codimension on A×C is a+d+e. Applying §5 and the Chow-theory section gives the same identity IN RATIONAL CHOW GROUPS:

    S(beta∘alpha)=S(beta)∘S(alpha).                      (6)

The diagonal supplies the identity. Factor permutations, external products, evaluation and coevaluation are preserved. When describing this via H^1 tensors, geometric permutations carry the usual Koszul signs on odd-degree factors; there is no replacement by unsigned permutations. Equation(6) is written directly with geometric correspondences and avoids that ambiguity.

If e_i are any finite set of orthogonal Hodge projectors with Σe_i=Delta, their images satisfy all these equations exactly. More generally any rational polynomial relation under additions, scalar multiplication, tensor products and defined compositions is retained, including noncommutative algebra actions. This is not limited to semisimple endomorphism subalgebras or to a chosen finite presentation. The section works on all products, so no missing all-arity extrapolation remains. Passing to sums, Tate twists and images of idempotents gives the corresponding functor on the pseudo-abelian correspondence category. This is a faithful tensor construction; it is not asserted full into all special-fiber Chow motives.

Thus jointly lifting projectors, choosing compatible matrix units, or preserving noncommuting correspondence relations is NOT a residual after the strongest primary operation. A failure of ad hoc separately chosen cycles would not obstruct (5)–(6).

## 7. Two additional compatible operations also already paid

First, suppose a particular specialized Hodge class is invariant under Gal(F/F_q). The numerical class in (5) is invariant. Base-change functoriality and uniqueness make its distinguished Chow class invariant as well. Choose a representative defined over F_(q^m); push it to F_q and divide by m. After base change this is the average of its m conjugates, which all have the same Chow class. It therefore descends the distinguished class to F_q with rational coefficients. Division by m is allowed even when p|m. This does not assert integral descent or a single field of definition for arbitrary classes before their invariance is given.

Second, if a generic algebraic cycle alpha is already symmetrically distinguished, ordinary specialization preserves that property. After finite descent work over an excellent DVR R with abelian scheme A/R. Choose any closure alpha_tilde of alpha. Apply the RELATIVE O'Sullivan section to its relative numerical class, obtaining beta. Its generic restriction is distinguished and has the same generic numerical class as alpha, hence equals alpha in CH of the generic fiber by uniqueness. Its closed-fiber restriction is distinguished by the primary base-change result. Compatibility of refined specialization gives

    sp(alpha)=beta_s,

so sp(alpha) is the distinguished representative of its numerical specialization. This justifies simultaneous specialization for actual generic distinguished cycles, not for an arbitrary hypothetical generic Hodge cycle. Relative numerical equivalence is stable under these base changes; the proof in the primary uses preservation of intersection scalars on the connected regular base.

This argument is stronger than independently rechoosing a section at each place. It still does not construct a generic algebraic representative for an arbitrary gamma in Hdg(A). On a CM generic fiber that representative is already supplied by Source032; on an arbitrary generic fiber Source001 only supplies special-fiber algebraicity. No reversal of specialization is used.

## 8. Boundary and outcome

The rational Chow-level operation examined here closes by the compatible composition (1)–(6), including crystalline realization, all projectors, all arities, rational Galois descent when invariant, and ordinary specialization for existing distinguished generic cycles. There is no residual coherence defect being left unpaid and renamed as a conjecture. Nor is the established primary section being nominated as a new supporting theorem.

What remains absent is an identified NONROUTINE full-scope operation beyond this composition. The present round has not supplied one. A generic Chow lift of arbitrary Hodge classes would require generic algebraicity not supplied here; this is a boundary, not a new target or a claim about present worldwide open status. Uniform integral denominators would reopen r58's existing T001U58 rather than constitute a distinct target. Its exact all-good-places, all-geometric-places, all-lattice-classes quantifiers remain unchanged. No integral conclusion follows from the rational section or the crystalline dimension argument.

The r58 archive already analyzes the numerical/integral distinction and the finite-family route back to generic algebraicity. The old Mumford construction history concerns cohomological spans conditional on generic algebraicity, explicitly not Chow idempotents; nothing here closes its missing generic algebraicity. r96's bounded Source001 screen mentioned abelian-motive/bad-reduction boundaries. None of these old scopes or dispositions is regraded or weakened.

No full author-proof nominee, supporting nominee, theorem freeze, independent correctness/contribution grade, acceptance or count is submitted. H138/T185R144 and all other named old full/technical/failed scopes retain their existing dispositions. No exhaustion, priority, current-open or impossibility claim is made. The reading/capture omissions and deviations remain material limitations, not mathematical certificates.
