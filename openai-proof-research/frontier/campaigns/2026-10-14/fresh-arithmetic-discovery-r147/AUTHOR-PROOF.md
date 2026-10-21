# Author proof at the frozen r147 scope

The statement is exactly THEOREM.md, SHA256 aa34714980af05fbbed5ae223b73b8ec10c1b19d8865ff61fbf2615f582682a8. This is an author-proof submission for the parent's independent correctness and contribution reviews, not either review. The source and all operative proofs at the specified immutable pin are stipulated true. No downstream manuscript, formalization or release is prepared.

## 1. Exact source input and fixed data

Write k0=Qbar. On Sigma=P1×P1 use F=O(1,0), S=O(0,1). We use the actual Source048 wrapper paper.tex and its six sections, not the catalogue headline. The operative labels are curve:six-vectors, curve:adjoint-jets, prop:curve-data, trace:pairing, trace:principal-parts, prop:residue-data, prop:jets, analytic:actual-lifting, prop:analytic-counterexample, analytic:invariants, algebra:finite-determinacy and prop:algebraization.

Fix a smooth elliptic curve over k0, a degree-two line bundle F on it, and an exact order-four class D0. The two degree-two pencils F and F+D0 embed it as Gamma⊂Sigma of bidegree(2,2). Put Delta=2D0, Phi=F+Delta and M=3Phi. Source048 chooses six distinct points Z on Gamma, a section beta of M vanishing simply at Z, and six nonzero vectors in a two-dimensional quadratic space with

    w=sum w_j,  w²=90,  w_j²+w_j·w=1.

All these data may be chosen over k0. Indeed the source's formula uses h=sqrt(90), R=sqrt(1+h²/4), the roots of X³−bX²+b lambda X−lambda with b=2h/R, and a nonzero scalar isometry. The nondegeneracy, distinctness, and avoidance requirements exclude a proper algebraic subset. Choose algebraic lambda sufficiently small and general as in its actual proof, then an algebraic isometry avoiding the finite prohibited directions. Division points, the six preimages under the degree-two Phi pencil, and beta are algebraic. Fix the compatible bundle isomorphisms and volume scalar over k0. In particular Gamma→P1 via F is unramified at Z.

Choose kappa0 lifting beta⁴ to H0(Sigma,O(8,4)); such a lift exists over k0 by the restriction sequence and H1(O(6,2))=0. Write gamma for the section defining Gamma, and set

    W=kappa0+gamma H0(Sigma,O(6,2)).                         (1.1)

This is an affine 21-space: h0(O(6,2))=7·3=21, and multiplication by gamma is injective. There is no projective scaling quotient here, since every member restricts to the same nonzero beta⁴ on Gamma. If two members define the same divisor on Sigma, their defining sections differ by a scalar, which must be one upon restriction to Gamma.

On a nonempty open W_sm the curves C_v=V(kappa_v) are smooth, connected, of bidegree(8,4), and have exactly fourth-order contact with Gamma at Z. This is precisely the source's Bertini/normal-derivative argument, valid for the entire affine system (1.1). Define on this family

    H_v=F|C_v,   S_v=S|C_v,   L_v=H_v+Z.

The source's contact and evaluation computations apply to every member of W_sm. They give

    g=21, deg H=4, deg S=8, deg L=10,
    K=6H+2S=4L, h0(H)=2, h0(L−H)=h0(O_C(Z))=1.             (1.2)

Also h0(S_v)=2. This last assertion follows directly from

    0→O_Sigma(−8,−3)→O_Sigma(0,1)→O_C(S_v)→0,

since H0 and H1 of the left term vanish by product cohomology. All line bundles and the contact divisor are algebraic relative objects over W_sm.

The residue mechanism is not replaced by arbitrary free choices: the trace quotient is W_tr=H0(C,2L+H)/xi²H0(C,3H), with trace splitting (3,0,0,−3). Its full double-principal-part comparison with H0(Gamma,Phi), including the negative adjunction scalar, identifies the six quadratic vectors with c_j l_j. The global meromorphic row P then satisfies p_j(0) wedge R_j(0)=1 and sum(W_j−1)=−9 deg L. These are the actual low-order solvability equations. Their solutions exist separately for each C_v by the stipulated proofs; no relative analytic choice of P, flows, or lifting is assumed below.

## 2. A nonempty primitive tetragonal open

We prove that W_sm contains a nonempty open W_pr on which the first projection C_v→P1 is simply branched, hence primitive. This verifies an additional input; primitivity is not inferred from the degree alone.

Let T⊂P1 be the finite set consisting of the branch values of Gamma→P1 and the images of Z. At a base point x outside T, the fiber line F_x meets Gamma at two distinct points a,b, and kappa restricted to F_x is a binary quartic whose values at a,b are fixed and nonzero. Conversely every quartic with these two values occurs: restriction of H0(O(6,2)) to F_x is all H0(P1,O(2)), and multiplication by gamma|F_x identifies this three-dimensional space with the kernel of the two evaluation maps on quartics.

First consider a ramification point of order at least three, lying outside Gamma. In local coordinates x,y with x the first projection, it satisfies

    kappa=kappa_y=kappa_yy=0.                               (2.1)

Variations gamma h with h∈H0(O(6,2)) give arbitrary vertical two-jets there. On a fixed fiber, degree-two polynomials give arbitrary jets of length three; multiplication by the unit gamma preserves this property. Thus (2.1) imposes three independent affine linear conditions at each point. The point varies in a surface, so the incidence has dimension at most 21+2−3=20. Its image in W has closure of dimension at most20. This argument works in homogeneous coordinate charts and includes potential ramification at infinity.

Next consider two distinct ramification points over the same x outside T. A quartic with both points double has the form c l_u² l_v² with u≠v. Since its values at a,b are prescribed nonzero, u,v avoid a,b. The two value conditions determine c and impose

    ((a−u)(a−v)/((b−u)(b−v)))² = A/B                       (2.2)

in any affine coordinate avoiding a,b,u,v, with the evident homogeneous form in other charts. The ratio on the left is nonconstant on the two-dimensional space of unordered pairs {u,v}. Therefore (2.2) cuts a subset of dimension at most one. Hence the double-double locus has dimension at most1 inside the affine three-space of quartics with the prescribed two values. Restriction from W is surjective with 18-dimensional fibers, so the incidence over all x outside T has dimension at most18+1+1=20. Again its image has proper closure in W. The zero quartic cannot occur, because the prescribed values are nonzero.

Finally require the quartic on each of the finitely many fibers x∈T to be squarefree. Each is a nonempty open condition on W. To see nonemptiness, if Gamma meets that fiber at distinct a,b, a prescribed zero value merely forces a simple root which can be made simple by varying h(a) or h(b); any remaining roots can be made distinct. If both prescribed values vanish, the affine system on that fiber is gamma times an arbitrary quadratic, and a general quadratic has distinct roots away from a,b. If Gamma is tangent to the fiber at a, then a∉Z, so the prescribed value at a is nonzero; the prescribed length-two jet imposes no multiple root elsewhere, and a general quartic in that affine three-space is squarefree. More explicitly, for y≠a the equations kappa(y)=kappa_y(y)=0 impose two independent conditions on h∈H0(O(2)); the incidence over y has dimension at most2, less than3. Thus such a member exists. Surjectivity of restriction from W gives nonempty opens upstairs. No simultaneous interpolation in the x-direction is required: finitely many nonempty opens in the irreducible W meet.

Intersect these conditions with W_sm and the complements of the two dimension-at-most20 images. The result W_pr is a nonempty open, defined over k0. Every degree-four projection on W_pr has only simple ramification and distinct branch values. For complex members its monodromy is generated by transpositions. Connectedness of C makes the permutation action transitive; a transitive subgroup generated by transpositions is S4, as the graph whose edges are these transpositions is connected. Thus the degree-four covering is primitive. This also proves geometric primitivity for the generic member by embedding k0(W) into C. The same conclusion holds for all geometric fibers of W_pr; alternatively the excluded incidence loci describe the simply branched locus algebraically, and any putative intermediate covering descends to a finitely generated characteristic-zero field and then embeds into C.

## 3. Forgetting every marking still leaves finite fibers

Fix a complex abstract curve C represented by a point of W_pr. Its degree-four pencil H is unique up to an automorphism of P1. Indeed, given a second degree-four morphism, take the normalization D of the image of C in P1×P1, and let e=[C:D]. The integer e divides4. If e=1, the image has bidegree(4,4), arithmetic genus(4−1)(4−1)=9, and its normalization has genus at most9, contradicting g(C)=21. If e=2, the original degree-four map has a nontrivial intermediate curve, contradicting primitivity. If e=4, both projections D→P1 have degree1, so the two maps differ by a target automorphism. These are all possibilities. Because h0(H)=2, the underlying line bundle and its complete pencil are determined.

Now consider every v∈W_pr(C) for which C_v is abstractly isomorphic to C, and choose an isomorphism alpha:C→C_v. We count possible embeddings C→Sigma, which bounds the number of distinct images C_v.

The pullback alpha*H_v must be H. The pullback alpha*L_v is a fourth root of K_C. There are exactly 4^(2g)=4^42 possible line bundles of this kind when one exists, because the fourth-power map on Pic0(C) has kernel of that order. Only some can occur. For a root L that does occur, h0(L−H)=1 by (1.2), so there is a unique effective divisor D in |L−H|. It is reduced of length six, being the pullback of Z. Thus the unmarked isomorphism cannot vary this divisor continuously.

The second ruling pulls back to a square root S_C of K_C−6H, by adjunction. There are at most2^42 such roots. Each occurring S_C has h0(S_C)=2, so its morphism to the second P1 is fixed up to PGL2. With H,S_C,L fixed, an embedding into Sigma is therefore determined up to PGL2×PGL2. It must take D to the fixed six-point set Z. Both projections of Z have at least three distinct values: each ruling has degree two on Gamma, so a fiber contains at most two of the six distinct marked points. The same is true for the projected D of any successful embedding.

There are at most6!=720 bijections D→Z. For a fixed bijection there is at most one automorphism of the first P1 and at most one of the second P1 realizing it, since each has its values fixed on at least three distinct points. Consequently

    #{v∈W_pr(C): C_v≅C} ≤ 720·4^42·2^42 = 720·8^42.        (3.1)

This does not assume that alpha preserves L, S, Z, Gamma, coordinates, or a frame. All their possible pullbacks have been counted. Nor does it identify scalar vectors with projective directions: the curve count only begins after the source residue construction has supplied the permitted fixed contact system. By (1.1), different normalized kappa's cannot define the same embedded divisor. The count is therefore a count of W-points, not merely of equations up to scaling.

This is the additional rigidity operation used below. The source's headline and routine formation of products supply no such unmarked comparison.

## 4. One generic source germ retains the algebraic exceptional curve

Put K=k0(W). Since K is finitely generated over the countable algebraically closed field k0, choose an embedding K→C. The generic curve C_eta then becomes a complex member of W_pr: every nonzero defining function of a nonempty open remains nonzero under the field embedding. The fixed Gamma,Z and all source residue hypotheses remain the stipulated ones.

Apply the complete source construction to this one complex curve. It makes finite transition germs, lifts jets modulo I^9 T_Y(−log C) on a realized Hausdorff neighborhood, and contracts C. The determinant is t^5 u with u|C=1, so the resulting normal isolated analytic germ has free analytic tangent sheaf and exceptional curve C_eta,C with conormal L_eta,C. All of those operations are already supplied by the source. This is not an assertion of their holomorphic dependence on 21 parameters.

The source's prop:algebraization produces a normal integral affine complex surface X_C with a single singular point x, a global algebraic derivation basis, and a completed local ring isomorphism to that analytic germ. This uses equations together with their complete relation matrix, not an arbitrary equation truncation. The completed tangent module is the continuous Jacobian kernel, and finite-presentation/faithful-flatness descent supplies the actual algebraic basis.

We require more than a completion isomorphism of bare sets. Apply Artin1968, Theorem1.2 and Corollary1.6, to the two analytic local rings: the original analytic germ and the analytification of (X_C,x). Their completions agree, so they are analytically isomorphic. The actual operative proof encodes a formal homomorphism by its coordinate images and finitely many ideal-membership coefficients, approximates the resulting finite analytic system, and keeps the map unchanged modulo the square of the maximal ideal. The resulting map is an isomorphism by Nakayama, completeness, and faithful flatness. No identification of unrestricted algebraic differentials of C[[x]] with continuous differentials is made.

Take the algebraic minimal resolution pi_C:Y_C→X_C. Its existence and projectivity may be obtained from algebraic surface resolution followed by contraction of exceptional (−1)-curves; the precise minimality operation is Lipman1969, Corollary27.3. Projectivity over the affine X_C follows from the same paper's Corollary27.2 applied to the smooth surface Y_C. The latter result assumes rational singularities of its DOMAIN, satisfied because Y_C is smooth; it is not applied to the nonrational singularity on X_C. The rational-singularity-only Theorem4.1 is used solely for factorization between smooth surfaces, not for the source singularity.

The analytification of this resolution is analytically minimal. Brieskorn1966, §1.6, proves for every normal two-dimensional complex space that the minimal resolution is unique and is characterized by the absence of exceptional smooth rational (−1)-curves. His proof resolves the graph between two resolutions, factors the resulting smooth modifications into point blowups, and cancels the exceptional curves of the first kind. The source resolution has only the genus-21 curve C, so it has none. The algebraic minimal resolution has none either; a compact exceptional analytic curve on Y_C is algebraic by the proper/projective comparison, and being a smooth rational (−1)-curve is unchanged by analytification. Hence the two resolutions agree near their exceptional fibers.

It follows that the entire reduced exceptional fiber of pi_C is a smooth curve E_C algebraically isomorphic to C_eta,C, with conormal algebraically isomorphic to L_eta,C. These identifications are algebraic by GAGA on the projective curves. The ideal of E_C is invertible. The reduced support of pi_C^*m_x is exactly E_C, and pi_C is an isomorphism outside E_C. Thus we have a FINITE algebraic diagram including X_C, x, Y_C, E_C, their maps, the exceptional-curve and conormal identifications, and the two algebraic derivations. The analytic neighborhood itself will not be spread.

## 5. Specialize the finite diagram over the generic curve

We give the specialization argument carefully, as the complex coefficients produced by the source need not be algebraic over K.

Choose a finitely generated K-subalgebra R⊂C containing the finitely many coefficients of the algebraic diagram of §4. Enlarge R and invert finitely many nonzero elements when necessary. Finite presentations, morphisms, equalities and isomorphisms descend to such a stage. This is the finite affine-cover and gluing argument of Stacks 01ZM; inverse morphisms and their two identities are included. A projective embedding Y_C⊂P^n_(X_C) can be descended with its equations, so projectivity is retained. We descend E_C as an effective Cartier divisor and its isomorphism to C_eta×Spec R, together with the conormal isomorphism to L_eta. Equality of the reduced exceptional support can be retained by finite ideal containments

    I_E^a ⊂ m_s O_Y ⊂ I_E                              (5.1)

on a finite affine cover, for some a≥1, with their finitely many coefficients. Such a exists on the original noetherian Y_C because the radicals agree and it is quasi-compact. The inverse isomorphism off E and the section is included as finite data.

We can arrange, after further localization of R, that X_R→Spec R is flat with geometrically integral normal two-dimensional fibers, and Y_R→Spec R is smooth of relative dimension two. Here C is a faithfully flat extension of Frac(R), so the geometric generic properties are known. Generic flatness, and constructibility of geometric integrality/normality for finitely presented fibers, give a nonempty open of Spec R on which these properties hold. The exact nonproper inputs are EGA IV3,9.7.7 and9.9.4–9.9.5: a constructible subset containing the generic point of an integral noetherian base contains an open neighborhood of it. We do not incorrectly invoke the proper-family openness statement12.2.4 for the affine X_R. For smoothness of Y_R, the complement of the smooth locus has constructible image in Spec R and misses its generic point; remove its closure. The same argument removes any unwanted relative-dimension locus. The diagram is finite type throughout.

Here is the additional module step needed to preserve actual tangent freeness on every fiber and every later base change. Write the affine algebra as

    A_R=R[z1,...,ze]/(f1,...,fq),
    J:A_R^e→A_R^q,  (a_j)↦(sum_j a_j partial_j f_i)_i,
    Q=coker J,  M=ker J.                                 (5.2)

Both Q and M are finite A_R-modules. After enlarging R, the two source derivations give a map theta:A_R²→M. Since it is an isomorphism after the faithfully flat extension Frac(R)→C, its finite kernel and cokernel vanish over Frac(R). Each is killed after inverting one nonzero element of R: choose finitely many A_R-generators and clear their R-denominators. Thus theta becomes an isomorphism.

Use generic flatness also for Q, in addition to A_R, to make Q flat over R. With I=im J the exact sequences

    0→I→A_R^q→Q→0,
    0→M→A_R^e→I→0                                      (5.3)

then have R-flat I (kernel of a surjection between flat modules) and are preserved by tensoring with any R-algebra R'. Therefore

    M⊗R R' = ker(J⊗R R') = Der_(R')(A_R⊗R R'),           (5.4)

using the Jacobian presentation of relative Kahler differentials. The source basis, transported by theta, is a basis of this kernel. This is stronger than merely descending two vector fields or knowing generic independence. It makes no flatness assertion about the differential module itself. The argument works also for nonnoetherian R', because the two Tor vanishings in (5.3) are consequences of flatness, and the polynomial differential presentation is valid after arbitrary base change.

The remaining geometric identities, including E≅C_eta×Spec R, its conormal, the complement isomorphism and (5.1), have been retained after localization. Choose any closed point of this nonempty affine K-scheme Spec R. Its residue field K' is a finite extension of K by the weak Nullstellensatz. Its fiber gives the entire algebraic diagram over K', with the same generic exceptional curve C_eta,K', the specified normal bundle, and universally compatible relative tangent basis. Geometric properties hold because of the open choices, not because specialization automatically preserves them.

The marked point remains singular. Over an algebraically closed field, if it were smooth, a local regular generator of its canonical sheaf would pull back to an effective divisor aE with a≥0. But adjunction on Y gives

    K_Y·E=2g(E)−2−E²=40+10=50,
    aE²=−10a≤0,

a contradiction. Outside the point the complement isomorphism identifies X with a smooth surface. Thus the singular locus is exactly that point.

## 6. Spread over a finite étale cover of an open 21-space

Normalize W_pr in the finite extension K'/K. Normalization is finite because W_pr is of finite type over a field and excellent. Characteristic zero makes K'/K separable. After shrinking W_pr to a nonempty principal open U, its normalization B→U is finite étale, surjective and of constant degree d=[K':K]. It is integral, smooth and affine; since k0 is algebraically closed, it is geometrically integral. Its dimension is21.

Spread the finite diagram over K' to an open of B. This uses exactly the finite presentation, geometric constructibility, and Jacobian-kernel argument of §5, now with base a finitely generated k0-domain of fraction field K'. In particular make A and coker J flat over the base, preserve theta, and preserve E's identification with the pullback of the universal curve and its conormal L. A projective model of Y→X descends using the embedding; smoothness of Y/B and geometric normality/integrality of X fibers are obtained on an open. Keep the two ideal containments (5.1) and the complement isomorphism.

These conditions might initially require removing a closed proper subset of B. Since B→U is finite, its image is closed proper in U (it misses the generic point). Remove that image and then choose a smaller nonempty principal open U in the original W. Its full inverse image B retains all the conditions and is still finite étale of degree d. Thus none of the fibers of the finite cover is silently omitted over the final U.

We have now constructed p,s,pi,Y,E exactly as in the frozen statement. Formula (5.4), applied locally to any B'→B, proves assertion2 including arbitrary base change. The scheme-theoretic fiber of pi over s(b) may be nonreduced; (5.1) proves exactly the claimed statement about its reduced support, which is E_b. The conormal of E_b is L_b because smoothness of E/B and Y/B and the descended Cartier and line-bundle data retain the conormal after base change. The only exceptional curve is smooth of genus21, so pi_b is minimal by the minimal-resolution criterion. All geometric fibers are normal and integral, and the adjunction argument of §5 proves assertion1 for every algebraically closed residue extension. These facts establish assertions1–3 at their full quantifiers.

## 7. Canonical structure and finite repetition of complete local rings

On each geometric fiber the determinant of the two global derivations trivializes the tangent determinant on the smooth locus. Its dual trivializes the canonical line bundle there. A normal surface is Cohen–Macaulay; its dualizing sheaf is the reflexive extension of that canonical line bundle. Hartogs and reflexivity therefore give omega_(X_b)≅O_(X_b). Thus X_b is Gorenstein, with a canonical generator having neither zeros nor poles on its smooth locus.

Pull this generator to Y_b as a rational two-form. Its divisor is supported on the only exceptional curve E_b, so it is aE_b for some integer a. Intersect with E_b and use adjunction:

    a(−10)=K_(Y_b)·E_b=50,  hence a=−5.                 (7.1)

This proves assertion4. It does not assert that the frame is commuting, that its dual one-forms extend holomorphically, or that the singularity is log canonical. The discrepancy is explicitly outside that positive range.

Finally suppose b,b'∈B(C) have isomorphic complete local C-algebras at their marked points. Their analytic germs are isomorphic by Artin1968, Cor1.6, whose hypotheses hold for both finite-type complex surfaces. Uniqueness of the analytic minimal resolution, using Brieskorn §1.6, implies that E_b and E_b' are isomorphic as unmarked compact curves. By GAGA this is an algebraic curve isomorphism. No isomorphism of the affine surfaces or their frames was assumed.

For a fixed complete local C-algebra R which occurs, choose one b with that completion. Every other point with completion R has exceptional curve isomorphic to E_b. By (3.1), there are at most720·8^42 possible u= rho(b')∈U(C). Over each u the finite étale map has exactly d complex points. Hence the total is at most

    N=720·8^42·d,                                      (7.2)

as frozen. If R never occurs, the set is empty and the same bound holds. An arbitrary affine-surface isomorphism must carry the unique singular point to the unique singular point, so it also induces one of these completed-local isomorphisms. The same bound therefore holds for affine-surface isomorphism classes.

The morphism from the universal curve system to the genus21 curve moduli space has finite fibers by (3.1), so its image has dimension21. This dimension statement can equally be expressed without choosing a coarse moduli space: the 21-dimensional parameter scheme has finite fibers under unmarked curve isomorphism, and the constructed singularity isomorphism relation refines that relation after a finite cover. This proves the last assertion of the frozen statement.

## 8. Strongest-payment comparison and boundaries

The source pays the residue-balanced six-vector construction, the complete finite jet induction, analytic lifting and isolated-germ algebraization with an actual algebraic global tangent basis. Varying a parameter in its formulas alone is not the theorem proved here. The additional closed operations are (i) the primitive-cover incidence calculation and finite unmarked root/pencil/contact count retaining all21 dimensions, and (ii) carrying the actual exceptional curve through completion, analytic equivalence, minimal resolution, finite-diagram specialization, and universal Jacobian-kernel base change. Neither requires a claim of relative convergence of the source's flows.

Hironaka's equivalence statements and Artin1969 already pay equation-and-relation determinacy and algebraization for isolated singularities. Moehring–van Straten2002, Theorem1.1 and its full proof, are stronger than a maximal-ideal-only statement: an ideal annihilating relative T1 over a noetherian coefficient ring is allowed. Thus a relative finite-determinacy estimate itself is not presented as new. Elkik1973 Theorem7/lemmas6–7 also algebraize suitable formally smooth-off-the-closed-locus algebras, but its stated theorem7 assumes a principal ideal. Our construction uses the source's already realized single analytic germ and finite algebraic data, so no unsupported application to a many-generated section ideal or to an unconstructed formal family is needed.

The original I31 scope constructs a complete-local threefold with a fixed exceptional SURFACE and excludes every positive grading. It explicitly avoids analytic/finite-type algebraization and claims no nonzero-parameter isomorphism separation. Its primitive canonical-weight, full-section-ring and Euler arguments are not repackaged here. I98/A98 and I102 construct finite-domain analytic deformations with exact moving first jets and radius-dependent base shrinkings; they do not give the algebraic finite-diagram operation used here. Their larger full targets remain unchanged. The r146 complementary-isomorphism calculation is preserved; it supplied the caution that a marked parameter is not automatically intrinsic, addressed here by the complete unmarked count, not by importing its separate cancellation family.

This is one author theorem. The integer21, the curve count, the algebraic family, and its discrepancy are not separate candidates. No new-to-literature priority, contribution grade, acceptance, campaign count, or exhaustion claim is made. The degree d and affine presentation remain existential. The theorem does not solve a universal-family or all-parameter extension problem.
