# Arithmetic147 — independent contribution review, round 1

**Conditional full-scope contribution verdict: TECHNICAL.** This verdict is conditional on correctness of the **entire unchanged frozen theorem**, SHA256 `aa34714980af05fbbed5ae223b73b8ec10c1b19d8865ff61fbf2615f582682a8` (2803 bytes), and concerns the submitted author proof, SHA256 `5bead5a1ae6f45922b566ed0519198c4fe171d2cb301385d5cd75606dc2739f8` (27979 bytes). It is not a correctness verdict, acceptance, adoption, or campaign count. No correctness-role material was read or inferred. Source048 and all operative proofs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.

The reason is an affirmative integrated reduction, not an absence-of-literature claim. The source already supplies the particular 21-dimensional normalized curve system and its special-divisor identities, as well as the hard singularity construction. Elementary curve reconstruction gives the exact finite unmarked bound. Classical approximation, minimal-resolution comparison, finite-presentation descent, constructibility and generic flatness then supply the whole existential family, including the universal ordered tangent frame. After composing these operations at their actual hypotheses, no closed residual requiring a new mathematical mechanism remains within the frozen scope. The detailed reduction follows; calling the ingredients familiar without paying these interfaces would not suffice.

## 1. Exact comparison scope and source payment

All eight canonical TeX bodies were read, including every input of the actual 2742-byte wrapper `paper.tex`, after Git-blob authentication against the complete 13223-entry tree. The source's statement and its proof operations are both inputs. Its curve section explicitly constructs

    W = kappa0 + gamma H0(P1×P1,O(6,2)),

with fixed elliptic Gamma, six distinct points Z and nonzero restriction beta^4. Hence dim W=7·3=21 and scalar duplication of equations is already removed: two sections with the same divisor differ by a scalar, which must be one on restricting to Gamma.

The source's smooth open supplies, for every member, a connected smooth (8,4)-curve C, exact fourth contact at Z, H=O(1,0)|C, L=H+Z, and

    g(C)=21, deg H=4, deg L=10, K_C=4L,
    h0(H)=2, h0(O_C(Z))=1.

These are actual consequences of `curve:adjoint-jets` and `prop:curve-data`, not estimates from the title. In particular h0(O_C(Z))=1 is already paid. The source also pays the entire trace/principal-parts comparison with its scalar and sign, residue-balanced vectors, finite flow and determinant induction, realized Hausdorff neighborhood, cofinal formal-functions lifting, contraction, and equation-plus-full-relation-matrix algebraization with an algebraic global tangent basis. Its `analytic:invariants` already gives the genus, self-intersection and canonical behavior of the analytic germ. None of these is credited again as a new contribution.

The fixed data can be chosen over k0=Qbar using the actual source formulas: the torsion and division-point choices are algebraic; the vector formula involves algebraic square roots and the roots of a cubic with algebraic coefficients; a sufficiently small general algebraic lambda and an algebraic isometry avoid the finitely many prohibited conditions. The lift of beta^4 is solution of an algebraic linear restriction problem with H1(O(6,2))=0. Choosing those data once is a parameter specialization, not a new arithmetic descent theorem.

For the second ruling S=O(0,1)|C, the exact restriction sequence has kernel O(-8,-3). Künneth gives H0=H1=0 for this kernel, hence h0(S)=2. Adjunction on the quadric gives K_C=6H+2S. These two elementary identities are the only extra section-count inputs below.

## 2. Full primitive-open calculation

A degree-four pencil need not be primitive merely because it has degree four. Here the necessary open can be obtained within the exact source affine system.

Let T be the finite set of branch values of Gamma's first projection and the first-projection values of Z. At a point off Gamma, multiplication by gamma is a unit on vertical jets. Restriction of H0(O(6,2)) to a vertical fiber is all H0(O(2)), which surjects onto a vertical jet of length three. Thus a root of multiplicity at least three imposes three independent affine linear conditions on W at a specified point. The point moves in dimension two, so the incidence has dimension at most 21+2-3=20. Its image closure cannot fill W.

For x outside T, the two Gamma intersections a,b are distinct and the prescribed quartic values A,B there are nonzero. The allowed quartics form an affine three-space: their differences are gamma times all binary quadratics. A quartic with two distinct double roots has the form c l_u^2 l_v^2. The value at a determines c and the value at b imposes

    ((a-u)(a-v)/((b-u)(b-v)))^2 = A/B

in a suitable affine chart. This is a nonconstant equation on the two-dimensional unordered-pair space, leaving dimension at most one. The restriction kernel has dimension 18; allowing x to vary gives total dimension at most 18+1+1=20. Homogeneous coordinates cover infinity and do not alter the dimension estimate.

For each of the finitely many x in T impose squarefreeness. If gamma has two distinct roots, any forced zero can be made simple by choosing the quadratic value nonzero there, and the remaining roots can be separated. If both prescribed values vanish, the quartic is gamma times an arbitrary quadratic, so choose the latter with distinct roots away from gamma's roots. If gamma has a double root a, then a is not in Z, since the source first pencil is unramified at Z. The prescribed value at a is nonzero. At any other point, vanishing of the quartic and its derivative imposes two independent conditions on the three quadratic coefficients; the moving-point incidence has dimension at most two. Therefore squarefree quartics again exist. Restriction is surjective, so each such condition gives a nonempty open upstairs. Their finite intersection in the irreducible W is nonempty; simultaneous interpolation of all these fibers is unnecessary.

Intersect with the source smooth open and remove the preceding two bad image closures. All ramification is then simple with distinct branch values. Connectedness and the monodromy generators give S4: the transposition graph must be connected, and transpositions on the edges of a connected graph generate the full symmetric group. Consequently the pencil is primitive. These conditions define a k0-open. For a geometric fiber over a larger algebraically closed characteristic-zero field, the finite curve/map data and any putative intermediate cover descend to a finitely generated field embeddable in C, so the same primitivity conclusion applies. This pays the full geometric-open requirement, not merely one convenient complex curve.

The operation is elementary discriminant-incidence avoidance in a fixed linear system, followed by elementary monodromy. The source did not need to state the resulting primitive-open corollary for this operation to be paid.

## 3. Unmarked curve comparison with the exact constant

Fix an abstract complex curve C occurring in the primitive open. Suppose it has two degree-four maps to P1. Let D be the normalization of the image of their product and e the degree C→D. Then e divides four. If e=1, the image is a (4,4)-curve whose arithmetic genus is 9; normalization cannot increase arithmetic genus, contradicting g(C)=21. If e=2, the first pencil factors nontrivially, contrary to primitivity. If e=4, each map D→P1 has degree one, so the two pencils differ only by a target automorphism. Thus H and its complete pencil are intrinsic to C.

Now pull back all the source data by an arbitrary isomorphism C→C_v. No marking is assumed preserved. There are at most 4^(2g)=4^42 possibilities for the pulled-back L, since it is a fourth root of K_C. This is the usual Picard-torsion calculation: over C the Jacobian is C^g/Λ with Λ of rank 2g, so its n-torsion has order n^(2g); any nonempty set of n-th roots is a torsor under that group. For each occurring L, the source's h0(L-H)=1 recovers a unique effective divisor D_Z. It is reduced of length six because it is the pullback of Z.

The pulled-back second ruling is a square root S_C of K_C-6H. There are at most 2^42 such roots, and every occurring one has h0(S_C)=2. Fixing H and S_C therefore fixes their complete maps up to PGL2×PGL2. Fix also L and hence D_Z. There are at most 6! bijections D_Z→Z. For any successful embedding, each projection of the six points has at least three distinct values: on Gamma a ruling fiber contains at most two distinct points. Consequently a fixed bijection fixes each remaining PGL2 transformation uniquely, since its effect is prescribed on at least three distinct values.

It follows that the number of possible images C_v for this abstract C is at most

    6! · 4^42 · 2^42 = 720 · 8^42.

Different choices of an isomorphism C→C_v can give the same image, which only decreases the count. There is no additional factor from Aut(C), no preservation-of-L assumption, and no division by a continuous group left unpaid. Normalization kappa|Gamma=beta^4 identifies each image with at most one actual W-point. The count is thus the frozen base-point count, not a count of marked models. The deliberately generous root/bijection product is not an effective determinacy bound or a new quantitative estimate beyond finite torsion and elementary coordinate rigidity.

This is the strongest part of the candidate beyond the source's stated endpoint. It is a useful reconstruction argument, but its closure uses precisely the source's existing h0(Z)=1 and canonical-root identities together with the elementary high-genus pencil argument above. I find no further nonroutine residual here after making that comparison explicit.

## 4. Preserve the actual exceptional pair through algebraization

Let K=k0(W), embed K into C over k0, and apply the stipulated source to the resulting single generic curve. This is legitimate because the generic point avoids every nonempty open condition in question. It assumes no relative analytic selection of flows, sections or convergence radii. The source provides an algebraic normal integral affine surface with a unique singular point, an algebraic ordered free tangent frame, and completion isomorphic to the source analytic germ.

Artin's actual 1968 Theorem 1.2 and Corollary 1.6 pay the completion-to-analytic comparison. A formal homomorphism is encoded by the images of finitely many coordinates and coefficients expressing the target equations in the source ideal. Approximation solves these finite analytic equations and preserves the cotangent map modulo the square of the maximal ideal. Nakayama gives surjectivity on completed rings; equality of all finite quotient lengths gives injectivity, and faithful flatness returns to the analytic local rings. The formal coordinate change need not itself converge. Both rings here are complex analytic local rings, as required. The complete theorem proof was read, not just the corollary's headline.

Take an algebraic minimal resolution of the affine surface. Lipman 27.3 supplies general minimality once resolution exists. Its proof uses a common resolution and the change of intersection/Euler-characteristic expressions under point blowups. The rational-target hypothesis of Lipman 4.1 is not imposed on the source singularity: only the smooth-surface factorization part is used. Lipman 27.2 gives projectivity over the affine target by applying its rational-singularity assumption to the **smooth domain of the proper map**, which satisfies it.

Brieskorn's actual §1.6, printed p.81, states and proves minimal-resolution uniqueness for every normal two-dimensional complex space. The proof resolves the graph of the birational correspondence, factors the two smooth modifications into point blowups, and cancels exceptional curves of the first kind. The source resolution has only a smooth genus-21 curve, hence no smooth rational (-1)-curve. An algebraic minimal resolution also has none analytically: compact exceptional analytic curves in its projective fiber are algebraic, and the relevant smoothness, genus and intersection numbers agree. Thus the two analytic minimal resolutions coincide near the exceptional locus.

In particular the entire exceptional curve and its conormal, not just their numerical invariants, agree with (C_eta,L_eta). GAGA on the projective curves makes the curve isomorphism and conormal isomorphism algebraic. The algebraic resolution, exceptional Cartier divisor, pair identifications, maps and frame are now finite algebraic data. No analytic neighborhood is claimed to descend or spread. This is exactly the distinction that lets the following classical construction apply.

## 5. Finite-diagram specialization and the universal ordered kernel

Choose a finitely generated K-subalgebra R⊂C containing the coefficients of the finite algebraic diagram. The actual proof of Stacks 01ZM descends affine presentations, then morphisms and equalities, and finally the finite open-cover gluing and cocycle identities. Apply that proof to the diagram, including both directions of each isomorphism and both composition identities. Descend a projective embedding Y→P^n_X; it pays projectivity without any properness assumption on X over R.

Include E≅C_eta×Spec R, the conormal isomorphism, local Cartier equations and their transition units, the section, and the inverse isomorphism between the complements. Equality of the reduced exceptional support can be expressed by finitely many containments

    I_E^a ⊂ I_s O_Y ⊂ I_E.

A single exponent exists by quasi-compactness and equality of radicals in the original noetherian diagram. On a finite affine cover these are finite equations with finitely many witnesses, so they descend. These inclusions claim reduced support only, exactly as frozen; they do not claim a reduced scheme-theoretic exceptional fiber.

After localizing R, make X/R flat and its fibers geometrically integral and geometrically normal of dimension two; make Y/R smooth of relative dimension two. Geometric generic properties descend from the faithfully flat algebraically closed extension C/Frac(R). EGA IV3 9.7.7 and 9.9.4–9.9.5 give constructibility for finitely presented, potentially nonproper families. A constructible subset containing the generic point of an integral noetherian scheme contains a nonempty open. Likewise the constructible image of a bad smoothness or dimension locus which misses the generic point can be avoided on an open. No proper-family openness shortcut is used. E's identification with the smooth curve family makes E/R flat; the Cartier sequence therefore also retains its fiberwise ideal/conormal interpretation after tensoring.

For the tangent assertion retain a finite affine presentation

    A=R[z1,...,ze]/(f1,...,fq),
    J:A^e→A^q,   J(v)_i=Σ_j (∂f_i/∂z_j)v_j,
    M=ker J, I=im J, Q=coker J.

The ordered source columns descend to theta:A^2→M. J theta=0 consists of finite equations. Over Frac(R), theta is an isomorphism, since it becomes one over C. Its kernel and cokernel are finite A-modules; a finite list of A-generators is killed by finitely many nonzero R-denominators. Localize at their product to make theta an isomorphism on the whole affine algebra.

Apply actual generic flatness (Stacks 0529) to A and the **whole finite A-module Q**, not just a chosen minor or the images of the two columns. With both A and Q flat over R, the sequence

    0→I→A^q→Q→0

makes I R-flat: the higher Tor groups of the two flat modules vanish. The second sequence

    0→M→A^e→I→0

then also stays exact after tensoring by **any** R-algebra R'. Hence

    M⊗_R R' = ker(J⊗_R R') = Der_(R')(A⊗_R R'),
    theta⊗1:(A⊗_R R')^2 ≅ Der_(R')(A⊗_R R').

This equality uses the finite presentation of relative Kähler differentials, valid over arbitrary rings. It does not identify algebraic and continuous differentials of a power-series ring, and it does not require Ω to be flat. No noetherian hypothesis is placed on R'. Localize this calculation on arbitrary B' and on its relative affine preimage to obtain the sheaf assertion; the maps glue because they are the canonical base-change map and the fixed ordered columns. This pays nonaffine as well as nonnoetherian base changes, including preservation of the specified **global ordered basis**.

After all these finite localizations, choose a closed point of Spec R. Its residue field K' is finite over K by the weak Nullstellensatz. The specialized diagram retains the same generic C_eta and L_eta, because their identifications were part of the descended diagram. This procedure is a standard finite-type specialization, not a deduction that the original complex coefficients were algebraic over K. It is compatible with all the preceding geometric properties because those were ensured on the same nonempty open before taking the closed point.

## 6. Exact base and all geometric fibers

Normalize the primitive open in K'/K. Excellence gives finiteness and characteristic zero gives generic étaleness. Shrink to a nonempty principal open U⊂W where the finite normalization B→U is étale of degree d=[K':K]. It is surjective, affine and integral. Since k0 is algebraically closed, integral finite-type B is geometrically integral; étaleness over smooth U makes B smooth and dim B=21.

Spread the K'-diagram to an open of B with the same finite-presentation, constructibility and full-Jacobian-cokernel operations. If any conditions initially hold only after deleting a proper closed subset of B, remove its image from U. That image is closed because the cover is finite and is proper because it misses the generic point. Then choose a smaller principal open in the original affine W. Taking its **full preimage** retains all d points over every complex U-point, rather than silently dropping some sheets.

For every geometric point over every algebraically closed extension, X_b is integral normal affine of dimension two, Y_b is smooth of dimension two, the morphism is projective and isomorphic away from the marked point, and its entire reduced exceptional fiber is the specified smooth C_b with conormal L_b. There can be no additional surface component supported inside E_b: smooth relative dimension two and the one-dimensional Cartier divisor rule that out. There is no exceptional rational (-1)-curve, so the resolution is minimal, by the algebraic criterion. The line-bundle identification gives E_b^2=-deg L_b=-10 and L_b^4=K_Cb.

The marked point cannot be smooth. A regular local canonical generator at a hypothetical smooth marked point pulls back to a holomorphic two-form with effective divisor aE_b, a≥0. Adjunction gives K_Yb·E_b=2g-2-E_b^2=50, whereas aE_b^2=-10a≤0. Off that point the complement isomorphism to the smooth resolution proves smoothness. This covers exactly one singular point at every geometric fiber, not just at closed complex parameters.

## 7. Canonical assertion, every completion class and dimension

On each geometric fiber the determinant of the global tangent frame trivializes the canonical bundle on its smooth locus. A normal surface is Cohen–Macaulay; its dualizing sheaf is the reflexive extension of that canonical bundle. Hartogs therefore gives omega_Xb≅O_Xb. It follows that every fiber is Gorenstein with trivial dualizing sheaf, as claimed. This does not assert a trivial relative dualizing sheaf after every base change; the frozen canonical assertion is fiberwise.

Pull back that canonical generator to Y_b. Its rational divisor has no nonexceptional component and the only exceptional curve is E_b, so it is aE_b. Adjunction gives -10a=50, hence a=-5. This argument is valid over all the algebraically closed extensions in the statement. It needs neither a commuting frame nor extension of its dual one-forms as holomorphic forms across E.

Fix **any** complete local C-algebra R0. If it never occurs, the claimed cardinality bound is automatic. Otherwise choose one occurring point b0. Every other occurrence has analytically isomorphic germ by Artin 1968, hence the same unmarked exceptional curve by Brieskorn's uniqueness, and hence an algebraically isomorphic curve by GAGA. Section 3 allows at most 720·8^42 possible U-points. Each has exactly d complex points above it under the finite étale cover. Thus the exact bound is

    #{b∈B(C) : completed O_(X_b,s(b)) ≅ R0} ≤ 720·8^42·d.

An arbitrary affine-surface isomorphism must preserve the unique singular point and induces such a completed local isomorphism. It obeys the same repetition bound. The source universal curve on the primitive open has finite fibers under abstract curve isomorphism, so its classifying image has dimension 21. The finite cover has dimension 21, and the singular-germ equivalence relation refines the exceptional-curve relation. This establishes the claimed full 21-dimensional variation in exactly the finite-repetition sense of the theorem. It asserts no pairwise distinctness, universal moduli family or chosen analytic coordinates.

## 8. Strongest primary and history comparison; residual assessment

The source's finite-determinacy proof was read in full with the complete relation matrix. The comparison is strengthened, not weakened, by the actual primary literature. Hironaka's equivalence Theorems I/II and application 3.3 concern compatible maps and relation matrices; the complete retained article body was read here, including its obstruction-module setup and its line-bundle algebraization sketch. It does not provide a full detailed proof of every equivalence theorem it states. Möhring–van Straten 2002 Theorem 1.1 supplies a fully read proof over a noetherian coefficient ring with an arbitrary annihilating ideal in a complete Zariski pair: Artin–Rees corrects the relation error into the normal module, an annihilator of relative T1 turns it into a derivation correction, a generator change removes the ideal-valued remainder, and invariant constants permit convergent iteration. This stronger relative determinacy is paid. It is not a construction of a missing formal family; the one-generic-germ method avoids needing that object.

Artin 1969 Theorem 1.10, 3.8–3.9 and the complete §5 proof were read, including the section's actual last sentence. Elkik Theorem 7 and its Lemmas 6–7 were compared with their actual principal-ideal hypothesis, not extended to a many-generated section ideal. The needed algebraization is already the stipulated source output; these classical comparisons therefore do not leave a relative algebraization obligation in the frozen scope.

The complete authorized original I31 body was read through its top-level endpoint. It constructs a complete-local threefold with a fixed exceptional **surface**, primitive canonical-weight formal deformation, full-section-ring preservation and obstruction to every positive grading. It explicitly does not assert analytic convergence, finite-type C algebraization, or separation of nonzero parameters. None of those old scopes is reopened here. The selected complete original I98 and I102 sections construct finite-domain analytic families with exact moving first jets and radius-dependent base shrinkings. They neither supply nor obstruct the finite algebraic-diagram specialization above. Their prior dispositions and larger targets are untouched. No arithmetic146 body, excluded role or peer finding was read; mentions in the explicitly admitted author material were not expanded into permission to read their originals.

The integrated additional work is therefore identifiable but technical: elementary curve rigidity exploits special divisors already built by the source, and the generic-point method spreads finite algebraic output using existing descent and flatness operations. In particular the arbitrary-base-change quantifier is fully paid by two short exact sequences, and full geometric fibers by simultaneous shrinking and constructibility. These are compatible operations on the same diagram, not separately named folklore with a bridge left between them.

**No unresolved essential contribution-assessment step remains at the frozen scope.** There is no identified closed residual beyond this composition that would justify SUBSTANTIAL under the supplied acceptance rule. This is not a claim that the theorem's exact wording previously appeared in a paper, nor an exhaustive worldwide-priority claim. Its precise combination may be new to the project and useful; that does not by itself meet the substantial-contribution threshold. Reading and access limitations are disclosed separately and were not used as evidence of novelty or as a shortcut to the verdict.

No equations, effective algebraization order, bound on d, universal property, extension across the deleted locus, pairwise distinctness, commuting frame or classification result was added. No author file was modified. Parent alone integrates and adopts dispositions and counts.

## References actually compared

- Source048, immutable pin above, all eight canonical TeX files; exact private authentication and semantic extents accompany this review.
- M. Artin, *On the solutions of analytic equations*, Invent. Math. 5 (1968), 277–291, Theorem 1.2 and Corollary 1.6; [published text](https://link.springer.com/content/pdf/10.1007/BF01389777.pdf).
- M. Artin, *Algebraic approximation of structures over complete local rings*, Publ. Math. IHÉS 36 (1969), 23–58; [published text](https://www.numdam.org/item/PMIHES_1969__36__23_0.pdf).
- H. Hironaka, *Formal line bundles along exceptional loci*, in the 1969 Bombay colloquium volume, 201–218; [retained TIFR volume](https://mathweb.tifr.res.in/Documents/Publications/Studies/SM_04-Algebraic-Geometry.pdf).
- K. Möhring and D. van Straten, *A criterion for the equivalence of formal singularities*, Amer. J. Math. 124 (2002), 1319–1327, Theorem 1.1 and full §2 proof; [author-hosted published version](https://download.uni-mainz.de/mathematik/Algebraische%20Geometrie/DvS-Publikationen/29.A%20criterion%20for%20the%20equivalence%20of%20formal%20singularities%20-%202002.pdf).
- R. Elkik, *Solutions d'équations à coefficients dans un anneau hensélien*, Ann. ENS 6 (1973), Theorem 7, Lemmas 6–7; [published text](https://www.numdam.org/item/ASENS_1973_4_6_4_553_0.pdf).
- J. Lipman, *Rational singularities*, Publ. Math. IHÉS 36 (1969), §4, Corollaries 27.2–27.3 and proofs; [published text](https://www.numdam.org/item/PMIHES_1969__36__195_0.pdf).
- E. Brieskorn, *Über die Auflösung gewisser Singularitäten von holomorphen Abbildungen*, Math. Ann. 166 (1966), §1.6; [GDZ scanned primary](https://gdz.sub.uni-goettingen.de/download/PPN235181684_0166/PPN235181684_0166___LOG_0028.pdf).
- EGA IV3 (1966), 9.7.7 and 9.9.4–9.9.5 with proofs; [published text](https://www.numdam.org/item/PMIHES_1966__28__5_0.pdf).
- Stacks Project [01ZM](https://stacks.math.columbia.edu/tag/01ZM), [0529](https://stacks.math.columbia.edu/tag/0529), [038Z](https://stacks.math.columbia.edu/tag/038Z), complete retained statements and proofs.
