# r194 — prefreeze calculations, not a frozen theorem

This is a research record. No full-scope nominee was frozen. All five Source318 proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are premises, including their operative constructions. The module calculations below are reductions using those premises, the actual primary interfaces in INTERFACES.md, and the already completed i105/i107 constructions. They are not offered as a new substantial result or as substitutes for an immutable old target.

## 1. Conventions and the already paid obstruction

Fix p≥5 until §6. Put S=S_p^∧ (derived completion), A_i=L_i S, R_i=L_{K(i)}S, Q=L_0S=H Q_p, T=L_{K(3)}S, X=L_2T, and J=K(1)∨K(2). All modules in §§1–5 are E(2)-local S-modules, equivalently A_2-modules. Write M[j]=Σ^jM. A localization is taken on the underlying spectrum with its uniquely extended module action; K-localization is not presumed smashing. Rationalization is Q⊗_S−.

The height-three source H constructs W=A_2∨A_2[-1]→X, its cofiber Y, a fracture map h:U=A_1[-3]∨A_1[-4]→Y, and F_4=X×_Y U. Its middle boundary is

    d=∂_w h: U → ΣW.

The roof for ∂_w ends in minus the suspended inclusion of fib(W→L_{K(2)}W). The rational quotient is V=Q[-5]∨Q[-6]∨Q[-8]∨Q[-9]; its boundary g:V→ΣF_4 ends in minus the suspended inclusion of fib(F_4→L_JF_4). These signs and the compatibility homotopies belong to the actual construction; a proposed change of basis cannot ignore them.

O proves that the canonical rational height-two localization map out of T is nonzero in degree −3. H uses this to prove d_3≠0 for its prescribed construction. Thus replacing F_4 by the direct sum W∨U would discard a genuinely nonzero extension. Neither rationalization of that extension nor positive-height localization detects it.

The completed original i107 already kills ALL four components of g for every H-admissible choice, using both actual fracture corners, not merely the exterior algebra of L_0T. In particular its degree-five calculation is already paid. We use that conclusion, not a new calculation of the old R105/R107 target.

## 2. Mapping groups and the middle matrix

Let ΓM=F_S(Q,M), the right adjoint for a rational SOURCE. This is not L_0M. The unit-compatible calculations established in i105 are

    ΓA_1 ≃ Q[-2],
    L_1R_2 ≃ A_1 ∨ A_1[-1] ∨ Q[-3] ∨ Q[-4],
    ΓA_2 ≃ Q[-4]^2 ∨ Q[-5],
    F_S(A_1,A_2) ≃ A_1[-2] ∨ Q[-4] ∨ Q[-5].             (2.1)

These are choices of splittings, not canonical coordinates. For completeness, the last equality comes from applying F_S(A_1,−) to A_2≃R_2×_{L_1R_2}A_1: the R_2 term is zero and the remaining map A_1→L_1R_2 is the first inclusion. This makes the last mapping spectrum the fiber of that inclusion. The Γ formulas follow from the same two fracture squares and ΓR_i=0.

The height-one fracture exact sequence gives

    π_{−1}A_1=0,   π_{−2}A_1=Q_p/Z_p,   π_{−3}A_1=0.   (2.2)

Indeed π_{−1}R_1=Z_p maps injectively to π_{−1}L_0R_1=Q_p, and π_{−2}R_1=π_{−3}R_1=0. The preceding π_0 map to Q_p is surjective. These are low stems at p≥5, not a height-independent vanishing assertion.

Use row order (ΣA_2,A_2) for ΣW and column order (A_1[-3],A_1[-4]) for U. The four groups containing the components of d are

    [ Q_p/Z_p ⊕ Q_p       Q_p             ]
    [          0          Q_p/Z_p ⊕ Q_p    ].          (2.3)

For example [A_1[-3],ΣA_2]=π_{−4}F_S(A_1,A_2), and [A_1[-3],A_2]=π_{−3}F_S(A_1,A_2)=0. Formula (2.3) is only a list of allowed groups. It does not compute the entries or their normalizations. In particular H's nonzero rational comparison scalar is not asserted to be a p-adic unit.

The vanishing of the lower left group is especially useful: it says that the map d_3 factors, after choosing a nullhomotopy of that zero component, through ΣA_2. Call the resulting map

    a : A_1[-3] → ΣA_2,      P = fib(a).                (2.4)

Since d_3≠0, a≠0. Its chosen coordinates lie in Q_p/Z_p⊕Q_p. No assertion about either coordinate separately, its valuation, or a canonical orbit representative is needed below. Rationalization of a is zero by degrees. Γa is zero by degrees as well: its source is Q[-5], whereas its target is Q[-3]^2∨Q[-4]. Nevertheless a itself is nonzero. This explicitly shows why testing either rational functor alone loses the attachment.

From (2.4), exactness of Γ and a choice of nullhomotopy give

    ΓP ≃ Q[-4]^2 ∨ Q[-5]^2.                             (2.5)

The calculation uses a triangle A_2→P→A_1[-3]→ΣA_2. It is compatible with, and recovers after doubling, i105's ΓF_4=Q[-4]^2∨Q[-5]^4∨Q[-6]^2.

## 3. Paying determinant coherence by a free-module construction

A first attempt would ask whether the two columns of d are related by multiplication by ζ_3. Merely knowing ζ_3²=0 in homotopy supplies neither a coherent algebra action nor a coherent module map. Here that difficulty can be removed without an obstruction-theoretic guess.

Let H=T_∞=E_3^{hG_3^1} be the actual half-sphere and choose ψ mapping to a topological generator of the reduced-norm quotient Z_p. The primary DH construction, in the E∞ formulation recorded in BMR §5.1, identifies T with the fiber of ψ−1 on H. Restrict the continuous action to the ordinary infinite cyclic subgroup generated by ψ. Its homotopy fixed points are the same fiber, so the restriction comparison

    T → H^{hZ}

is an equivalence of underlying spectra, and hence of the E∞-rings in this construction. This use of the ordinary circle avoids silently defining continuous cochains on the non-p-complete A_2 by a discrete-coefficient convention.

Set

    C_0=F(S^1_+,S),       C=A_2⊗_S C_0.

The equivariant unit S→H gives C_0→T, and localization gives an E∞ A_2-algebra map C→X. The underlying A_2-module of C is A_2∨A_2[-1]. Its two basis maps to X are the unit and the determinant class, with the chosen generator fixing the sign of ζ. We choose H's w to be this map. Rescaling the degree −1 class by the permitted unit changes no basis assertion in H.

Now X, Y=cofib(C→X), and their boundary triangle are actual C-modules. Let h_3:A_1[-3]→Y be the first component of any H fracture lift for this w. Free-module adjunction supplies the coherent C-linear map

    h_C : C⊗_{A_2}A_1[-3] → Y.                         (3.1)

Its first underlying component is h_3 and its second is ζh_3, with the suspension convention inherited from C. At K(1), H's basis is (1,ζ,δ,ζδ); hence the two quotient classes of (3.1) are exactly (δ,ζδ). Rationally its two classes are (β_3,ζβ_3), where β_3 is the source's normalized rational generator. Thus (3.1) is still H-admissible: take its actual localized maps and their actual comparison homotopy as the input data. This is an existence construction for a compatible choice, not a claim that every independently chosen H lift was already C-linear.

Form F=C-module fib(∂_w h_C). By the free adjunction, ∂_w h_C is determined by d_3:A_1[-3]→ΣC. The lower component is the zero group in (2.3). Choose its nullhomotopy and use a from (2.4). Extending that chosen homotopy freely identifies the boundary, as a C-linear map, with

    C⊗_{A_2}a : C⊗A_1[-3] → ΣC.

Extension of scalars is exact, giving

    F ≃ C⊗_{A_2}P.                                    (3.2)

This establishes the diagonal pairing of the middle attachment with all module coherence. No assertion that C is a formal square-zero E∞ algebra is used. In a graded matrix convention the suspension can introduce a sign in the second diagonal entry; equation (3.2), with a defined from the source's signed boundary, is the sign-independent specification. There is no independent off-diagonal parameter for this chosen free extension.

The quotient Z=cofib(F→X) is rational. Its rational classes form the free module on α_5 and β_3α_5 over the exterior action of ζ. This uses the multiplicative rational algebra of X, while the map to Z is merely C-linear: no multiplication on Z is presumed. Consequently, by choosing these two classes as maps into the rational target and extending freely, there is a C-linear equivalence

    t : C⊗_{A_2}(Q[-5]∨Q[-8]) → Z.                    (3.3)

The underlying four classes are exactly the H quotient basis. The new construction is therefore among the H choices covered by completed i107. That result makes the underlying boundary ∂t zero as an S-module map.

Forgetting a general C-linear map can lose information. In (3.3), however, the source is FREE. Adjunction identifies its C-linear homotopy class with the two generator restrictions

    [Q[-5]∨Q[-8], ΣF]_{A_2}.

Both restrictions are zero because the underlying boundary is zero. Thus this boundary is actually null as a C-linear map. Splitting its triangle yields the reduction

    X ≃ C⊗_{A_2}M,
    M = P ∨ Q[-5] ∨ Q[-8],
    A_2 → P → A_1[-3] --a--> ΣA_2,   a≠0.              (3.4)

The equivalence is C-linear and can be taken under C. It depends on the displayed choices and nullhomotopies. This is not a ring equivalence, not a uniqueness statement, and not an identification of M with the half-sphere.

Everything used to reach (3.4) is an actual source/history construction or a free-module adjunction: DH/BMR supply the coherent determinant action, H supplies h_3 and the bases, i105 supplies the zero component, and i107 supplies the full tail nullity. The enhancement is recorded because it closes a tempting coherence gap rather than leaving that gap as a purported novelty. It does not supply a nonroutine new bridge for nomination.

## 4. What (3.4) actually reconstructs from the half-sphere

There is a precise categorical form of the remaining comparison, stronger than the vague instruction to “lift the determinant action.” Let D=Fun(BZ,Mod_{A_2}), with the chosen discrete ψ action, and let u be A_2 with trivial action. Then

    End_D(u)=C,        Γ_Z(N)=Map_D(u,N)=fib(ψ−1:N→N).

The corresponding adjunction is

    L : Mod_C ⇄ D : Γ_Z,       L(B)=u⊗_C B.             (4.1)

Because BZ has the finite cell model S^1, Γ_Z is a finite limit in a stable category and preserves colimits. Both Γ_ZL and the identity preserve colimits, and their unit is an equivalence on the free generator C. Hence the unit B→Γ_ZL(B) is an equivalence for every C-module B. This proves that L is fully faithful; it is not an assertion that every Z-object lies in its image.

Take H_2=L_2H as a Z-object. Exact localization and the actual DH fiber identify Γ_ZH_2 with X, including its C action. The counit of (4.1) gives a canonical comparison once X is identified with its fixed points:

    ε : L(X) → H_2,      N=cofib(ε).                   (4.2)

Applying Γ_Z to the counit is an equivalence by the unit calculation and the adjunction identities. Therefore

    Γ_ZN=0,      ψ−1:N→N is an equivalence.             (4.3)

Under the choices of (3.4), L(X) is M with trivial Z action. Thus (4.2) is the concrete comparison

    (P∨Q[-5]∨Q[-8])_{triv} → L_2H,

and (4.3) states exactly what the entire source filtration and its determinant module structure leave undetected.

A complete identification with H_2 would require the cone N in (4.2) to vanish, with compatibility for the original continuous Z_p action rather than only its restricted Z action. Equivalently, for the discrete comparison one must show that H_2 belongs to the localizing subcategory generated by the trivial A_2 representation. Equation (4.3) alone does not prove this. All exact finite tests commuting with Γ_Z still give zero fixed points on their image of N; applying the same fixed-point test again cannot supply conservativity.

This is an identifiable residual object and map, not a claim that the actual N is nonzero. No counterexample to the desired comparison has been constructed. Nor is the half-sphere conjecture being renamed and proposed anew: its old scope remains immutable. This calculation identifies why the module-level closure is insufficient for a distinct full-scope result.

## 5. Test against the strongest primary completion comparison

The October 7 BMR version is stronger and later than the August version cited in the supplied manuscripts. Its proof constructs an actual equivariant E∞ map B→Bhat, from the spectral deformation of a separable extension L to that of its completed perfection Lhat. Its two-tower computation gives, before the tame norm quotient,

    k → (Lhat)^{hSG_h} → k(-1)[-h].                   (5.1)

This is a triangle, not an assertion of formality. The residual tame norm acts on the last line with weight 1−h. For h=3 and p≥5 this is nontrivial, so exact tame averaging eliminates the line. Derived Nakayama then gives the E∞ equivalence with the COMPLETED proxy. Coheight-one Morava descent turns this into a retraction of the actual half-sphere unit. It does not itself replace B by Bhat before fixed points.

BMR Proposition 5.3.8 explicitly reduces the actual-to-completed comparison to an acyclicity assertion on the relevant graded coefficient modules. At height two the paper pays that assertion. No height-three all-coefficient comparison was imported here from its height-two proof.

In the present notation, a successful use of that primary route would have to compare the actual B-cochain descent diagram with the completed diagram while controlling the ψ action on the cone (4.2). H's distribution and finite-stage arguments do pay the ordinary P-cochain comparisons used in X. P-cochains already include the norm quotient. They therefore compute Γ_ZH_2; they do not automatically recover the norm-one cochains before that quotient. One must either supply a contraction of the residual norm-one complex compatible with all coefficient stages and ψ, or establish a conservative completeness property that kills (4.3). Neither operation is proved by the present reductions.

The distinction is testable at the chain level. In a two-term norm resolution the residual cochains have the form

    [N --(ψ−1)--> N].

Its acyclicity means invertibility of the displayed map. A contraction of this two-term complex can use (ψ−1)^{-1}, and therefore does not contract N. To prove N=0, a separate operation on the underlying norm-one object is necessary. Replacing a two-term contraction by such an operation is exactly the missing implication. No new quantitative bound or descent exponent has been claimed to make it automatic.

## 6. Prime three: isolate what the generic detector can split

In this section p=3 only. Use P's finite unramified constant extension S_k, Z_k=L_{K(3)}S_k, its diagonal detector, O_x=k[[x]], F_x=k((x)), and G_F=O_F^× for the unramified quadratic extension F/Q_3. To avoid confusion, F_x is the generic coefficient FIELD and F in G_F is the quadratic p-adic field. Let ωbar be the actual periodicity line after extension to F_x and let δ be the residue norm G_F→F_3^×.

P proves, through every x-jet before passage to F_x, the four cohomology rows

    s=0,1 : ωbar^j;
    s=3,4 : F_x(δ)⊗ωbar^j.

Its exact finite abutment filtration gives

    0→δωbar^{r+2}→V_{2r}^Δ(Z_k)→ωbar^r→0,
    0→δωbar^{r+1}→V_{2r−1}^Δ(Z_k)→ωbar^r→0.           (6.1)

The source itself does not assert a splitting. The key obstruction δ≄ωbar^b for every integer b is already proved there using the entire principal-unit action, F_x^{G_F}=k, and the valuation-one Hasse invariant h∈ωbar^2. Restricting just to μ_8 loses that proof. A nonzero equivariant F_x-linear map between distinct rank-one lines is impossible; vanishing of such Hom groups is not vanishing of Ext^1.

There is more structure available for these particular lower quotients than an arbitrary extension of lines. The actual unit provides the lower row-zero class. The DH determinant class provides the lower row-one class. Here the mod-three normalization is important: P §7 uses a continuous section of reduced norm on 1+3Z_3 built from an unramified cubic element of trace one. Its cohomology in degrees one and four uses the SAME nonzero Hom_cts(1+3Z_3,F_3) generator. Thus normalized ζ_3 restricts to a nonzero generator, not three times a generator. This is read from the actual norm quotient calculation, not inferred from the height being three.

The canonical map C⊗_S S_k→L_2Z_k, with C the localized circle cochains as in §3, can be tested by P's exact functor and diagonal projection. In degree 2r its unit summand maps to the generator of the row-zero quotient in (6.1). In degree 2r−1 its ζ summand maps to the generator of the row-one quotient. Naturality of the cochain comparison identifies these edge maps with the identity after the fixed normalization. Coefficients in all even degrees are obtained from the actual E_2 periodicity line, so these are F_x-linear equivariant maps of the lines ωbar^r.

Consequently each of the particular sequences (6.1) has a section supplied by this actual lower-row map. This is a detector-level consequence of unit, ζ, and the source's natural spectral sequence, not a general inference that distinct characters split all extensions. No splitting was extracted from dimensions alone.

Let D_k=cofib(C⊗_S S_k→L_2Z_k). Degreewise injectivity of the tested map and the long exact sequence give the exact generic coefficient descriptions

    V_{2r}^Δ(D_k) ≅ δωbar^{r+2},
    V_{2r−1}^Δ(D_k) ≅ δωbar^{r+1}.                     (6.2)

Cup product by the reduced-norm class identifies the row-three line with the row-four line in P's two-term quotient resolution. The coefficient comparison is compatible with multiplication by this constant cochain. Hence ζ carries the odd line in degree 2r−1 isomorphically to the even line in degree 2r−2. It kills the even upper line. For the latter assertion the target has no higher filtration; for the former the induced map on the single remaining quotient is an isomorphism. On the lower two lines ζ maps the even generator to its odd partner and then to zero. The normalization can be chosen so these two nonzero maps are identities of the displayed lines; changing ζ's sign changes both together.

Thus the generic representation, with its ζ action, has two exterior pairs: the unit pair in degrees 0,−1 and a δ pair starting in degrees −3,−4. This removes an apparent unknown generic extension. It does not give a spectrum representing the second generator. In particular the distinguished element of V_{−3}^Δ(D_k)=F_x(δ) is not an element of π_{−3}D_k and cannot be treated as a map from the sphere.

## 7. The integral realization problem after the generic calculation

To turn (6.2) into a spectrum-level attachment description, one would need an actual integral source object and an actual map whose tested class is the δ generator, with both:

1. compatibility with every cooperation coface and degeneracy, through every x-jet and then through the p-adic levels;
2. compatibility with the full G_F action (including principal units), the norm action, and passage back from the test to the E(2)-local fracture diagram.

No such source object or map is constructed here. Adding a formal symbol for a δ line to the list of generators would leave precisely this operation unpaid. P's all-jet quasi-isomorphisms identify the existing spectral sequence; the source explicitly does not need a separate spectral realization of those coefficient maps. That feature is sufficient for its finite-assembly obstruction and insufficient for the new realization request.

One can see a concrete failure of a tempting shortcut before tackling those higher coherences. An F_x coefficient f representing a generic section can have a pole in x. Multiplication by x^m clears that pole but does not preserve the same equivariant map: for g∈G_F the new discrepancy is the factor g(x^m)/x^m. The nontrivial semilinear action is precisely what the source retained through all jets. A finite-residue-character projector is likewise not an F_x-linear projector for the full semilinear action. Thus neither “clear denominators” nor “average the character” transports (6.2) to the required integral map.

A further independent obstruction to reversing the detector is its exactness versus conservativity. The detector kills rational and height-one objects. Even a realized K(2)-local map with the desired generic homotopy would leave rational and height-one gluing data to specify; (6.2) cannot determine them. The generic field step also discards x-power torsion. Neither the source finite-assembly failure nor the generic decomposition gives uniform torsion bounds with which to reverse these losses.

This is not an assertion that a suitable twisted object cannot exist. It is also not a proposed finite-assembly theorem with extra generators, a Picard consequence, or a claim at any other prime. The full operation has not closed.

## 8. Descent exponents: check the correct category before transferring a bound

W uses an actual unit kernel z=β_1^{(p−1)^2}, detected at height h=p−1 by the finite-subgroup HFPSS. Heard's primary calculation has positive even E∞ term

    F_p[Δ^{±p}][β]/(β^{(p−1)^2+1}),

so β^{(p−1)^2} survives. Its actual unit image is β_1 to a nonzero scalar. At the upper heights a=p (p≥5) and a=p+1 (p≥7), W's multiplicative Adams filtration and strong horizontal bound kill that power. The inequalities are

    2(p−1)^2 − (p^2+2) = p(p−4) ≥ 0       (a=p),
    2(p−1)^2 − ((p+1)^2+2) = p^2−6p−1 ≥ 0 (a=p+1,p≥7).

These compare with F^{a^2+2}=0, not with an unproved exact numerical nullity exponent of the Adams map. W separately pays actual finite descent using its sphere/no-phantom and exact-test constructions. The finite-group detector, upper-height vanishing, and transport through the same unit are all already part of its proof.

The 2^n-stage filtration in G is in modules over the derived complete sphere; its cofibers are different chromatic localizations. It is not by itself an A-module resolution in the symmetric monoidal category in which a proposed A-based exponent is defined. MNN's exponent characterization uses the actual maps I^{⊗s}⊗M→M for I=fib(1→A). An exact test carries finite diagrams and chosen nullhomotopies, but need not identify T(I^{⊗s}) with T(I)^{⊗s}. Therefore counting the G stages cannot manufacture the missing tensor comparison.

The source's finite-cube quick convergence DOES justify exact-functor passage through its specific Adams/Amitsur limits, and this stronger operation was used rather than rejected. After that payment the remaining numeric-exponent proposal still needs a monoidal identification or an explicit compatible nullhomotopy in the target category. No such new bound was derived. The related a^2+1 refinement in completed i105 is already paid and was not retried.

## 9. Prefreeze disposition

The strongest construction retained here is (3.4), together with the exact counit cone (4.2)–(4.3), and the generic δ-pair isolation (6.2). The first resolves the apparent determinant-module coherence issue by free adjunction; it does not resolve the half-sphere residual. The second resolves the generic lower-row extension by actual unit/ζ sections; it does not realize the δ generator integrally as a map of spectra. The descent calculation identifies the missing tensor interface rather than substituting a stage count for it.

There is no frozen theorem, author-proof nominee, new small-prime claim, explicit exponent bound, retry of an old target, or general impossibility assertion. The closed steps above are retained as calculations; the unpaid operations are the specified residual-cone vanishing/continuous comparison and integral full-cooperation realization. No distinct full-scope operation with all those interfaces closed emerged in this round.
