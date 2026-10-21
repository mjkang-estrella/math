# r145 — concrete dimension-reduction calculations (PREFREEZE)

These are research derivations, not a frozen theorem or an author-proof nominee. The one family is Source046. Both counterexample headlines and all operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are premises. The operation investigated is retaining smooth projectivity, largeness, and failure of holomorphic convexity in a threefold descended from the source fourfold. No earlier frozen scope is changed. Statements below that follow from source/classical operations are diagnostic payments, not proposed contributions.

## 1. Exact source input and the obstruction to preserve

Write X for the smooth connected projective fourfold of Source046, A⊂X for its embedded simple abelian surface, and Γ=π1(X). The inclusion has image an infinite cyclic subgroup C⊂Γ, not an injective rank-four abelian subgroup. With A=ℂ²/Λ, Λ≅ℤ⁴, its kernel K⊂Λ has rank three and Λ/K≅ℤ. For the universal cover p:U→X, a component of p⁻¹(A) is the connected cover

    A_K = ℂ²/K → A.

It is a closed complex submanifold of U. Closedness is important: components of the inverse image are locally separated sheets, so each component is closed, not merely an immersed leaf. Its underlying real manifold is ℝ×(S¹)³. Thus H₃(A_K,ℤ)=ℤ, and the Stein surface homotopy-dimension theorem already gives non-Steinness. The source also proves U has no positive-dimensional compact analytic subvariety. Its proper Remmert reduction, if it existed, would have finite fibers, hence make U Stein. This is the source's paid route from non-Steinness to failure of holomorphic convexity.

For the reductions below it is useful to verify the stronger, classical function-theoretic description O(A_K)=ℂ. This does not create a new candidate.

Put W=spanℝK, a real hyperplane in ℂ², and V=W∩iW, a complex line. On any translate of the real torus T=W/K, expand the restriction of a holomorphic function in Fourier characters m∈Hom(K,ℤ), viewed as real linear forms on W. The tangential Cauchy–Riemann equations along V give, for a nonzero Fourier coefficient, m(v)=m(iv)=0 for all v∈V: the two coefficients are real and the complex CR relation forces both to vanish. If m≠0, ker(m)=V is a rational two-plane for K. Then V/(V∩K) is an elliptic curve embedded in A, contradicting simplicity. Every Fourier coefficient except the constant therefore vanishes. The function is constant on each translated T. Its complex-linear differential vanishes on W; a complex-linear functional on ℂ² vanishing on a real three-plane is zero. It follows that the function is constant on connected A_K.

Consequently all functions on U have the same value on A_K. For any a∈A_K, the holomorphic hull of {a} contains all of A_K and is noncompact. This directly preserves failure of holomorphic convexity whenever the same closed analytic A_K is retained. It is stronger than merely carrying a real 3-cycle, which need not obstruct Steinness in a complex threefold.

## 2. The constrained hypersurface and its exact defect

Fix an ample line bundle L on X, write h=c₁(L|A), and E=N_(A/X), of rank two. For m sufficiently large, a general section of I_A⊗L^m defines a hypersurface Z_m containing A. Serre generation of the normal first jets gives a general normal derivative

    σ ∈ H⁰(A,E*⊗L^m|A).

It is transverse to zero. Away from A, Bertini gives smoothness. At a zero of σ, write the defining equation as xa+yb=0 with A=(x=y=0). Transversality means a,b restrict to local coordinates on A. Thus x,y,u=a,v=b are ambient coordinates and the exact local model is

    Z_m: xu+yv=0,       A: x=y=0.                 (2.1)

No unproved higher-order normal-form elimination is needed here. These are ordinary threefold nodes. Their number is

    δ(m) = ⟨c₂(E) − m h c₁(E) + m²h²,[A]⟩.      (2.2)

Indeed the Chern roots of E*⊗L^m are mh−e₁,mh−e₂. Since ⟨h²,[A]⟩>0, δ(m)>0 for every sufficiently large m. The high-degree regime used to obtain jet generation therefore does not remove the singularities. This is a statement about this generic constrained construction; it says nothing about every possible embedding or special low-degree section.

The hypersurface is connected (ampleness) and normal (isolated hypersurface singularities in dimension three). It is irreducible: distinct three-dimensional components in a smooth fourfold would meet in dimension at least two, inconsistent with isolated singularities and connectedness.

Deform Z_m inside its complete linear system to a smooth ample hypersurface H_m. The link of (2.1) is S²×S³, the Milnor fiber retracts to S³, and a small-resolution neighborhood retracts to S². These three spaces are simply connected. Removing disjoint node neighborhoods and applying van Kampen gives, compatibly with the maps to X,

    π₁(Z_m) ≅ π₁(H_m) ≅ π₁(X)=Γ.               (2.3)

The second isomorphism is ordinary Lefschetz. In particular the map from A into Z_m still has image C≅ℤ.

The normal projective Z_m inherits largeness in the normalization-of-subvarieties sense: a positive-dimensional irreducible subvariety has the same composite fundamental-group image in X, which is infinite. Its universal cover contains the same closed A_K, and the preceding hull argument applies. This singular diagnostic is paid by the source's cut-and-node operations; it is not a weakened replacement for the smooth target.

## 3. Use the source's strongest resolution, not just a naive blowup

Source046's lemma `lem:ambient-blowdown` already constructs a projective small resolution that leaves the surface unchanged. Choose a sufficiently ample Cartier divisor on Z_m containing A, with general first-order equation x at every node, and write it A+R. Locally R=(x=v=0). Blow up its coherent ideal (x,v). The two charts are

    x=tv, y=−tu       with coordinates (t,u,v),
    v=sx, u=−sy       with coordinates (s,x,y).

The strict transform A′ is t=0 in the first chart and misses the second; thus A′→A is an isomorphism. The charts are smooth, and the blowup is projective. Denote the result q:T_m→Z_m. Its exceptional curves E_j are ℙ¹, one per node. They meet A′ transversely in one point, and the same van Kampen calculation gives π₁(T_m)≅Γ compatibly with A′.

The universal cover of T_m contains a closed A_K and therefore is not holomorphically convex. But every E_j has trivial fundamental-group image. In fact these are exactly the irreducible positive-dimensional subvarieties of T_m with finite image: if V is not contracted by q, the normalization of V has the same function field as its image in Z_m, and the birational map to the normalization of that image induces a surjection on fundamental groups. The latter image in Γ is infinite by largeness of X. This surjection can also be seen by lifting loops off the proper exceptional subset and using normality to perturb them. If q(V) is a point, V is one of the exceptional curves. Thus the resolution localizes the failure of largeness to finitely many rational curves, but it does not eliminate it.

This entire resolution operation is already paid in the primary source. An alternate small resolution or its flop still has a compact ℙ¹. Higher resolutions add exceptional subvarieties. Contracting exactly the exceptional ℙ¹s returns the nodes. These observations do not exclude other global constructions.

## 4. Finite branched covers cannot smooth this nodal model

There is a stronger local obstruction than the failure of an unramified cover. In the local normal ring of (2.1), the Weil divisor D=A has infinite order modulo Cartier divisors.

To see this without merely naming the local class group, use the preceding opposite small resolution. Its strict transform D′ is Cartier and meets its exceptional ℙ¹ transversely in one point. Hence

    deg O(D′)|ℙ¹ = 1.

If mD were Cartier for an integer m>0, its pullback line bundle would have degree zero on the contracted ℙ¹. Because the resolution is small, it has no exceptional divisors; the pullback Cartier divisor is therefore exactly mD′. Its degree is m, a contradiction. Thus D is not ℚ-Cartier.

Now suppose a finite surjective map f:Y→Z_m existed with Y smooth. Localize at a node and take the semilocal ring of Y above it. It is regular. The divisor pullback f*D is Cartier, and every invertible module over this semilocal ring is free, so f*D is the divisor of a rational function g. For the finite extension of function fields of degree d, the valuation formula for the norm gives

    div Norm(g) = f_*div(g) = f_*f*D = dD.

This makes D ℚ-Cartier, a contradiction. The same argument applies to a connected component dominating the irreducible germ. It covers ramified as well as quasi-étale finite morphisms, and does not assume flatness. In the quasi-étale case one has the additional elementary obstruction that the punctured node is simply connected.

This is a local diagnosis of this Z_m; it is not an impossibility theorem for branched constructions over a different smooth base. In particular it does not invalidate Stover–Toledo, Llosa Isenrich–Py, or the surface manuscript. Their finite-cover operations have other local hypotheses. Source046's surface proof first detects complete finite commuting local meridian groups and then resolves. Such a procedure need not be a finite map from a smooth space to Z_m, and a subsequent resolution can introduce precisely the compact curves forbidden here.

Finite étale base change of the entire pair (X,A) does not cure (2.2). On any connected component A′ above A the normal data pull back, so δ′(m)=deg(A′/A)δ(m)>0 in the same high-degree regime. It preserves the original universal-cover obstruction, but preserves this derivative obstruction too.

## 5. Smooth the threefold: what is and is not preserved

A general H_m∈|L^m| is already smooth, projective and large: every positive-dimensional subvariety is one of X's subvarieties, and Lefschetz identifies π₁(H_m) with Γ. Thus largeness is not the missing step on the smoothing branch. The missing step is failure of holomorphic convexity of its universal cover.

An exact local obstruction prevents treating A as an unchanged divisor during a smooth-total-space smoothing. Suppose a one-parameter smoothing 𝒵→Δ has smooth total space near a node and has a flat family of effective surfaces 𝒜⊂𝒵 whose central cycle is mA, with no additional components, m>0. The total 𝒜 is a codimension-one Weil divisor on a smooth space, hence Cartier. Flatness excludes a component equal to the central fiber. Restricting its Cartier divisor to the central fiber makes mA Cartier at the node, contrary to §4. This rules out that precise persistence mechanism, including multiplicity. It does not rule out every base change with singular total space or a replacement obstruction.

The available stronger alternative is to add a residual divisor: locally

    div(x) = A+R,       R=(x=v=0).

The class of R cancels the class of A. The Cartier sum can participate in a deformation, so one must not claim that every surface-like central cycle is unsmoothable. What fails to follow is preservation of the cyclic image and the closed Cousin surface A_K.

The gluing locus cannot simply be avoided by choosing another representative of the old real 3-torus. Let C=A∩R, with its effective divisor structure on A. It is nonzero (near each node it contains v=0 in the (u,v)-plane). Every nonzero effective divisor on a simple abelian surface is ample. Let η be the translation-invariant positive (1,1)-form representing c₁(O_A(C)). Its restriction to the real hyperplane W has rank two: a symplectic form on a real four-space cannot vanish on a three-plane. Therefore

    i* c₁(O_A(C)) ≠ 0 in H²(A_K,ℝ),
    i* c₁(O_A(C)) ∩ [T] ≠ 0 in H₁(A_K,ℝ),      (5.1)

where T=W/K generates H₃(A_K). On A_K minus the lifted divisor, the pulled-back line bundle is trivial, by its canonical nonvanishing section. A compact 3-cycle disjoint from that divisor would therefore have zero cap product in (5.1). No representative of [T] can be chosen wholly off the gluing divisor.

This shows why the obvious 'transport the torus away from the surgery' argument is unavailable even after the compatible Cartier cancellation. It does not assert that every homology class dies in every smoothing, nor would survival of a real H₃ class in a three-dimensional complex manifold alone prove non-Steinness.

## 6. A stronger analytic reduction using the actual extension proof

Let H=H_m be a general smooth high-degree section and C=A∩H a smooth ample connected curve. Lefschetz on A gives π₁(C)→π₁(A) surjective; hence its image in Γ is the same infinite cyclic C (the curve and the subgroup are distinguished by context). The inverse image of H in U is connected and simply connected by π₁(H)≅Γ; call it U_H. The connected cover C_K of the curve inside A_K is a closed, noncompact Riemann surface in U_H. It is connected because π₁(C)→Λ/K is surjective.

If restriction O(U)→O(U_H) were surjective, every function on U_H would be constant on C_K by §1, and the hull of a point of C_K would be noncompact. Full extension is therefore a concrete sufficient operation, not just an unspecified appeal to deformation stability. It is stronger than necessary: one only needs every function on U_H to be constant on C_K.

The actual sheaf sequence identifies the extension obstruction:

    0 → p*L^(−m) → O_U → O_(U_H) → 0,
    ∂: O(U_H) → H¹(U,p*L^(−m)).                 (6.1)

The developed primary reduction is stronger than leaving (6.1) as a named vanishing problem. Lárusson's 1995 Theorem 3.1 and 2000 Theorem 1.2 apply to a smooth weight φ with bounded differential, provided

    m Θ_L ≥ i∂∂̄φ + εω,     ε>0.               (6.2)

They identify the weighted L² holomorphic-function spaces on U and U_H. The original proof was read: extend locally constantly in the normal coordinate, divide local differences by the defining section s to obtain an L^(−m)-valued Čech cocycle, use a partition of unity to obtain a closed (0,1)-form, bound it by local Cauchy estimates and bounded dφ, solve ∂̄ in weighted L², and subtract the solution times s. Negative-bundle L² vanishing follows from positive-bundle vanishing by closed-range duality. The 2000 improvement proves uniqueness by showing F/s is also L² and applying degree-zero vanishing. It is not an unweighted H¹ vanishing theorem.

Choose a smoothed distance τ on U with bounded differential and Levi form, and e^(−aτ) integrable for some a>0. For any fixed b>a, sufficiently large m gives (6.2) with φ=bτ. Every f∈O_(bτ)(U_H) extends and is constant on C_K. In particular all bounded functions on U_H are constant on C_K. This gives a noncompact hull for the bounded-function algebra and for this fixed weighted space. Such a hull is not the hull for all holomorphic functions; it does not establish failure of holomorphic convexity.

The curvature budget is explicit. If Θ_L≥λω and i∂∂̄τ≤Mω with λ>0 and M≥0, the sufficient inequality is

    mλ > bM.

For M>0 this pays a specified finite range b<mλ/M, not arbitrary growth for a fixed H_m. If M=0, all exponential weights may pass this particular curvature estimate, but functions need not have any finite exponential-growth bound. No such exceptional M=0 exhaustion is claimed for U. Increasing m changes H_m; one cannot interchange 'for each growth rate choose a section' with 'one section handles every function'. Choosing a new weight adapted to an arbitrary function also loses the bounded-gradient/curvature budget.

There is a directly compatible primary control for the density shortcut. Lárusson 2000 Example 1.3 takes a cyclic cover of an abelian surface with no nonconstant holomorphic functions, and a sufficiently positive curve. Its slow-growth holomorphic functions are constant although the open Riemann surface has nonconstant holomorphic functions. Our A_K and sufficiently ample C_K have exactly this source of the distinction. Constants are closed in the compact-open topology, so no general density theorem for the prescribed slow-growth class can repair the missing step. This does not prove density fails in every possible class on U_H; it prevents importing such a principle without an additional operation.

Thus the paid analytic reduction reaches all functions in an actual, quantified weighted class on a smooth large threefold's universal cover. The unpaid operation is control of the remaining functions on the same U_H, at least on C_K. This is retained as a precise reduction, not nominated as a conditional or growth-restricted substitute.

## 7. Finite covering operations compared at their strongest scope

Lárusson 1995 Proposition 4.1, including its proof, provides a useful counterweight: every smooth projective manifold is finitely dominated by a smooth projective manifold with Stein universal cover. The construction uses a high-degree complete intersection in a product with a product of hyperbolic curves. The latter has a positive line bundle with a bounded trivialization upstairs. Finite pullback preserves this property; the negative logarithm of the trivialization norm, augmented by a smoothed distance, yields a strictly plurisubharmonic exhaustion. Thus arbitrary branching can destroy the desired obstruction even over the smooth source X. It cannot be treated as harmless covering bookkeeping. This operation is an actual paid primary result, not a new dimension-reduction result and not a contradiction of the local non-ℚ-factorial obstruction in §4.

The source fourfold's virtual branching is along separately smooth, disjoint components of each labelled divisor, with compatibility enforced on a common cover. Stover–Toledo's residual-finiteness/cup-product and divisibility arguments and the good-pair statement of Llosa Isenrich–Py were read at their operative interfaces. They do not assert that a node with non-torsion Weil class has a finite smooth cover. Likewise Eyssidieux–Funar's fixed-rank linear-cover convexity and stable-family constructions do not supply a representation that is infinite on the required cyclic image while retaining the nonconvex cover. Their finite local groups and compact lifted destabilizing chains belong to a different geometry.

The separate surface manuscript has a noncompact connected union of compact rational curves in its universal cover. Each function is constant on each rational component, hence on the connected string. Its weighted Golod–Shafarevich construction proves that this string is infinite. This is a powerful obstruction to convexity, but inserting those rational components into a would-be large example immediately violates largeness. No large-group or no-compact-subvariety assertion is transferred to that surface.

## 8. Original-history comparison and outcome

The actual original sections read include the complex-Kähler full targets in i98, the smooth-versus-normal transport in arithmetic r17, the relative topological operations in i97, the K3 relative problem in i102, the cone-deformation/all-order construction in i31, and the holomorphic-versus-symplectic blowdown comparison in i74. None pays the exact missing operation in §6. In particular the i31 all-order negative-weight deformation mechanism operates with Cartier/formal data and algebraization over its specified base; naming it does not produce a compact projective smoothing that retains A_K in this node calculation. The i97 and i74 topological/symplectic operations do not confer persistence of a closed analytic subspace. Their original full targets remain immutable.

The completed arithmetic r144 exception was read and preserved: its rank-two presentation and terminating all-rank reduction are paid; the undeformed generic flavor obstruction differs from the compatible deformed ideal; uniform geometric/Hall comparison for its specified filtration remains unpaid. It is not repurposed here. Supplied S176A, analytic161/166 and T054L136 dispositions are unchanged and their excluded bodies were not read.

No viable full-scope theorem was frozen. The outcome is PREFREEZE/no nominee, supported by the exact node count, the projective resolution and group comparison, the finite-map norm obstruction, the Cartier-cancellation test and torus intersection, and the weighted extension reduction. This is a failure to close the specified operation in this round, not exhaustion of Source046, a global impossibility claim, an acceptance decision, or a mathematical self-grade.
