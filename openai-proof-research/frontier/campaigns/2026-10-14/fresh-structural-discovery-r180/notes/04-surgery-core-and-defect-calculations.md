# r180: carrying the nonlinear test through surgery and geometric localization

Everything here is prefreeze. The object M_q, q=x1x2, is the exact model of note 03. The objective tested is distinguishing it, without marking restrictions, from the source's linear models. No claim of distinction is made.

## 1. The boundary cochain is exact; its quadratic variation is not odd monodromy

For every label a_s define the gluing exponent

    e_c(b,s)=c(b+a_s)+c(b).

For any sequence a_1,…,a_k of panel-label steps with sum zero, telescoping gives

    Σ_{j=1}^k e_c(b+a_1+⋯+a_{j-1},a_j)=0.                   (4.1)

In particular the four corner gluings around a two-panel square have zero total exponent. This is also why the orthant charts glue correctly. For q=x1x2, on the quotient A/U≅F2² its values at 00,10,01,11 are 0,0,0,1. The two horizontal differences are 0 and 1; the two vertical differences are 0 and 1. Their sum around the square is 0. On the other hand

    D_aD_b q = x1(a)x2(b)+x2(a)x1(b).                       (4.2)

For the two basis directions this is 1. Formula (4.2) compares parallel gluing jumps at different base labels; it is NOT deck monodromy around the square. Treating it as monodromy would incorrectly produce an odd cyclic filling from an actual manifold already constructed by (3.1). Thus the strongest source odd-cover obstruction does not fire on this coboundary.

The natural comparison h_c,d=f_d^{-1}f_c is an actual homotopy equivalence in the homotopy category, with the specified common Π-marking. It has zero Whitehead torsion because Wh(Π)=0. Its existence does not imply that a chamberwise map j_d^{-1}j_c has boundary extensions: homotopy inverses of relative graph-filling equivalences are not homeomorphisms.

## 2. The full marked assembly calculation closes, but gives s-cobordism

Let L⟨1⟩ be the connected quadratic L-spectrum, with the orientation twist when appropriate. Here the models are orientable. Since BΠ≃Q2 has dimension four and Π satisfies Farrell–Jones,

    H_4(BΠ;L⟨1⟩)→L_4(ZΠ) is injective,
    H_5(BΠ;L⟨1⟩)→L_5(ZΠ) is surjective,
    Wh(Π)=0.

For clarity the connective comparison uses the cofiber L_{≤0}: its homotopy groups vanish in positive degree, and H_5(BΠ;L_{≤0})=0 by dimension. This is the operative KL Lemma 2.3 argument, not an appeal to a four-dimensional geometric structure-set bijection.

Under the normal-invariant identification, the surgery obstruction of the homotopy equivalence h_c,d is zero. Its normal invariant maps to zero under the injective assembly composite, so it is zero. Because M_d itself is K(Π,1), the intermediate comparison H_4(M_d;L⟨1⟩)→H_4(BΠ;L⟨1⟩) is an isomorphism: there is NO residual spherical kernel and no unstated normal-invariant repair. Obtain a normal bordism to the identity. Use a relative normal self-bordism of M_d×I with opposite L_5 obstruction; surjectivity gives it. Stacking cancels the obstruction. Five-dimensional surgery yields a TOP s-cobordism W_c,d with the specified end homotopy equivalence. This is precisely Khan's map-level proof, not merely an unmarked existence statement.

Thus ordinary normal invariants, this assembly obstruction, and the marked s-cobordism class do not distinguish the quadratic model from the linear models. In particular, selecting a different normal invariant is not a mechanism available to this test.

The stable product operation already read in PD/stable gives a product after adding finitely many S²×S²×I along arcs. On the ends this adds free hyperbolic modules, with the original markings retained in the stated stable realization. No numerical bound, coherent action on the stabilization, or removal of the added handles follows. For each ONE comparison, existence of some finite stabilization is enough for the paid reduction. Asphericity is asserted only BEFORE stabilization; the stabilized manifolds have nonzero π2.

## 3. Carry the bordism to its strongest actual core interface

Quinn's original 2004 cores preprint was read in full, including Theorem 2.2, the immersed Whitney/accessory handle construction, the dual-decomposition step, arbitrary-core insertion, and the controlled criteria in §4. Apply Theorem 2.2 to W_c,d and an embedded finite graph Y⊂M_c surjecting onto Π. Such a graph is obtained by choosing a finite generating family and embedded arcs in the four-manifold. The result is a decomposition

    M_c=U∪N_0,     M_d=U∪N_1,
    W_c,d ≅ (U×I) ∪_{∂N×I} W^5,

where W^5 is a smooth regular neighborhood of a graph and both N_i are smooth 2-handlebodies whose spines homotopy 2-deform to that graph. The inclusions Y→N_0 and U→M_c−Y are homotopy equivalences. The core construction works even when the original bordism is only topological.

This is more than saying “s-cobordism is hard”: it moves all the failure of a product into a specified kind of graph core with unchanged outside product. Yet the construction does not identify N_i with the original panel chambers V_b. In its proof the actual Whitney/accessory handles first have exact prescribed boundaries. Dual decomposition produces π1-negligible embedded handles with HOMOTOPIC boundaries, sufficient for the core but not sufficient for a product. In dimension five those homotopies become handle isotopies; on the four-dimensional end they do not give the relative chamber homeomorphisms required by note 03.

Quinn's §3.3–3.7 also prevents a false invariant: any chosen core can be inserted into a product, and graph sums can make a core arbitrarily more complicated without changing the ambient bordism. Therefore counting handles or the apparent complexity of a core extracted from W_q,ε cannot distinguish M_q from Mε. The ambient embedding and relative boundary identification must remain part of any obstruction.

The controlled statement is more precise. There is a fixed positive δ_0 for the specified unit-edge graph convention such that an induced core equivalence N_0→N_1, together with a δ_0-controlled equivalence N_1→Y and a δ_0-controlled relative equivalence of the ends, gives a topological product. Our surgery calculation supplies an UNCONTROLLED core equivalence, and neither its normal invariant nor its chain equivalence supplies these simultaneous control estimates. Applying this to a source pair already known nonhomeomorphic shows that a universally valid automatic control improvement cannot be assumed. That is a paid source-plus-classical consequence, not a new counterexample to a specific quantitative assertion.

## 4. Why the operative reflection transfer does not silently close the interface

PD's controlled removal is retained in its full strength. It starts from a model of a specified reflected PD complex and uses a labelled stabilized middle module, periodic homotopies, shelling of finite chamber regions, protected duals, and contractible direction patches to construct a marked graph filling. It is not a functor taking an arbitrary homeomorphism between models to homeomorphisms of the original chambers.

For M_c the source target is always Q2, whose chamber P2 already has a graph filling. Running the reflection transfer therefore returns an allowed filling of S2. Its output carries no theorem identifying it with a prescribed copy V_b, let alone identifying all such copies simultaneously or recovering their c-values. Inserting the derived s-cobordism W_c,d changes neither this fact nor the odd/even cover data. The equations in §1 show exactly why no odd cover is introduced by the nonlinear pattern.

DHHRS's actual characteristic-cover mechanism has also been tested rather than cited by analogy. In that construction the cover group is a free product of Z²'s. Every Z² in the total group has trivial image in the hyperbolic quotient: a nontrivial image would be Z, whose lift translates a compact loop support to disjoint chambers while preserving its conjugacy class. Collapsing other chamber cores contradicts that preservation. The subgroup generated by these Z²'s is characteristic. In the present construction the chamber groups are nonabelian free and Π is hyperbolic, so no such rank-two-abelian detector exists. Even a characteristic covering alone would only lift a homeomorphism; it would not recover all finite panel chambers or their boundary parametrizations.

## 5. A second attempted shortcut: polarization cannot create δ in the outer group

Suppose, for the sake of testing compatibility, that the realized profile of M_q were a full complement Bε containing P_q. For a basis of Bε choose arbitrary realizing homeomorphisms and extend to a set-theoretic choice σ of representatives. It is invalid to demand that these representatives form an action. Their multiplication defects

    k(a,b)=σ(a)σ(b)σ(a+b)^{-1}

lie in the KERNEL of Homeo(M_q)→Out(Π), because Bε is a subgroup. They cannot equal an outer δ-defect: δ is nontrivial in O. Thus importing the polarization value 1 in (4.2) as an outer multiplication defect would conflate a chamber-coordinate variation with a nonzero outer class. A geometric secondary invariant in this kernel might be interesting, but none is constructed here and no conditional result depending on it is nominated.

## 6. Exact remaining operation and decision

We have built every M_c, proved its comparison, computed the exact visible translation subgroup for q_r+ℓ+t, sharpened the global source obstruction to the canonical profile P(X), eliminated normal/assembly/s-cobordism separation, and localized the remaining geometry to embedded graph cores. For q=x1x2, the missing step is to control arbitrary self-homeomorphisms strongly enough to determine P(M_q), or to produce another invariant of the embedded relative cores that distinguishes this model. The existing proof only determines the exact chamberwise translations. It does not prove the full-profile equality (3.4), unmarked distinction, or the opposite.

No viable nonroutine full theorem has been frozen. Decision: PREFREEZE / no nominee. All displayed closed deductions are retained as paid reductions, not submitted as the remaining acceptance. This is not an exhaustion claim or a global impossibility statement, and it does not weaken or reopen any older full target.
