# Prefreeze reduction: the residual bracket is horizontal curvature

This is a compatible reduction, not a full-scope nominee. All assumptions made to perform the reduction are displayed. In particular an arbitrary almost-holomorphic MRC map is NOT silently replaced by a smooth map on all of X.

## 1. Smooth-locus setup and descended projectors

Let f:X°→Y° be a proper holomorphic submersion with connected smooth projective rationally connected fibers Z_y. Suppose T_X°=E_1⊕E_2 is the restriction of the specified splitting. This applies on a suitable smooth fibration locus of an MRC map in the projective setting. Let P_i be its projectors and V=T_X°/Y°.

For each y, the composite

    T_Zy → T_X°|Zy --P_i--> T_X°|Zy --df--> O_Zy ⊗ T_Y°,y

vanishes: its entries are holomorphic one-forms on Z_y. Thus P_i preserves V pointwise. Its images V_i=P_i(V) are holomorphic subbundles, V=V_1⊕V_2, and V_i=E_i∩V. There is no rank-jump issue for an idempotent on a connected component.

P_i induces an idempotent p_i on f*TY°. Proper connected fibers give f_*O_X°=O_Y°. The projection formula identifies

    H0(X°,End(f*TY°)) = H0(Y°,End(TY°)).

So p_i descends to an idempotent of TY°, with image W_i. The identities p_1+p_2=1 and p_1p_2=0 descend too. Consequently

    TY°=W_1⊕W_2,     0→V_i→E_i→f*W_i→0.                (1)

Surjectivity in (1) is pointwise: lift a vector in f*W_i to TX° and project with P_i. This constructs quotient summands on the smooth locus; it does not split either extension in (1).

The base distributions W_i will now be ASSUMED integrable. If they extend as a splitting on a smooth compact non-uniruled projective base, Höring's theorem provides this assumption. A noncompact smooth MRC locus alone does not meet that theorem's hypotheses. This is one of the global interfaces left explicit.

## 2. Fiberwise product and vanishing of mixed vertical tests

The source rationally connected theorem gives, on each fiber, a compatible product

    Z_y ≅ Z_1,y × Z_2,y,
    V_i|Zy = pr_i* T_Zi,y.                              (2)

Zero-rank factors are points. Nonzero factors are smooth projective rationally connected, by projecting rational curves on Z_y. Thus H0(Z_i,y,Ω1)=0. In particular

    H0(Z_y, Hom(V_i|Zy,V_j|Zy))=0,  i≠j.              (3)

For completeness, fix a point z_j in the other factor. A section of the Hom bundle restricts on Z_i×{z_j} to a finite tuple of one-forms on Z_i with values in the fixed vector space T_Zj,zj. Each is zero. Vary z_j. This proves (3) without choosing identifications (2) in a family.

Since the bracket of vertical fields restricts to the bracket on the fiber, (2) also makes each V_i integrable on X°. No holomorphic variation of the product is required for this statement.

Let B_i:Λ²E_i→E_j be the Frobenius tensor P_j[e,e']. The base integrability assumption makes its image lie in V_j. To see this locally, lift a frame of W_i to f-related fields in E_i and add a frame of V_i. Brackets of the lifts project to brackets in W_i; those involving vertical fields project to zero. Tensoriality then proves the assertion for arbitrary local sections.

Restrict B_i to V_i⊗E_i. It vanishes on V_i⊗V_i by integrability of V_i, hence factors through

    V_i ⊗ f*W_i → V_j.                                 (4)

On Z_y the second input is a trivial vector bundle, so (3) kills (4). Every point belongs to a fiber; (4) therefore vanishes everywhere. Alternation now gives the unique factorization

    B_i : Λ²E_i → Λ²f*W_i --C_i--> V_j.                (5)

By the projection formula the residual tensor corresponds to

    C_i ∈ H0(Y°, Λ²W_i* ⊗ f_*V_j).                     (6)

No local freeness or base-change theorem for f_*V_j is being assumed. It is a coherent direct image, and the formula is for its sections. Dimensions of fiber automorphism spaces may jump.

This pays more than fiberwise integrability: ALL bracket tests with one vertical input vanish. The only remaining bracket for E_i is a horizontal two-direction operation taking values in vector fields on the opposite rational factor. Neither the rational-box argument nor a trivial normal bundle kills (6).

## 3. What has and has not been obtained

If W_i has rank at most one, or the right side of (6) has no sections, B_i vanishes on this locus. If this happens for both i and X° is dense in a smooth X, the original global Frobenius tensors vanish by holomorphicity. That is an elementary compatible source/primary consequence, not a nominated restriction of the general re-embedding question. No extra vanishing of f_*V_j is asserted; rationally connected factors may have many vector fields.

Equations (1) can have extension classes in H1(X°,Hom(f*W_i,V_i)). A splitting of TX into E_1,E_2 does not itself furnish a horizontal splitting of the entire relative tangent sequence. A correction framed only as a connection on a fixed fiber bundle therefore does not yet address every original tangent splitting.

Even after a smooth global quotient is available, non-uniruledness of the base does not give c1(Y)=0. Müller's replacement theorem and the affine Kähler Calabi–Yau theorem have an additional hypothesis at exactly that point. Their proofs pay that case and do not pay an unrestricted one.

Finally, (5)–(6) live on the stated smooth locus. The 2026 equal-multiplicity descent theorem is useful where its entire vertical-tangent containment and equidimensionality hypotheses hold; it is not a global extension of (1) across all degenerations. Reflexive extension over a codimension-two set does not remove an unexamined codimension-one pole or prove that a new embedding stays a subbundle.

## 4. Concrete test of the remaining term

Take an abelian surface A with invariant independent fields U,V and let X=A×P1. With coordinate z on the affine chart of P1, the global fields S=∂_z and T=z∂_z have bracket [S,T]=S (both extend at infinity). Let

    E=span(U+S,V+T),     F=T_P1.

Then E≅O_X², F=pr_P1*T_P1, and TX=E⊕F. The quotient f:X→A has V_1=0 and V_2=F, W_1=TA and W_2=0. Formula (5) is exactly

    B_E(U+S,V+T)=S ∈ H0(P1,T_P1).

Every rational curve into X projects constantly to A. Thus the source's rational boxes test vertical directions and cannot see this nonzero horizontal two-form. Restriction of ANY connection curvature to a one-dimensional base curve is also zero for dimension reasons. This example refutes the proposed inference from curvewise flatness to ambient flatness; it does NOT refute the re-embedding question. Note03 gives the explicit correction for this same example.
