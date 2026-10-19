# Full numerical support: the stronger compatible reduction

This is a preselection calculation testing existing operations, not a frozen candidate or a nomination. The former r78 nonfree-quotient numerical-kernel gap must be compared with mass–Hom bounds, rather than only with a quadratic form pulled back through forgetting. Initial feasibility preceded the detailed primary comparison below. No reading is backdated.

## Precise categorical calculation

Let X be smooth projective over C, let a finite group G act on X, and let σ=(Z,P) be a G-invariant numerical stability condition on Db(X). Suppose σ has a mass–Hom bound: for every A there is C_A with dim Hom(A,E)≤C_A m_σ(E) for every E. Constants may depend on A and σ. Write F:Db_G(X)→Db(X) for forgetting. There is no freeness assumption on the action.

Macrì–Mehrotra–Stellari, [0705.3752v3](https://arxiv.org/pdf/0705.3752v3), Lemma2.16, proves the induced slicing by lifting the unique HN triangles. Invariance makes the HN factors invariant; uniqueness of their maps supplies the cocycle identities for their linearizations. The induced central charge is Z_G=Z∘F and its semistable objects are precisely those whose underlying objects are σ-semistable. The same HN factors give

    m_σG(E)=m_σ(FE).

This identity is on arbitrary objects, not merely stable ones. In characteristic zero, the Hom space in the equivariant derived category is the invariant subspace of the ordinary Hom space. Consequently, for each equivariant A,

    dim Hom_G(A,E) ≤ dim Hom_X(FA,FE)
                      ≤ C_FA m_σ(FE)=C_FA m_σG(E).

Thus the entire mass–Hom condition transfers. This is not inferred from injectivity of numerical forgetting. In fact, F can have a large numerical kernel.

Here is the exact full-lattice argument, which is Cheng's existing proof with the Serre functor in place of tensoring by a dualizing complex. For any Hom-finite category with a Serre functor S, finite-rank numerical group N and such a stability condition, choose finitely many A_i whose Euler functionals separate N_R. Put

    ||u||²=Σ_i χ(A_i,u)².

Shift a semistable E into phase φ∈(0,1]. If Hom(A_i,E[j]) is nonzero, the slicing and Serre duality imply

    φ⁻(A_i)−1 ≤ j < φ⁺(S A_i).

Only a fixed finite set J_i of integers can occur. The mass–Hom inequality for A_i[−j] then yields

    |χ(A_i,E)| ≤ Σ_(j∈J_i) C_(F(A_i[−j])) |Z_G(E)|.

Summing squares gives ||[E]||≤C|Z_G(E)|. Equivalently C²|Z_G|²−||·||² is nonnegative on semistable classes and negative definite on ker Z_G. Every numerical direction is included in the norm; no bound on arbitrary signed kernel vectors by their zero charge was asserted. The bound is only on actual semistable objects.

This is the operative proof of [Cheng,2608.14540v1](https://arxiv.org/pdf/2608.14540v1), Theorem2.1. Its scheme statement is not quoted as a stack theorem: the categorical argument above explicitly identifies the hypotheses used. The quotient category has Serre functor E↦E⊗ω_X[dim X] with its natural G-linearization. It is smooth and proper for a finite group in characteristic zero. One can see the smoothness interface by equivariantizing a finite perfect resolution of the diagonal, using the finite sum of its translates and the averaging idempotent. This is a standard finite-group categorical operation, not a new source construction.

For clarity, finite rank is not obtained by assuming forgetting injective. For a smooth proper dg model, the diagonal is perfect; applying its Hochschild trace functor to a finite perfect construction shows that Hochschild homology is finite-dimensional (properness makes the image of a free bimodule a perfect C-complex). The Euler pairing factors through Hochschild homology by [Shklyarov,0710.1937v3](https://arxiv.org/pdf/0710.1937v3), Theorems3.4–3.5. Hence every finite integer Euler matrix has rank bounded by that finite dimension. Its rank over Q equals its rank over C. Choose a maximal independent finite set of Euler rows over Q; they separate the numerical quotient and embed it into Z^s. The quotient is therefore finite-rank free. The usual dg model for Db_G(X) may be obtained from the induction of a generator of Db(X); averaging makes every equivariant object a summand of induction of its underlying object. The dg enhancement/model construction itself is a standard background input, not freshly reconstructed here.

The charge factors through this numerical quotient. Indeed induction is adjoint to forgetting, so χ_G(Ind A,v)=χ_X(A,Fv); numerical vanishing of v implies numerical vanishing of Fv. Left/right Euler radicals agree through the Serre functor. This also appears in MMS Remark2.18. No crepant-resolution equivalence is required or claimed.

## Compatibility with the actual source055 sector

The source's ordinary large-volume condition has exactly the standard double-tilt heart, including strict-positive/nonpositive boundary conventions. If B,H are G-invariant numerical classes, pullback by every g preserves both slope torsion pairs, all HN filtrations and Z. The ordinary stability condition is therefore G-invariant. The separate square-root-Todd heart is not automatically assigned this invariance argument.

The missing input is not automatically supplied by the words “support property.” It is supplied by the actual construction, with the starting mass bound taken on (P1)^n, not assumed on an elliptic power. In source055 `06-ambient.tex`, `lem:elliptic-scaled-support` and `prop:product-sector`, the positive-weight product conditions descend continuously through the sign quotient to (P1)^n. At equal weights this is exactly Li–Liu–Liu–Macrì–Perry–Stellari–Zhao's [2607.28411v1](https://arxiv.org/pdf/2607.28411v1) Proposition5.1 and formula(5.2): the same sign quotient of the same product slicing, with the same positive charge normalization. Their Theorem5.4 connects this condition to a finite-length exceptional-collection heart, for which mass–Hom bounds hold; Theorem7.5's proof explicitly starts with this (P1)^n construction. Their Remark7.3 transports the bound along the connected positive-weight family on (P1)^n. Only a pointwise constant is needed, so no uniform mass comparison along an unbounded path is assumed.

The source next takes the finite flat symmetric quotients block by block to a product of projective spaces, deforms the charge in its support neighborhood, and restricts along closed immersions. Lemma7.4(2) transports mass–Hom bounds through these finite-flat pushforward constructions; the relative dualizing complex is perfect for maps between these smooth varieties. Remark7.3 handles deformation. Lemma7.4(1) handles the closed immersion because it is finite. Thus the SAME constructed ordinary condition, not an unidentified condition with the same charge, has the bound. Source `07-heart.tex` identifies its heart with the prescribed double tilt, including slope zero. The detailed Proposition5.1/Theorem5.4 check came after the first scratch formulation and corrected an unnecessarily assumed mass bound on the elliptic starting category; all this occurred before any freeze.

In particular the full compatible calculation applies to a fixed smooth projective threefold with K_X≅O_X and any fixed finite group action preserving the selected B,H. At each G-invariant B_*,H_* the source's neighborhoods intersected with the invariant spaces and its single threshold T retain all B,H in those neighborhoods and every t≥T. The numerical support constant may depend on X,G,B,H,t. No parameter-uniform support constant is claimed. Z_G is the underlying-space integral; division by |G| gives the conventional quotient-stack integral and only rescales support constants.

This closes the particular kernel-control interface left in r78 by a stronger already available primary operation. It does not identify a residual unpaid compatibility operation for nomination. The full frozen-scope/gate workflow was never started. No claim of verbatim duplication, independent correctnessPASS, author contribution rating, or worldwide priority is made.
