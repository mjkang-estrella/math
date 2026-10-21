# r171 prefreeze calculations: the strongest paid coherence step

This file applies actual source and primary proof operations to the finite-group construction in CALCULATIONS.md. It is not a frozen new theorem or a contribution verdict.

## 1. The primary theorem that prevents an artificial gap

Girón Pacheco–Szabó, *Classification of anomalous actions of finite groups with the Rokhlin property*, arXiv:2608.09517v1 (10 August 2026), Theorem 4.1, applies to a separable algebra which is unital, stable, or has almost stable rank one. It does not require simplicity, nuclearity, UCT, or a bounded trace simplex. For two existing anomalous Rokhlin actions with the same anomaly, pointwise proper approximate unitary equivalence of their automorphisms is equivalent to a cocycle conjugacy whose underlying isomorphism is properly approximately inner.

For honest actions the anomaly is 1. This is the version used below. Importantly, an honest action must already exist before applying this theorem. CALCULATIONS.md supplies existence separately, without falsely promoting independently selected automorphisms to an action.

The actual mechanisms were read, including the proof of the finite correction lemma, rather than using the theorem as an unexplained name:

1. Lemmas 2.5–2.6 use stability to replace contraction implementations on finite sets by unitaries in 1+B. The stable construction uses three orthogonal multiplier isometries; two slots complete a contraction to an isometry and a spare full properly infinite complement completes it to a unitary. The approximation is on the tested B-elements. This handles the distinction between source multiplier unitaries and proper approximate unitary equivalence.
2. Proposition 3.1 averages along Rokhlin towers to promote approximate Murray–von Neumann equivalence of underlying maps to equivalence of coherent tuples. The orthogonal orbit pieces eliminate the need for independently chosen group-product implementers to satisfy a scalar associator relation.
3. Theorem 3.3 and Lemma 3.4 correct an approximate coherent tuple, with finite multiplicative, covariance, and continuity tests enlarged before selecting tower coordinates. In the displayed finite correction, the group-product defect is bounded by (6|G|+21)ε. The continuity estimate includes 9ε+sqrt(38ε) in addition to the old coherence defect. These are norms of actual finite-test errors, not tracial errors. Choose the input tolerances small enough for a summable schedule; the proof arranges successive increments bounded by 13·2^(−n) on its chosen tests. The limit is an actual coherent morphism.
4. Corollary 3.2 supplies equivariant uniqueness of coherent maps. Theorem 4.1 then constructs coherent morphisms in both directions, makes both compositions equivariantly approximately inner, and invokes two-sided approximate intertwining (Theorem 1.15). The resulting coherent isomorphism is a cocycle conjugacy. The abstract intertwining theorem is stated there with its earlier reference; I read the present proof and interfaces, not every earlier ancestral proof.

The source has its own point-intertwining construction, and Gabe's actual multiplier-pair theorem has a continuous path conclusion. It would therefore be inaccurate to describe the paid input as only disconnected pointwise choices with no path or intertwining machinery. The new primary theorem is the stronger compatible group operation for existing Rokhlin actions.

## 2. Applying it with the full trace cone

Let P=A⊗W⊗K and Q=B⊗W⊗K, with A,B separable nuclear complex C*-algebras. Let α:G→Aut(P) and β:G→Aut(Q) be honest Rokhlin actions of a finite group. Suppose

    F:T(Q)→T(P)

is a topological cone isomorphism, and for every g,

    T(α_g) F = F T(β_g).                                      (4)

All cones here contain all extended lsc tracial weights. By Source301 choose φ:P→Q with Tφ=F. Put γ_g=φ α_g φ⁻¹, an honest Rokhlin action on Q. Contravariance and (4) give

    Tγ_g = F⁻¹ Tα_g F = Tβ_g.

The constant maps γ_g,β_g are source point models for the same data: equality of all trace pullbacks implies equality on every cut for every coordinate trace before regularization. Norm uniqueness therefore provides multiplier unitaries comparing γ_g with β_g on each finite set.

Q is stable. An inner automorphism implemented by w∈U(M(Q)) is properly approximately inner: multiply w by a sequential approximate unit of Q to obtain contractions and use Lemma 2.6. Thus for every finite test set and tolerance, replace the particular multiplier implementation by a unitary in 1+Q at an additional arbitrarily small error. Diagonalizing these finite sets shows

    γ_g ≈pu β_g    for every g∈G.

Apply Theorem 4.1, with anomaly 1 on both sides. Its cocycle conjugacy has an underlying isomorphism ψ:Q→Q with ψ≈pu id_Q. The composition Ψ=ψφ is a cocycle conjugacy between α and β, and it realizes exactly F on the full cone.

The last assertion requires checking infinite weights, rather than merely citing preservation of normalized traces. If Ad(v_n)(a)→ψ(a) for a≥0 and v_n∈1+Q, lower semicontinuity and inner invariance give τ(ψ(a))≤τ(a). At the same time

    ||Ad(v_n*)(ψ(a))−a|| = ||ψ(a)−Ad(v_n)(a)|| →0.

Lower semicontinuity in this reverse norm convergence gives τ(a)≤τ(ψ(a)). Thus equality holds, including at infinity, and Tψ=id. Hence TΨ=Tφ Tψ=F. This argument never infers an inequality between trace values merely from Cuntz comparison; that would only give the corresponding rank inequality. Both norm limits are essential here.

The same observation proves invariance under point-norm limits of multiplier-inner automorphisms used in RELATIVE.md. It retains finite-domain and kernel ideals and uses no subtraction of extended values.

## 3. What this pays, and what it does not

Together with CALCULATIONS.md, the construction realizes a prescribed finite-group action on the full cone by an honest Rokhlin action on P. For existing Rokhlin actions, the prescribed equivariant cone isomorphism is realized by a cocycle conjugacy. The source supplies the algebra classification and uniqueness; the primary supplies the coherent Rokhlin correction and two-sided group intertwining. This is a standard classification composition once those inputs are present. It is not submitted as a substantial new result.

The conclusion is cocycle conjugacy. It does not assert conjugacy without a cocycle, a canonical realization, an exact functorial choice of isomorphisms for every cone map, a section of the automorphism-group quotient with additional topology, or an extension agreeing exactly with a prescribed ideal action. Dropping Rokhlin, stability, separability, or nuclearity would require new interfaces; none is inferred here.

For comparison, Nawata's arXiv:1905.09469v2 treats the simple monotracial setting with existing strongly outer finite-group actions after W tensoring. Its actual 2×2 cohomology proof starts with an actual cocycle, builds twisted fixed-point matrix corners, and uses projection comparison and a partial isometry to solve the cocycle equation. It cannot alone manufacture a group law from arbitrary source lifts, and its simple trace hypotheses do not cover arbitrary ideal cones. The 2026 theorem above removes that artificial limitation for the existing-Rokhlin-action comparison. I did not replace it with the older weaker interface.

The model construction in the 2026 paper, Lemma 6.1 and its full proof, already uses finite-group-indexed direct sums, translation actions, and equivariant inductive systems. Its range theorem is for Kirchberg K-theory modules. The present full-cone averaging identity is worked out explicitly in CALCULATIONS.md; it is not a claim that the K-theory theorem directly classifies W-stabilizations. Equally, the block construction is not being represented as an unprecedented new proof primitive.
