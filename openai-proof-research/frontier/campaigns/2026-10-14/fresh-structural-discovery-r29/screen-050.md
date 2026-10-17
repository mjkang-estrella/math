# Family 050: the projective-plane transfer is technical

This is a pre-freeze screen, not a campaign nomination or independent acceptance. The source at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true. The complete proposed consequence is retained below; no target was frozen and then weakened.

## Consequence and its proof

Let S=P¹×P¹, P=O(1,1), and f_m the coordinatewise power maps. Let G be the rank-two bundle in the source, and set V_m=f_m*G. There is m₀ such that for every integer m≥m₀ the rank-four bundle

F_m=π_*(V_m⊗P²)

on P² has no smooth Griffiths-semipositive Hermitian metric, although it is ample. Here π:S→Sym²(P¹)=P² is the finite flat double quotient exchanging the factors. In fact F_m is ample for every positive m.

First, for each fixed positive integer a, the source's trace-limit argument applies to V_m⊗P^a. Replace the line bundle P throughout Proposition `prop:limit` by P^a: its sole power-map identity becomes f_m*(P^a)=(P^a)^m. The root frame transition tends to one as before; equivalently its exponent is 2a/m in frames for P. The normalized coefficient bounds, weak limit, submean noncollapse, radial convolution, polarization on every fiber, and overlap identification in the source remain unchanged. Thus positive metrics for infinitely many m would give a nonzero finite nonnegative psh Hermitian quadratic on G∨. Source Proposition `prop:obstruction` excludes that object. Consequently, for each fixed a there are only finitely many m with a strictly positive metric on V_m⊗P^a. This is persistence under a fixed twist, not a uniform assertion when a varies with m.

The double cover has ramification divisor R equal to the diagonal, O(R)=P, and π*O_P²(1)=P. Its relative dualizing line bundle is ω_π=P. Put E_m=V_m⊗P, which is ample by the source. Finite duality gives

(π_*(E_m∨))∨ ≅ π_*(E_m⊗ω_π)=F_m.

Theorem 1.1 of Biswas–Laytimi–Nagaraj–Nahm, arXiv:2407.01151v1, says that a finite direct image of an anti-ample bundle between smooth projective varieties is anti-ample. Applied to E_m∨ it proves that F_m is ample. Its §2 proof was read, including the curve/base-change argument for anti-nefness and the small rational twist argument for anti-ampleness.

There is also an elementary double-cover verification of exactly the same ampleness step. For every vector bundle M on S,

0 → σ*M⊗O(-R) → π*π_*M → M → 0,

where the last map is evaluation and σ exchanges factors. Locally the cover is A[t]/(t²-d); the kernel of multiplication B⊗_A M→M is the other-sheet module with the ramification factor. Geometrically, S×_P²S consists of the diagonal and the graph of σ, meeting along R; the ideal of the diagonal restricts to O(-R) on the other component. Tensor the corresponding exact sequence by the second pullback of M, and push along the first projection. This also explains the kernel's twist and avoids treating the ramified fiber as a disjoint union of two reduced points. For M=V_m⊗P², the kernel is σ*(V_m⊗P) and the quotient is V_m⊗P². Both are ample. Extensions of ample vector bundles are ample, and ampleness descends under finite surjective pullback. This recovers the preceding finite-duality consequence rather than supplying a new operation.

Suppose now that F_m has a smooth Griffiths-semipositive metric. Holomorphic pullback preserves semipositivity even at ramification points. The evaluation map π*F_m→V_m⊗P² is a vector-bundle quotient, so the quotient metric is smooth Griffiths-semipositive. Tensoring with a fixed positive metric on P makes V_m⊗P³ strictly Griffiths-positive: the added line curvature is positive in every nonzero base direction and every nonzero fiber vector. The fixed-twist conclusion with a=3 excludes this for all sufficiently large m. This proves the stated consequence without claiming that ramified pullback preserves strict positivity.

## Operation-level disposition

The changed base P² is a meaningful difference from the source's quadric surface. It does not, by itself, establish a substantial new mechanism. The extra operation is precisely the combination of finite duality, the existing direct-image anti-ampleness theorem (or the standard double-cover kernel sequence), the source's same trace argument with a fixed line power, and ordinary quotient/tensor curvature rules. There is no new limiting object, new positivity estimate, new obstruction, or newly resolved uniform parameter issue in this transfer. Disposition: **TECHNICAL, no nominee**. This conclusion does not require finding a prior paper whose headline states this exact rank-four/P² consequence.

The 2026 Du–Xie and Liu–Wan constructions are credited separately. Du–Xie 2609.26504v1 Theorem 1.1 concerns rank two on an abelian product; the portions read give a persistent integral Levi obstruction and deformation to an ample locus. Liu–Wan 2609.37309v1 Theorem 1.1 concerns stable rank two on every Hirzebruch surface and excludes a larger Finsler metric class. Its introduction and §§4.2–4.5 were read: the final bundle comes from prioritary-stack deformation near a split model, not a stated descent to P². These inspected results are not asserted to prove the exact consequence above. They also do not restore substantiality to the elementary transfer.

## Reading limits and provenance

All nine source text files were retrieved through the complete preprints tree and authenticated against pinned Git blobs. Actual source reading: introduction in full; ampleness section in full; limit section in full; conclusion in full; obstruction section lines 1–100 and 220–308; bibliography entries relevant to the named comparisons. The construction section and the omitted middle of the obstruction section were not fully reread in this screen. The source's obstruction theorem is a stipulated premise, not an audited theorem.

Biswas–Laytimi–Nagaraj–Nahm 2407.01151v1: introduction and complete §2 proof read; the unrelated §3 is not used. Du–Xie: HTML lines 27–194 only. Liu–Wan: HTML lines 40–182 and 411–578 only; the complete analytic obstruction proof was not read and is not used to derive the consequence. Private fetched bytes and retrieval URLs are in `private/primary/receipt-050.json`; fetching a body is not a claim to have read all of it. Bounded searches did not establish an exact P² duplicate, and their missing hits are not novelty evidence. No worldwide priority claim is made.

Original reasoning/prose: Myeongjin Kang, no affiliation, CC BY 4.0. Any original checking code: MIT. Third-party bodies remain private.
