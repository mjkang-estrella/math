# Family 230: ordered variation versus spatial packing

Pre-freeze feasibility screen only; no full target frozen and no nomination. Original prose Myeongjin Kang (no affiliation), CC BY 4.0. Third-party inputs private.

## Actual interfaces and positive comparison

The pinned explicit SLE gauge introduction gives, for every fixed 0<κ<8 and d=1+κ/8, positive finite H^h on every positive-time compact segment, where h(r)=r^d(log log(1/r))^((2-d)/2), and finite expected H^h in bounded spatial regions. Its proof uses a retained measure and a finite-mesh sausage covering charge; it expressly does not identify this measure with natural parametrization. A natural separate question is the exact spatial packing gauge. No claim that this is a new named conjecture is made.

Holden–Yuan, arXiv:2211.15609v4 (20 February 2025; journal publication in 2026), Theorems 1.1, 1.7 and 1.8 already prove finite ordered ψ-variation and identify its fine-mesh limit with natural length, for ψ(r)=r^d(log log(1/r))^{-(d-1)}. Theorems 1.2–1.3 already give the sharp modulus and fast-exit LIL. Propositions 5.2 and 5.15 give the matching small-content probability for the segment ending at its FIRST exit from a disk, with conditional estimates under a precise nice-tip condition. The proof iterates a bounded-content, nice-tip-preserving crossing event; the LIL ending uses a backward sequence of nested first exits and a conditional-event lemma. These are existing substantial operations, not new work here.

## Paid deterministic upper bound (technical)

Let γ:[a,b]→R² be continuous with finite ψ-variation Vψ(γ), and ψ be increasing near zero with ψ(2r)≤Kψ(r) for small r. Let E=γ([a,b]) and take a finite family of disjoint open balls B(x_i,r_i), centers x_i∈E, with all r_i sufficiently small compared with diam(E). For each i select t_i with γ(t_i)=x_i and take the connected component of γ^{-1}(B(x_i,r_i)) containing t_i. Because E is not contained in this ball, at least one endpoint of this component lies inside [a,b] and maps to the sphere; choose that endpoint u_i. The segment between t_i and u_i has image in the closed ball, endpoint displacement r_i, and interior image in the open ball. For different i, interiors of these time intervals are disjoint. Order the finitely many intervals, add their endpoints to one partition, and obtain

    Σ_i ψ(r_i) ≤ Vψ(γ),   hence Σ_i ψ(2r_i) ≤ K Vψ(γ).

Taking finite subfamilies handles countable packings. Thus the packing premeasure, and therefore the outer packing measure, with gauge ψ is finite. The constant-curve case has zero premeasure. For the SLE gauge ψ, a fixed K is available since ψ is regularly varying. Applying Holden–Yuan yields finite ψ packing premeasure on every positive-time chordal segment. This is a routine deterministic consequence of an actual primary theorem and is NOT nominated.

## Unpaid positivity interface

A sufficient route to positive spatial packing measure would control lower densities of the entire natural occupation measure μ:

    liminf_{r↓0} μ(B(z,r))/ψ(r) < ∞

on a positive-μ subset, together with a packing-density theorem. The first-exit estimates alone do not establish this. They control the natural time between a visit to z and first exit; μ(B(z,r)) also counts all previous visits and all subsequent returns, which may contribute much more. The inclusion is in the wrong direction: first-exit content ≤ whole-ball occupation. In the two-sided Palm picture both wings and their later returns must be controlled. The quantitative primary nice-tip construction preserves tip regularity for the next crossing; its displayed conclusion does not exclude later returns to the original disk or bound their total occupation.

One possible additional operation would be a conditional small-total-occupation event of probability exp(-C u^{-1/(d-1)}) at radius r and threshold u r^d, compatible with infinitely many nested scales under the two-sided marked-point law. Neither the pinned stopped Green upper-mass tail nor the primary first-exit lower-tail estimate is this statement. Uniformity over arbitrary rough pasts cannot be inserted for free: the primary explicitly needs nice tips even for the one-sided lower estimate. No such two-sided return estimate was proved here, and no smaller full claim is substituted.

## History and reading limits

I126, lines216–220, screened use of the exact Hausdorff gauge as a discrete microscopic-length limit. That operation is different, but it does not establish eligibility or substantiality of the present packing question. The present paid upper bound is technical independently of that history. No claim of exhaustive history or worldwide novelty clearance.

Read the complete pinned explicit-gauge introduction. The combined introduction/local-laws display truncated part of local-laws; only its visible finite-tilt and physical localization material is preliminary reading, not a claimed full read or a premise for a new proof. All16 retrieved source texts are pinned-blob authenticated in source-receipts.json; retrieval is not reading. Read Holden–Yuan extracted lines1–335 (introduction/main statements),1700–1810 (variation Vitali operation and Proposition5.2 through nice-tip setup),2080–2200 (end of nice-tip proof, Lemma5.5/Proposition5.4/Lemma5.3/Proposition5.15 complete endings),2370–2545 (modulus/LIL proof endings), with overlaps. Middle preparatory Lemmas5.6–5.14 were not fully read; no claim that all their geometry has been audited. The retrieved arXiv PDF identifies itself as v4, even though the unversioned URL was used. Journal metadata was discovered by search; journal text was not read.

Disposition: exact new interface identified but unpaid; pre-freeze screen closed without nomination. The upper packing bound is technical and requires no new pinned-source operation.
