# AB194 independent contribution and eligibility review

Myeongjin Kang; no affiliation. Original review prose CC BY4.0. Original verifier code MIT. Third-party inputs remain private.

**Verdict: TECHNICAL for the exact full frozen AB194 target.** This is a contribution verdict relative to the stipulated pinned source and the campaign's requirement for a substantial additional mathematical operation. It is not a rejection of the claimed inequality, an independent full-proof verdict, or a claim that an inspected primary paper already states AB194 in its full generality. No acceptance or count change is made.

## Exact object reviewed

The reviewed author packet is fresh-arithmetic-discovery-r10, with external SHA256 anchors:

- manifest: `581d8051354ede8bed18853f82c8a87726df5223a7d912b7aa00054d87658481`;
- scope.json: `8f3721124a0e1d78e567221d97f188e0416587bd6b40aeb7615f4346df7e6de3`;
- rank-isolation.md: `35085a430f183cd16a4ee6dcd8eca293739a633e0df2da2c094f4dfbaaef7667`.

The claim is: for every prime p, every nonzero complete commutative Noetherian local ring (R,m,k) of characteristic p, every d=dim R≥0, every finite-free complex F in degrees0,…,d with finite-length homology and H0(F)≠0, and every0≤i≤d,

    binom(d,i) χ∞^R(F) ≥ e_m(R) β_i^R(F).

Here β_i=dim_k H_i(k⊗_R F), not the rank of an arbitrary nonminimal term, and χ∞ is the stated Frobenius-normalized Euler limit. The target has none of the domain, reducedness, equidimensionality, Cohen–Macaulayness, F-finiteness, residue-field, gradedness or geometrically-reduced-exceptional-fiber restrictions listed in scope.json. This review does not replace that target with an endpoint, domain, graded or dimension-two case.

The author's exact-membership verifier passed with its external manifest anchor. Independently, all nine retained pinned source blobs matched the complete preprints tree, Git blob identities and SHA256 values. All three primary PDFs were freshly fetched from their versioned arXiv URLs and matched the retained bytes. These are identity checks, not mathematical certification.

## Decisive operational comparison

The substantive unrestricted-local machinery is already in the pinned Lech source at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. In particular, the source supplies:

1. the normalized-length/perfection theory and its finite-length-module comparison;
2. the blowup, divided complex, arbitrary integral root bundle, finite twist-map vanishing and exact exceptional-layer Euler functional;
3. isolation of a chosen rank by integrating the derivative of a polynomial with zeros at the unwanted evaluation nodes;
4. Frobenius amplification, parameter reductions, minimality, residue extension, prime filtration and top-dimensional multiplicity summation.

Item3 is not merely a general analogy: the source's final proof takes exactly

    H_0(x)=∏_{j=1}^h(x+j),   P_0=H_0'/h,

rounds the scaled derivative roots, proves degree-zero hyperhomology, and uses

    0 ≤ (h−1)! λH0(F)
        + μ Σ_k (−1)^k b_k Σ_{l=−ks}^{−1} ∏_a(l−r_a).

It then integrates P_0 at the nodes0,−1,…,−h and uses alternating rank zero to isolate b0. These are the same bundle, functional, interpolation method, scaling, rounding and error estimate used in AB194.

The two additional verifications in AB194 are valid-looking useful refinements, but are routine within that already explicit operation:

**Root-window relaxation.** For a positive layer l≥0, the existing spectral argument only needs

    #{j:r_j>l−ks} ≤ k.

It therefore suffices to exclude indices j≥k+1, which follows immediately from r_j<−(j−1)s. The source excluded j≥k using the stronger upper bound r_j<−js. Its negative-layer argument is unchanged: for l<0 and j≤k−1, the same original lower bound r_j>−(j+1)s gives r_j>l−ks. Thus the enlarged window does not require a new spectral-sequence construction, a new vanishing theorem, or an additional geometric positivity input. It uses precisely the source's two twist quotient sequences with the minimal count required by the already chosen total degree.

**Move the omitted interpolation node.** For rank i, replace the source's H_0 by

    H_i(x)=∏_{0≤j≤h, j≠i}(x+j).

This is the same cardinal-node recipe: make the primitive vanish at every unwanted node, then differentiate to obtain the Euler polynomial. Rolle interlacing puts H_i' in the enlarged sufficient windows. The only enlarged gap is the one crossing the omitted node. Its node value is

    H_i(−i)=(−1)^i i!(h−i)!,

so the identical layer functional and identical cancellation give b_i/binom(h,i). Bounded rounding and the source's Riemann-sum estimate give the same O_h(Σb_k/s) error. There are only h+1 choices, so uniformity in i adds no further analytical or algebraic operation.

Finally the source's characteristic-p proof carries any such uniform rank coefficient through q=p^n, s=q−c and the limit. It already keeps b0 before discarding it, already allows noncyclic H0, and already performs the non-domain component argument inside its residue-field reduction. Minimal ranks remain unchanged under the same scalar extensions. Hence the full unrestricted ring scope is inherited once the rank coefficient is changed; AB194 supplies no separate new descent or asymptotic operation there.

This is an explicit same-operation reduction, not a judgement from the number of proof lines. The source has already formulated arbitrary-root bundles and the numerical functional at the generality needed; it has also chosen derivative interpolation for exactly the purpose of eliminating unwanted rank coefficients. AB194 adjusts the sufficient index count and selects another member of that interpolation family. Under the inherited brief's exclusion of routine parameter changes and expansions of an already available proof operation, this does not clear the substantial-contribution threshold.

## What the verdict does and does not assert

AB194 is stronger as a statement than the scalar corollary printed in the source. In particular, the interior inequalities are not asserted to follow just by numerical manipulation of χ∞≥e or the retained b0 estimate. The review must reopen the source proof, as above. For example, formal alternating-rank data (1,N,N,1) in length3 show why endpoint inequalities alone do not numerically bound the two middle coordinates; this is only a comparison of numerical functionals, not a claim that every such datum is realized by a short complex over a particular ring.

Nor is H_i for an interior index literally a translation of H_0: its missing interior node creates a gap. The additional observation is that the source's existing degree count already tolerates that gap. Recognizing this yields a useful source-relative strengthening. My TECHNICAL verdict is based on the explicit reuse of the source's extraction mechanism and on the already-paid local-ring generality, not on pretending that no observation was needed or that all consequences of a short proof are minor.

The most favorable substantiality interpretation is that every Betti coordinate is now controlled over all complete local rings in positive characteristic, beyond the inspected classical classes. That is a meaningful enlargement of the theorem statement. It does not establish a new bridge from graded rings or from Ulrich existence: the pinned source had already built the unrestricted blowup/length bridge, and AB194 changes the coordinate tested by its final polynomial. The campaign requests a substantial additional operation, not merely an unstated wider corollary of the stipulated proof. On that distinction the contribution gate does not pass.

## Closest primary proofs and later-work screen

The actual primary proof comparisons support **not DUPLICATE**, but they do not overcome the source-relative technical reduction.

- [Iyengar–Ma–Walker, 2104.10140v2](https://arxiv.org/abs/2104.10140v2), Theorem5.16, proves the all-Betti estimate conditional on a lim Ulrich point through two Koszul-homology comparisons. Theorem7.1 and Corollary7.2 obtain the Dutta inequality for standard-graded localizations. Their actual construction uses Proj, a finite linear projection, product-projective sheaves and Frobenius; it does not directly construct the needed point for arbitrary complete local rings. Conjecture8.1 is the scalar all-characteristic Dutta bound, not the full target of this review.
- [Iyengar–Ma–Walker, 2209.03498v2](https://arxiv.org/abs/2209.03498v2), Theorems4.17 and6.2 and proof§6.13, work with graded rings admitting linear Noether normalizations, a class broader than standard graded rings. The proof tensors with lim Ulrich graded modules, identifies limiting Betti tables over the normalization and uses a uniform graded regularity bound to enter the finite topology. This does not give an unrestricted complete-local comparison. It would be inaccurate to describe all earlier work as only standard graded.
- [Iyengar–Ma–Walker, 2510.02698v1](https://arxiv.org/abs/2510.02698v1), Theorems5.2 and6.9, give all three rank bounds in dimension two under geometric reducedness conditions on the exceptional fiber. The first uses an Ulrich module of constant generic rank and the Koszul argument; the second passes to R/j(R) and Dutta multiplicity. The geometric assumptions are not removable merely by invoking these proofs. The [publisher record](https://link.springer.com/article/10.1007/s10013-026-00828-4) now records publication on9October2026. Its full text was inaccessible without subscription; arXiv still listed only v1 when checked. No claim of inspecting the version-of-record proof is made.

Fresh searches of Dutta/Betti inequalities, complete-local scope and later Ulrich results, together with Linquan Ma's current primary publication list, did not identify a later unrestricted theorem in the bounded search. That negative result is not a novelty proof. The decision rests on the positive source-operation comparison, not absence of search hits. The read-limits record specifies exactly which bodies were inspected and which references were only identified.

## Developed-chain eligibility

No relevant pre-AB194 developed family194 chain was identified in the inspected project history. The older I14 occurrence is an inventory entry, not a developed Lech/Dutta argument. I28's actual filtered SmallCM construction and failure concern persistence of a complex-surface obstruction and the missing nonconical example. I226's actual EGH work concerns graded consecutive cancellations and division/Clifford coefficient obstructions. Neither is the rank-isolation operation here. Both remain excluded and are not relabeled as AB194. Older202/203 and209 exclusions also remain binding.

Thus I find no specific historical-family disqualification for this frozen claim within the inspected record. This is bounded eligibility clearance, not exhaustive worldwide or project-wide certification from a missing title. The failure is the contribution threshold: **TECHNICAL**, not an identified old-chain duplicate. The separate proof gate must decide full correctness; no proof verdict is imported from this review.
