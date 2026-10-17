# Family 178: logarithmic girth survives the existing spectral repair

Myeongjin Kang; no affiliation. Original prose CC BY 4.0, original code MIT. Third-party inputs are private and retain their own rights.

**Technical source consequence only; no nominee and no scope freeze.** The prospective operation was simultaneous cycle control and exact two-sided spectral repair. Reading the source's lower operations shows that its construction already pays almost all of this: the intermediate graph has logarithmic girth, and the final repair succeeds with probability 1−o(1) under a bounded-density pairwise-independent sample space. Replacing endpoint-collision rejection by a graph-distance rejection is an ordinary bounded-degree ball count. The resulting deduction below is useful, but it does not supply the substantial new mechanism required by this campaign.

## Exact source interfaces

Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, family178, `preprints/Deterministic-nonbipartite-Ramanujan-graphs-in-every-fixed-degree-September-23-2026/`. All 14 text blobs were retrieved from this directory via the complete preprints-tree and checked against their Git blob identities. Only the reading extents recorded separately are claimed as semantically read. There is one manuscript in this catalogue family; unrelated automorphic Ramanujan manuscripts were not treated as graph companions.

Write q=d−1, with d≥3 fixed, and a=1/10000. The source setup has q^g0 asymptotic to n^(0.002a), up to fixed integer-rounding factors, and M=ceil(n^(1/3+10a)).

- Introduction, thm:main: deterministic polynomial-bit-time simple d-regular graphs at every sufficiently large even n, all nonconstant adjacency eigenvalues strictly in (−2sqrt(q),2sqrt(q)). Its separate target-size corollary and limits on uniform-in-d complexity are already paid.
- Foundations, lemma:structure and the early admissibility rule: actual girth at least g0 throughout early pairing and cleanup. The unresolved boundary vertices have pairwise separation R0>g0 and no short nonbacktracking returns.
- Boundary, prop:boundary-completion: every completed edge preserves the girth exclusion. Therefore the simple d-regular graph BEFORE exact repair has girth at least g0, not merely a small average number of cycles.
- Repair, thm:exact-repair and its full seven-step proof: three stipulated input conditions give a rounded edge-pair law μ, each atom ≤C_d/(dn)^2, and M pairwise-independent draws. Both signed spectral success events, endpoint validity, and vertex-disjointness have joint probability 1−o(1). The entire polynomial-size affine prime-field seed space is enumerated; exact rational inertia tests certify the final strict spectrum.
- The source proof's collision estimate is O_d(M²/n). The construction does not condition every draw sequentially on distant prior draws, and doing so would destroy its stated independence. The valid extension below adds a final rejection event instead.

## Elementary deterministic switching lemma

Let G be a finite simple graph of girth at least integer g≥3. Let e1,...,ek be old edges such that the distance in G between the endpoint sets of every two distinct ei is at least g. Delete those edges and insert any perfect matching of their 2k endpoints. The resulting graph H is simple, has the same degrees, and has girth at least g.

Proof. Endpoint sets are disjoint. A new matching edge between different old-edge endpoint sets was not already present because their old distance is ≥g>1; a new edge within a single old endpoint pair just reinstates that deleted edge. Hence simplicity and degree preservation hold. A cycle containing no inserted matching edge is already a cycle in G. Otherwise, inserted edges cannot be consecutive, since they form a matching, so the cycle contains a nonempty segment P of retained old edges between two endpoints of inserted edges. If P joins distinct selected old-edge endpoint sets then |P|≥g by the distance assumption. If its endpoints belong to the same old edge ei, they are the two distinct endpoints of ei; P avoids ei, and P+ei is a cycle in G, so |P|≥g−1. In either case, the whole new cycle has length at least g because it also contains an inserted edge. This covers cycles using many different switches, not merely cycles created by a single switch. ∎

The usual two-edge switches of the source form just such a new perfect matching on all selected endpoints. This lemma does not assume a tree neighborhood around every vertex and does not require independence.

## Probability cost under the actual source law

There are 2M oriented old-edge slots. For a fixed oriented edge e, at most C_d q^g oriented edges have an endpoint within distance <g of an endpoint of e, by the bounded-degree ball estimate. A pair of slots from the same draw has joint atom bound C_d/(dn)^2 directly from μ. A pair from distinct draws has such a bound because the draws are pairwise independent and each edge marginal has atom bound C_d/(dn). Therefore every fixed pair of slots is too close with probability at most C_d q^g/n. The union bound gives

    P(any pair of old-edge slots at distance <g) ≤ C_d M² q^g/n.

No higher independence is used. Equality of slots and shared endpoints are included in this failure event. If M²q^g/n=o(1), the distant-slots event meets the source's simultaneous spectral success event with probability 1−o(1), without modifying μ or its moment estimates. A deterministic search adds a breadth-first distance test in the original pre-repair graph to the existing seed rejection rule. This costs polynomial time and cannot remove all passing seeds.

Take

    g(n)=floor(10^(-7) log_(d−1)n).

For all sufficiently large n, g(n)≥3 and g(n)≤g0 because 10^(-7)<0.002a=2·10^(-7). Also

    M²q^g/n = O_d(n^(−1/3+20a+10^(-7))) = o(1).

The exponent is exactly −9939997/30000000 <0. The source's 1−o(1) spectral conclusion and polynomial seed enumeration therefore yield the following technical consequence:

For every fixed d≥3 there are n0(d), k(d) and a deterministic algorithm that, on every even n≥n0(d), outputs a simple d-regular graph on n vertices, with girth at least floor(10^(-7)log_(d−1)n), every nonconstant adjacency eigenvalue strictly between ±2sqrt(d−1), and O_d(n^k(d)) bit complexity. Such a graph is connected and nonbipartite by the source spectral argument.

This is a source-method retention consequence, not an independent proof/contribution PASS and not a frozen nominated target. It does not assert a good logarithmic constant, optimal girth, polynomial complexity jointly in d,n, an arbitrary-base two-lift, prescribed cycle statistics, or a local adjacency oracle. Optimizing the retained constant would not change the operation-level assessment.

## Adversarial and boundary checks

- The distant-slots event is imposed on the old graph and before any switches; independence is not assumed after conditioning on it.
- The matching lemma handles new cycles visiting several switch locations. Pairwise vertex-disjoint switches alone are insufficient. In the cube Q3, delete 000–001 and 111–011 and insert 000–011 and 111–001. This is a valid vertex-disjoint degree-preserving switch, but creates the triangles 000–010–011–000 and 111–101–001–111. Q3 initially has girth four. The old distance between the selected edges is less than three, so the stronger hypothesis correctly rejects this example.
- Small n and g<3 are absorbed into the threshold n0(d). Fixed d≥3 is essential to the volume bound with q>1. Even n is unchanged; no odd-order extension is asserted.
- If no spectral repair were necessary, the pre-repair graph already has the girth property; the argument nonetheless works with the source's fixed M-switch repair.
- Exact spectrum verification, probability rounding, cutoff computation and bit complexity remain the source's work. They are not re-audited as upstream truths and not credited as new deductions.

## Closest primary comparison and history

Huang–Yau, *Spectrum of Random d-regular Graphs Up to the Edge*, arXiv:2102.00963v3, Section3 Definition3.1 and conditions (3.2), and Section5.2 Propositions5.9–5.12, were read at the actual proof bodies. Their local switching scheme already isolates switches by graph distance. Proposition5.10 counts bounded-degree balls and uses probability/union estimates; Proposition5.11 carries separation into the switched graph. Their analytic target and probability space differ, so their theorem is not falsely claimed to imply the exact algorithm above. The additional distance rejection here uses the same elementary operation, plus the supplied source's bounded density and pairwise independence. Source repair itself credits these antecedents. Primary URL: https://arxiv.org/html/2102.00963v3 .

I05's earlier cross-field screen had already rejected strong thin trees plus Ramanujan graphs as a route to arbitrary spectral thinness/signings. No such target is reopened here. The I88/I90 free-space approximation chain and r21 connected-matroid chain were discovered during preliminary screens and excluded. Coboundary-expanders/quantum-code puncturing was only screened in I07; it was not selected. No exclusion is inferred merely from a catalogue hit, and no worldwide priority claim is made from an absence of old-family matches.

The initial prospective gap—cycle control through the exact repair—is thus already paid by source operations and elementary isolation. A stronger arbitrary-base signing or sharp-girth target would require a different mechanism, not a renamed continuation of this deduction; no such target is frozen or claimed here. The packet closes as technical research support, with no manuscript, Lean development, acceptance, count, upload or publication.
