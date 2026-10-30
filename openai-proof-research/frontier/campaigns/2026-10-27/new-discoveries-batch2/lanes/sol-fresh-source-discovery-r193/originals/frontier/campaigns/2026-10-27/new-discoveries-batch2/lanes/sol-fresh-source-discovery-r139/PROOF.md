# Ordinary refutation, excluded from discovery credit

This is a complete ordinary mathematical refutation of Achour's Conjecture 1, not an eligible campaign nomination. No independence, novelty, formalization, or manuscript clearance is asserted.

Source: Hassine Achour, *A Degree-Spread Bound Between Independent Domination and Minimum Maximal Matchings: A Conjecture*, August 5, 2026, version 1.0.0, DOI10.5281/zenodo.21806398 (concept DOI21806397). The actual deposited `paper.tex`, Section1, Conjecture labeled `conj:main`, asks whether every finite simple connected nontrivial graph G satisfies

    i(G) <= mu*(G) + Delta(G) - delta(G).

Here i is the minimum size of an independent dominating vertex set; mu* is the minimum size of an inclusion-maximal matching. Both definitions were read in the source. There is no minimum-degree-two assumption, no regularity assumption, and no restriction to order at most9.

Let G have vertices a1,...,a6,b1,...,b6 and exactly the eleven edges

    a1a2,a2a3,a3a4,a4a5,a5a6,
    a1b1,a2b2,a3b3,a4b4,a5b5,a6b6.

It is the corona P6 o K1, a connected simple tree. Its pendant vertices have degree1, its endpoint core vertices degree2, and its four interior core vertices degree3. Thus delta=1 and Delta=3.

Every dominating vertex set contains at least one of ai,bi for each i: the only neighbor of bi is ai. These six disjoint pairs force size at least6. The set {b1,...,b6} is independent and dominating, so i(G)=6.

The three edges a1a2,a3a4,a5a6 form a matching M. Every edge of G touches a core vertex, and every core vertex is matched by M. Consequently no edge can be added to M, proving it is maximal. Thus mu*(G)<=3. For the reverse inequality, every maximal matching matches every core vertex: if ai were unmatched, bi would also be unmatched since it has no other neighbor, so aibi could be added. A matching edge matches at most two core vertices, so at least3 edges are necessary. Hence mu*(G)=3.

The proposed bound would give 6<=3+3-1=5, which is false. This one admissible graph refutes the full universally quantified conjecture, not merely a helper or a proposed strengthening. No finite computation is needed for this conclusion.

For context, the same argument gives a classical corona identity. For any finite simple core H of order k, let C=H o K1 and let nu(H) be its maximum matching size. Then i(C)=k and mu*(C)=k-nu(H). Indeed, in any maximal matching of C, every core vertex must be matched. If t of its edges lie in H, the other k-2t core vertices must be matched to their leaves; its size is k-t>=k-nu(H). Conversely a maximum core matching, supplemented by pendant edges at unmatched core vertices, is maximal in C and attains that size. If H is connected and k>=2, Delta(C)-delta(C)=Delta(H). The claimed inequality on these coronas is therefore equivalent to nu(H)<=Delta(H), already contradicted by P6. Even path cores give violations of unbounded size while the corona degree spread stays2.

This last observation is not a second credited result or a novelty assertion. The direct proof makes explicit why the candidate fails the task's routine-classical-adaptation exclusion. The actual earlier Alikhani–Soltani source arXiv1712.03422, Section2.2, theorem labeled `corona`, states the same saturation identity for H o E_m as nu(H)+l with l unmatched core vertices, and explicitly states the perfect-matching case k/2. Its proof and following path/cycle corollary were read. That public theorem predates Achour's conjecture by years. Its printed proof is abbreviated; the elementary complete argument above does not depend on accepting any missing step in that exposition.

Strongest objection: this construction is an immediate use of familiar corona behavior and an already public saturation formula. It should receive zero campaign credit under the explicit exclusion, even though it contradicts the literal new source question. It is not proposed as a new theorem about coronas.

Exact mathematical falsifier of this handback: show an omitted edge or hypothesis in the actual source excluding this 12-vertex tree, an independent dominating set of size<=5 in the specified graph, or a two-edge maximal matching. The private-leaf and core-coverage arguments rule out the latter two. There is no remaining ordinary-proof gap. The remaining eligibility gap is substantive originality; independent clearance and full current registry coverage were not obtained, and no Lean/paper work is warranted.
