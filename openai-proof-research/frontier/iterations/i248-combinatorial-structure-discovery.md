# I248 — Uniform rooted-pattern packing amplification

Date: 2026-10-12. **Verdict: candidate worthy of independent proof and contribution gates.** One nomination; no acceptance. The target is twenty total substantial findings, with ten previously accepted. No shared state was changed.

## Result

Fix d≥2. For sufficiently large n, 1≤s≤10 log n, and 0<r<1 with r^(ds+binom(d,2))≥n^(−1/100), put p=1−(1−r)^(128d)≤128dr. There are deterministic graph classes D,E of probabilities 1−o(1) under G(n,r), G(n,p), respectively, uniformly in r,s, such that for **all** G∈D, H∈E, root sets Y⊆[n] with |Y|≤n^(2/3), and families R of rooted d-vertex edge-presence patterns,

    ν_R(H;Y) ≥ min{2d ν_R(G;Y), floor((n−|Y|)/(16d²))}.

A pattern prescribes an arbitrary internal graph on d nonroot vertices and ≤s neighbors in Y for each of them. ν_R counts the maximum number of vertex-disjoint nonroot blocks realizing any of the patterns, allowing arbitrary overlaps and repetition in their root neighborhoods. The claim is a simultaneous packing-rank comparison, including adaptive choice of R after seeing either host, not merely an expectation inequality for a fixed pattern.

Consequently, every J⊆G with no root-root edges, at most n/(1000d³) nonroot vertices, root degree ≤s at each nonroot vertex, and all components of J−Y of order ≤d embeds in H fixing Y. This application uses the classical Aharoni–Haxell criterion. The nominated rank comparison itself does not.

## Full proof and source contracts

The complete proof, quantifiers, error bounds, counterexample attacks and application are in [analytic-attempt.md](../experiments/i248_combinatorial_structure_discovery/analytic-attempt.md). The essential paid chain is:

1. Apply the pinned 175 Bernoulli-extension compression to the entire edge requirement of a rooted block; symmetrize its slots.
2. Bound every source R-packing by twice a maximum weighted disjoint packing for the compressed family Q.
3. Compare the expected weighted packing to the expected ordinary Q-packing after independent edge addition, with the correct max/E inequality.
4. Use vertex-block bounded differences to control all compressed families simultaneously.
5. Select maximum packings equivariantly in independent denser layers. Conditional on cardinality they are uniform d-matchings on the nonroots. A permutation martingale controls loss to previously occupied vertices, giving packing amplification up to a linear cap.
6. Union-bound the compressed tests, then transfer the rank estimate back to arbitrary R.

The source's one-vertex Hall proof does not supply step 5 or the maximum-packing comparison. Standard compression, sprinkling, bounded differences, and hypergraph Hall are explicitly credited.

[The source/prior-art record](../sources/i248_combinatorial_structure_discovery/literature.md) contains exact pinned contracts and full read extents. [Input authentication](../experiments/i248_combinatorial_structure_discovery/input-authentication.json) authenticates every retained pinned excerpt against the immutable preprints tree and SHA256. [Reading and failures](../experiments/i248_combinatorial_structure_discovery/reading-and-failures.md) records rejected routes and access limits.

## Contribution case and limits

The proposed contribution is a uniform rank-transfer operation for disjoint rooted configurations with arbitrarily overlapping root requirements. It extends an interface supplied by family 175 in a way that can synchronize bounded connected blocks through the same roots. It does not give arbitrary piece gluing, spanning embeddings, induced embeddings, growing block size, optimal constants/densities, or efficient algorithms.

A serious prior-art comparison is Ferber–Luh–Nguyen, *Embedding Large Graphs into a Random Graph*, arXiv:1606.05923v3, whose entire block-embedding argument §2.4 was read. They already use compatible-block hypergraphs, sprinkling, and hypergraph Hall. Their root sets are disjoint across different blocks and their proof exploits that condition in a Janson calculation. Whether replacing that restriction by a uniform typical-source rank comparison clears the substantiality standard is for the independent contribution gate. It must not be accepted merely because no identical title was found or because d=1 was the only case in the pinned proposition.

MathDB's actual accessible [Goddyn thin-tree record](https://mathdb.com/p/366968/goddyn-s-thin-tree-conjecture) was inspected and reports two indexed source papers; no matching MathDB problem for this rank-transfer theorem was found. No significance score or claim of observed prominence for I248 is made.

## Gate handoff

Request independent reconstruction of the whole rank proof, particularly vertex-block Lipschitzness, symmetrization, conditional uniformity, random-layer amplification, cap/floor arithmetic and the cross-product quantifier. Separately request contribution review against rooted block-transfer and matching-universality literature, including the withdrawn 2609.20864 lead only as a lead, not as a proved result. No further subordinate agent was launched here; the parent owns the gates and shared state.

This submission is neither R017 nor a count increment. It contains no entropy/coefficient-rounding or cycle-decomposition revival. The user-stipulated corpus was not audited.
