# MathDB 350979: an order-15 obstruction to circulant realization

Status: candidate, not accepted. All campaign counts remain unchanged.

The exact source is Tuite–Thomas–Chandran, arXiv:2106.06827, Conjecture 4.5. Its assertion is that for every n ≥ 11 there is a circulant graph with order n, diameter two, and monophonic position number two. A monophonic position set contains no three distinct vertices of any induced path. The source Theorem 4.4 concerns unrestricted graphs, not circulants. Its computational verification through order 32 therefore does not contradict the obstruction below. The general-position survey arXiv:2501.19385, §4, repeats the same conjecture and explicitly identifies a circulant as a Cayley graph of a cyclic group.

## Theorem

Every circulant graph of order 15 with diameter two has monophonic position number at least three. Consequently Conjecture 4.5, and the reserved MathDB statement interpreted in its source scope, is false.

## Proof

Label the vertices by the cyclic group Z/15Z. An undirected simple circulant is determined by a subset of the seven pairs of differences ±1, ..., ±7. There are exactly 2^7 = 128 possibilities. Use bit d, for d = 0,...,6, to select difference ±(d+1).

The finite classification is as follows. If a graph is triangle-free at vertex 0 and every vertex has distance at most two from 0, its mask is either 41 or 70. The respective positive difference sets are {1,4,6} and {2,3,7}. For both masks the three distinct vertices 0, 5, 10 have identical open neighborhoods. The classification is kernel proved in `Circulant.classify` (qualified namespace `Circulant350979`), with the two neighborhood equalities kernel proved separately. The independent Python certificate `outputs/order15-certificate.json` records an explicit triangle or a distance obstruction for every other mask: 109 triangle cases, 17 distance cases, 2 twin cases. No graph is omitted up to labelling; quotienting by isomorphism is unnecessary.

A triangle is a monophonic position set of size three. Indeed, if all three vertices lay on an induced path, their three indices would have to be pairwise consecutive, which is impossible.

Three distinct vertices having identical open neighborhoods also form a monophonic position set. Suppose an induced path contained all three. The path has positive length. Choose a path neighbor q of the first of these vertices. Identical neighborhoods imply that q is adjacent to all three vertices. Since the path is induced, q's index would have to be consecutive to three distinct indices. An integer has at most two consecutive neighbors, a contradiction. This argument does not assume any bound on the length of the path.

Now take any circulant graph of order 15 with diameter two. Its mask has every vertex within two steps of 0. If the graph contains a triangle at 0, the first lemma supplies a three-vertex monophonic position set. Otherwise the classification and the second lemma supply {0,5,10}. Thus the monophonic position number is at least three, as asserted.

## Formal endpoint and semantic bridges

`Circulant350979.source_refutation : ¬ Circulant350979.SourceClaim` is the full universal source refutation. `SourceClaim` quantifies over every n ≥ 11 and every jump set in ZMod n. It uses mathlib's `SimpleGraph.circulantGraph` and `SimpleGraph.diam`, and the explicitly defined maximum size `mpNumber` of a monophonic position set.

`InducedPath R m f` states that f : Fin (m+1) → V is injective and that adjacency of two image vertices holds if and only if their indices are consecutive. This is precisely an ordinary simple induced path, indexed in its vertex order. All lengths m are quantified, with no diagnostic length cutoff. `MonophonicSet` excludes every triple of distinct set members from every such path. `mpNumber` is the maximum cardinality over all subsets satisfying this condition. The proof explicitly transfers a three-vertex obstruction to a cardinality lower bound.

`Bridge.represent` proves that every arbitrary jump set on ZMod 15 is represented by one of the 128 masks, including asymmetric jump sets (mathlib symmetrizes them) and zero jumps (mathlib removes loops). `radius_of_diam` derives the two-step condition from mathlib's actual diameter. The endpoint therefore does not replace graph semantics by a bounded checker predicate. The order is exactly 15 and satisfies the source lower threshold 11.

## Significance and prior-art limits

This is a universal finite nonexistence result refuting a human-posed existence conjecture. It is not the assertion that one particular graph fails, nor a change of graph-order, density, endpoint, or path conventions. The residual graphs are familiar independent three-fold blow-ups of C5 (up to cyclic relabelling); their familiarity is disclosed. The new obstruction is the exhaustive elimination of all other circulants at order 15. Source clique bounds and multipartite formulas alone do not supply that classification. No theorem read in the source supplies it through symmetrization, iteration or addition. Whether the finite obstruction meets the campaign's substantive standard is reserved to independent review and the root.

Historical ID/title screen found no earlier technical exclusion of this ID in the checked notes. The live OpenAI/math head was 4eaee87548250b2682affda7d05d947c05554bae and Omega head c63ab162315fddd0801cbe9f47dbf3eda6e13360, matching the root's recorded revisions. Complete cached D5/Problems/preprints path listings were hash-bound and screened for Monophonic, Tuite and Circulant. No matching monophonic theorem appeared; other circulant paths are listed in `outputs/candidate-registry-paths.json`. This is a path screen, not a semantic reading of all registry proofs. The current source, its cited monophonic-position precursor, and the current survey were inspected selectively. Search queries and primary HTTP receipts are retained. The publisher/repository final PDF request returned 403 and was not retried or bypassed; the journal body is not independently authenticated. No complete citing-literature, deleted-history or worldwide novelty claim is made.

## Verification and trust

Run `./run.sh` from this directory. It makes a source-only ZIP, extracts fresh copies, strictly recompiles the three proof modules and audit module, audits all local declarations including generated declarations, and runs leanchecker. Results and full logs are in `replay/` and `logs/`. Only propext, Classical.choice and Quot.sound are permitted. No sorry, admit, added axiom, unsafe declaration, native_decide or ofReduceBool is used. Kernel `decide` checks the finite classifications.

The Lean version is 4.34.1. The external mathlib source/cache is the supplied pinned revision d13f23b723b8a846827a245b89c10fc7d3f11612 and is read-only. External prebuilt oleans are trusted; this is not a full upstream rebuild or source-to-olean attestation. Leanchecker uses the same Lean installation, so is not an independent foundation. Sampled process-group RSS enforcement is not a transient-peak/cgroup guarantee. Earlier diagnostic wrapper receipts measured only the launched process, as their field names explicitly state. The final replay uses process-group sampling, 2 CPUs, CPU limit 120 seconds per process, wall 140 seconds, RSS cap 6 GiB and the explicitly permitted 64 GiB virtual-address limit. An earlier 12 GiB address-space replay failed to map an existing upstream private file; the permitted 64 GiB replay passed. No upstream files were edited or rebuilt.

Final registry refresh: Omega advanced to 3409c20e34b82de35b950c7b78c259e712387b58 (2026-11-02 10:19:24 UTC). The frozen-base-to-final compare, retained with an HTTP receipt, contains 51 changed files over 36 commits (below API truncation caps). No Monophonic, Tuite or Circulant path is in the delta. See outputs/registry-final-screen.json. OpenAI/math remained unchanged. This extends the cached path screen to the final retrieved head; it still does not claim all-proof semantic clearance.
