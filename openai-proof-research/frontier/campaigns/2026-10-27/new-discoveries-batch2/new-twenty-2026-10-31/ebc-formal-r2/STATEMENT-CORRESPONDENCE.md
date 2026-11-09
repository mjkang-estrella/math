# Statement correspondence

Source carried forward from round 1: Newman, Miranda, Flórez and Narayan,
Uniform edge betweenness centrality, EJGTA 8(2) (2020), 265–300,
Definition 1.1 and Conjecture 2.1, p. 279; arXiv:1709.04773v1.

All round-1 definitions remain byte-identical. `circulant m s` is the loop-free
undirected graph on ZMod m with differences in ±s. `shortestPaths` literally
filters walks of length dist x y by IsPath. `sigma` counts those paths;
`sigmaEdge` filters them on membership of the unordered edge in the walk's
edge list. `edgeBetweenness` sums the rational ratio over all ordered distinct
vertex pairs, including path endpoints and with no extra normalization.
Uniformity compares all actual edges. Edge transitivity uses graph automorphisms
and their action on unordered edges.

`Conjecture21` quantifies over all seven source classes (Fin 7 indices 0–6
represent Classes 3–9) and every natural n ≥ 1, requiring uniformity AND failure
of edge transitivity. The source order and jump formulas are unchanged.
The checked Class 4 n=1 instance is C_32(1,7,9). Unequal betweenness values at
edges {0,1} and {0,9} refute uniformity, hence refute the full conjunction.

Round 1's endpoint required DistanceAndCounts and PathSplitting32. Round 2
proves both Props with no new hypotheses on the endpoint. The first uses
general BFS correctness and kernel-checked all-source local equations. The
second uses a general shortest-path pair bijection and disjoint orientations,
then the certificate-proved connectedness of G32. Arithmetic tables do not
redefine any graph invariant.

The final theorem is exactly
`EBC337062.conjecture21_false_unconditional : ¬ EBC337062.Conjecture21`.
Unreachable pairs retain Mathlib's dist = 0 convention and rational 0/0 = 0;
connectedness is proved for the counterexample rather than assumed in the
conjecture. The general splitting theorem assumes connectedness; the final
endpoint does not. No source novelty or campaign acceptance is asserted.
