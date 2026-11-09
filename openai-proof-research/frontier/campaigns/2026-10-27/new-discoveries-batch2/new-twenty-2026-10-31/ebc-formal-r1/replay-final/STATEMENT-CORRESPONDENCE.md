# Statement correspondence

Source: Newman, Miranda, Flórez and Narayan, Uniform edge betweenness
centrality, EJGTA 8(2) (2020), 265–300, Definition 1.1 and Conjecture 2.1,
p. 279; arXiv:1709.04773v1. Required dossier and review gates A, B and E were
read before implementation. TASK.txt controls this lane.

* `circulant m s` is on ZMod m, for an arbitrary jump set s. Adjacency means
  unequal vertices and either x-y ∈ s or y-x ∈ s. This is the source's ±jump
  undirected adjacency with loops removed.
* `shortestPaths` consists of walks w with w.length = G.dist x y AND w.IsPath.
  Counting this finset counts paths, not an unrelated matrix surrogate.
* `sigmaEdge` filters those paths on the literal unordered edge in w.edges.
* `edgeBetweenness` sums the rational ratio over all ordered x,y with x ≠ y.
  Endpoints count and no extra normalization is applied.
* `EdgeBetweennessUniform` compares all actual edges. `EdgeTransitive` uses
  graph automorphisms and their Sym2.map action on unordered edges.
* `classData` uses Fin 7 indices 0..6 for source Classes 3..9 respectively.
  Orders are written as (one less than the source constant) + variable term
  + 1. These are identically the seven source formulas, including at n = 1.
  `class4_n1` is a checked definitional equality to (32,1,7,9).
* `Conjecture21` states uniformity AND failure of edge transitivity for every
  one of these indices and every n ≥ 1. The endpoint refutes precisely this
  Prop, but conditionally on the two explicitly listed combinatorial bridges.
* Arithmetic tables and layer equations do not redefine the graph invariant.
  Their connection to the literal path invariant remains an explicit premise.

Unreachable pairs use Mathlib's dist = 0 convention; their path count is zero
for distinct endpoints and the rational ratio uses 0/0 = 0. This does not
change the intended connected circulant instance. No additional connectedness
hypothesis weakens Conjecture21.
