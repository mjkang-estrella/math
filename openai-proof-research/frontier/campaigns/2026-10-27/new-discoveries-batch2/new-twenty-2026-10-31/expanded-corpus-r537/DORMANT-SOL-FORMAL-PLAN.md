# Dormant formal plan: MathDB 362080

No dispatch. Nothing here has been compiled; this lane runs no Lean. The file name is the one the task requires and does not imply any model assignment.

## Literal endpoint

For every k >= 1 there are c > 0, C > 0 and n0 such that for all n >= n0 and every tree T on Fin n,

    c * n^(k-1) <= treewidth (tokenGraph k T) and treewidth (tokenGraph k T) <= C * n^(k-1).

## Definitions the statement needs

- `tokenGraph k G`: a `SimpleGraph` on `{s : Finset V // s.card = k}`, with A ~ B iff the symmetric difference of A and B is an edge of G.
- `TreeDecomposition H`: a finite index type, a `SimpleGraph` on it with `IsTree`, bags as `Finset` of vertices, covering of vertices, covering of edges, and connectedness of each vertex's bag set. Mathlib has no treewidth, so this is lane-defined and needs fidelity review.
- `treewidth H`: the minimum over decompositions of the maximum bag size minus one. A faithful alternative that avoids a universe issue is to state the two inequalities directly: there exists a decomposition of width at most C n^(k-1), and every decomposition has width at least c n^(k-1).

## Modules, in order of cost

1. Definitions and elementary lemmas. Cheap.
2. Upper bound. Decomposition combinators: add a set to every bag; disjoint union, which needs gluing index trees into one tree; Cartesian-product bags V(A) x W. Centroid of a tree; Mathlib has `SimpleGraph.IsTree` but no centroid lemma. Token-vector partition after removing S, and the Cartesian-product isomorphism for several components. Probably the most expensive part, because the gluing and product isomorphism are bookkeeping heavy.
3. Balanced separator from a tree decomposition: the orientation and double-oriented-edge argument on a finite tree.
4. Lower bound. Route definition with hand-off along the unique tree path; it is cleaner to define by recursion on a list path with a head-first phase structure. Walk validity. Load counting as an injection from routes through Z into a product of `Fin` ranges, with Case A and Case B.
5. Final arithmetic on natural numbers and casts to reals.

## Imports and risk

Specific imports only; a whole-library Mathlib import is excluded by the campaign's Lean update. Likely imports: `SimpleGraph.Acyclic`, `SimpleGraph.Connectivity`, `Finset.Powerset`, `Fintype.BigOperators`, basic real order. No measure theory, no analysis, no polynomials.

Estimated size: 1500 to 2500 lines (author estimate only; nothing has been compiled). The highest formal risk is the disjoint-union gluing and the multi-factor Cartesian isomorphism. A simplification worth trying is to prove the upper bound through an inductive "bag tree" datatype and transport it to a `SimpleGraph` tree only once at the end.

## Faithfulness checks to pay later

- Controls: the star and path small cases, and a wrong-exponent negative control.
- Standard axioms only: propext, Classical.choice and Quot.sound.
- Independent review that `TreeDecomposition` matches the source definition in Section 1 of arXiv 2402.17962v3.
