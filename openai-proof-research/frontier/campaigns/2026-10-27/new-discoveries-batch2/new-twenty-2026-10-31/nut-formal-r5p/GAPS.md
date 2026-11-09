# Incomplete: Coverage8 is absent; zero credit

The root-fixed interface has not been found false or unworkable. It and all
inherited modules remain byte-identical. No interface repair was attempted.
No unconditional finite obstruction or target is proved. Root acceptance is
required, and none is claimed. Counts remain 20/40 beyond the previous 39.

## Coverage progress and precise remaining obligations

1. Complete: `catalogueGraph` is a genuine simple graph for every natural code.
   `SimpleCode` gives the required symmetry and absent diagonal bits.
   `catalogue_simple_1` through `catalogue_simple_8` prove SimpleCode for every
   member of the actual inherited lists (and [0] at order one).
   `catalogueGraph_adj` therefore gives their exact adjacency specifications.
2. Complete at the labelling/encoding level: `extendLabels` extends an arbitrary
   permutation of the deleted graph, sends castSucc i to v.succAbove (e i),
   and sends the new last vertex to v. `transportedMask` records the transported
   neighbourhood. `transportedMask_lt` and `transportedMask_bit` prove its bound
   and its precise adjacency interpretation.
3. MISSING: prove `eligibleNeighbors n a (transportedMask G v e) = true` from
   connectedness and the subcubic bound, when a represents the deleted graph
   under e. Specifically: prove the filtered mask list is nonempty; its length
   is at most three; each selected old vertex has deletion degree strictly less
   than three; identify `graphDegree n a i` with that deletion degree. The latter
   strict inequality must use the extra edge to v, not just the inherited
   non-strict deletion bound.
4. Complete: `encodeBits_testBit`, `row_encode_testBit`, `grid_testBit`, and
   `extendGraph_testBit` prove no-carry row-major bit encoding for arbitrary
   orders. `transported_extension_spec` then proves the exact transported graph
   adjacency, including all cases involving the new vertex, assuming only the
   old adjacency specification.
5. MISSING: the universal catalogue induction. Establish the one-vertex base;
   combine the actual per-source closure theorems at each order into a usable
   membership-indexed closure lemma; perform deletion induction using item 3
   and `transported_extension_spec`; specialize at order eight to the connected
   subcubic `supportGraph`; convert the graph isomorphism to the permutation and
   `SupportCode (C.submatrix e e) code` required by `Nut8.Coverage8`.

## Composition and conditional assembly

`finite_of_parts (hc : Coverage8) (hp : PerSupport) : FiniteObstruction` is proved.
`target_of_parts (hc : Coverage8) (hp : PerSupport) : Target` is also supplied,
using r4a's unchanged endpoint. Both retain their two explicit assumptions.
The exact requested `FinalEndpoint.lean` source imports `Coverage8` and states
`nut8_target (hp : PerSupport) : Target`. It is NOT compiled when Coverage8.lean
is absent. It must not be treated as a checked declaration. PerSupport remains
assigned to the separate r5q lane; this lane does not inspect or modify it.

## Validation limits and deviations

The replay compiles and checks only the partial module list in modules.json.
A successful replay, audit and rejected negative controls do not prove Coverage8
or constitute acceptance. See the fresh replay receipts for actual outcomes.

Two capped development Lean calls briefly overlapped: the first BitEncoding
trial ran while the initial dependency build was active. This violates the
one-heavy-process-at-a-time rule. Both retained their individual watchdogs and
logs, and all later calls and the fresh replay are sequential. No other resource
relaxation was made. Failed development logs were retained with unique names.
