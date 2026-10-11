# I182 analytic record: the controlled extension reduced, survival unpaid

No new graph, parameter, triple, attachment or population was tested.
The only new enumeration runs on the one retained, frozen, authenticated
I177 glued graph (the same graph the mandatory controls re-examine) and
on the abstract two-square patch.

## 1. Exact setting

The glued graph `G` is cubic, simple, planar, bipartite and a brace
(`graph_check` with the retained 900 matching extensions re-verifies all
of this on the retained graph). The patch is two quadrilateral faces
sharing exactly the chord edge `xy`, with simple boundary
`C=(x,a,b,y,d,c,x)` disjoint from the five ports, alternating halves
`A={xa,by,dc}` (the half used by the lost packing `p`) and
`B={ab,yd,cx}`, and continuation edges at `a,b,c,d` with external
terminals `a',b',c',d'`. By I181's forcing lemma (re-audited fresh in
the mandatory control: exactly one degree-correct local subset per exact
half, chord and all four continuations forced, terminal pairing
`{a'b', c'd'}`), any perfect matching `M` containing `A` has complement
`H=G-M` whose patch restriction is forced to be

```text
S = B + xy + (a-a') + (b-b') + (c-c') + (d-d'),
```

two forced paths `a'-a-b-b'` and `c'-c-x-y-d-d'`.

## 2. Reduction lemma (proved; certified on all 626 retained cases)

Let `G' = G - V(C)` (six fewer vertices; 24 in the retained graph), with
every vertex cubic except the four terminals, which have degree two. Deleting
`A` is a bijection between `A`-containing perfect matchings of `G` and
perfect matchings `M'` of `G'`, and

```text
G - M = (G' - M') union S.
```

Every vertex of `G' - M'` has degree two except the four terminals,
which have degree one; hence `G' - M'` is a disjoint union of cycles and
exactly two paths whose four endpoints are the terminals. Attaching the
two forced paths joins terminals `a'` with `b'` and `c'` with `d'`.
Therefore `G - M` is one Hamiltonian cycle if and only if

- `G' - M'` has no closed component, and
- its two paths pair the terminals crosswise,
  `{a',c'}&{b',d'}` or `{a',d'}&{b',c'}`, not `{a',b'}&{c',d'}`.

(The parallel pairing closes each forced path separately and gives two
cycles.) If some continuation terminals coincide, the same statement
holds on the quotient multigraph; the retained instances all have four
distinct terminals, and the certificate checks the equivalence for every
perfect matching of every retained instance (626 checks, no exception).

The port pairing and used cut labels of `H` are read off from
`H' = G' - M'` alone, because the cut edges and ports all lie in `G'`.
So E182 is *exactly* a property of the perfect-matching population of
the explicit derived graph `G'`:

> **(CPTP-survival)** `G'` has a perfect matching whose complement is an
> acyclic cross-paired two-path graph **and** whose cut-label set and
> pairing form one of the eleven survivor types.

Equivalently, in the auxiliary cubic bipartite multigraph
`G'' = G' + {a'b', c'd'}`, a Hamiltonian cycle through both contracted
edges with surviving cut usage.

## 3. The topological half is always payable; only survival is missing

Because `q = p triangle E(C)` lies in the *complete* lost fibre, any
compatible exterior partner of `q` glues to a Hamiltonian cycle `H0`;
its complement `M0` contains `A`, so `M0'` is a cross-paired acyclic
two-path complement in `G'`. Its local restriction is `q` itself, of
lost type `(01;01)`. Hence under the exact E182 hypotheses:

- control (1) (`A` contained) and control (2) (Hamiltonian complement)
  are *simultaneously* achievable, certified by `M0`;
- the entire unpaid content is control (3): the nonempty cross-paired
  population must contain a member whose port pairing is not one of the
  two lost types `P=(01;01)`, `D=(0134;01,34)`.

This is strictly sharper than I181's isolation of the problem: the
patch, the three-edge prescription and the Hamiltonianicity are all
eliminated; what remains is a single four-terminal pairing-plus-survival
predicate on one derived graph.

## 4. What the retained graph certifies (finite, not a proof)

The retained I177 graph contains exactly three port-disjoint internal
two-square patches — the ladder squares

```text
(14,15,23,22)+(15,16,24,23),  (15,16,24,23)+(16,17,25,24),
(16,17,25,24)+(17,18,26,25),
```

whose boundaries are the first three retained six-cycle moves. (A fourth
ladder patch meets port 19; three further quadrilateral pairs are not
internal to `X`.) Each patch gives both directed instances, six in all,
each with `p,q` both in the complete retained lost fibre.

On every instance the certificate enumerates every perfect matching of
`G'` (111, 111, 102, 102, 100, 100) and finds:

- 8 matchings with Hamiltonian complement on each instance;
- of these, exactly 5 are controlled (survivor fibre) and 3 are lost
  with type `P` (one is the `q`-completion);
- the controlled matchings hit exactly fibres 5, 6 and 9 — the three
  witness states of the retained helper graph;
- conversely, every survivor packing using the opposite half (3 per
  instance) times every compatible exterior partner (5 single-cycle
  products per instance, 9 disconnected equal-pairing products correctly
  excluded) reproduces exactly the 5 controlled matchings.

So on the only authenticated instance population, E182's conclusion
holds, and the controlled matchings are precisely the helper products.
This is finite confirmation, not a general proof, and it supplies no
refutation: a refutation needs an actual construction in which *every*
cross-paired acyclic complement is lost, and no such graph is available
within the freeze (new graph tests are not authorized).

## 5. Why the stipulated theorems do not close it

- Brace two-extendability prescribes two disjoint edges in a perfect
  matching; the CPTP condition is a constraint on the *complement's*
  component pairing plus a port-survival condition, not an edge
  prescription.
- The pinned `cor:pfaffian-paths` (every three-edge path lies in a
  Hamiltonian cycle of a cubic 3-connected bipartite Pfaffian graph)
  forces one connected `P4`, e.g. `c-x-y-d`. The required prescription
  in `G''` is *two disjoint edges simultaneously* (`a'b'` and `c'd'`),
  plus survival of the cut-label set — a strictly stronger and different
  shape of control. No reduction of the two-edge prescription to one
  `P4` prescription preserving simplicity, bipartition, planarity or the
  Pfaffian property of `G''` was found; contracting or deleting to merge
  the two edges destroys cubicness or creates the prescription's own
  edges.
- `cor:edge-avoidance` and `thm:main` are pure existence statements.
- The elevenfold fibre nonemptiness supplies packings of each type
  somewhere in `X`, never prescribed on the patch.
- D168's bidirectional shortcut remains false and is not used.

## 6. Sharper missing condition and one bounded next action

Missing condition (CPTP-survival above): within the provably nonempty
cross-paired acyclic two-path complement population of `G'`, some member
avoids the two lost port types. Bounded next action: prove or refute
that the lost `(01;01)` exterior routing of the `q`-completion can be
re-routed inside the fixed exterior `Y` to a surviving pairing while
preserving the cross pairing of the two terminal paths — equivalently,
decide CPTP-survival for the derived quadruple `(G'; a',b',c',d')`; a
refutation is an actual written `X` meeting every H180 hypothesis in
which all cross-paired complements have lost port pairing.
