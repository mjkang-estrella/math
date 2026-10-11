# I181: two-square six-cycle helper

2026-10-11. Research iteration following I180. This is not an upstream
truth audit, a completeness claim, or a literature-priority claim. All
OpenAI results at the pinned commit are stipulated true.

## Verdict

**E181 remains UNRESOLVED.**

I180's finite helper graph and helper witnesses are authenticated and
replayed. The two-square patch has a precise local reattachment lemma:
once an actual cycle-free survivor helper using the opposite half of the
six-cycle exists, toggling that six-cycle automatically preserves its
type, endpoint pairing and acyclicity. The same argument also explains
why a lost packing and its six-cycle toggle have the same local routing.

The missing step is existence of that helper. None of the supplied
elevenfold fibre nonemptiness, brace extension, Pfaffian/P4 existence,
edge avoidance, or the I180 helper witness constructs a packing with the
required simultaneous six-cycle prescription and proves that it lands in
a surviving fibre. No new graph search was run and no hidden graph
population was imported.

The accepted count remains **8**; this report claims no ninth accepted
finding.

## Authenticated inherited state

The supplied detached I180 anchors authenticate exactly:

- report SHA-256
  `ee97afc179f45d40644f935d05956db17a785560fc249f5d47159b0ad2b42322`;
- seal SHA-256
  `0edee6b86197f691803982fb695396b5102cbf100a307dab6cd10c7900c8abda`;
- verifier SHA-256
  `4b5dbdbe7b518529b145c6ee2bb6a5562c235a56634c513365485a5dc098070e`.

Before any I181 mathematical diagnostic, `auth181.py` froze
`inputs.json` with **972 strict bindings and four context bindings**.
It checked I180's 44 owned files, 913 strict external files, all
ancestor inventory/control/context/membership chains through I175, and
15 parent evidence files. The I179 final integration receipt was already
present in I180's original freeze, so no supplement was needed.

The fresh code was developed only after that freeze. Ancestor Python was
read only for schemas and certificate interpretation; it was never
executed, imported, compiled or copied as implementation.

## Scoped replay verdicts

| Scope | Verdict |
| --- | --- |
| U176 k=6 port-minor words | PASS for the retained U176 certificate, with exact same-matrix minor checks; not an independent theorem re-proof. |
| I177 adjacent absorption | PASS for the 24 mask exact-one checks, 16 all-zero records, 34 under witnesses and four cycle failures. |
| I178 five-port presentation/completion | PASS for 15 complete fibre entries, 22 anchor changes and six distinct residuals. |
| I179 exterior lock | PASS for 18 masks, nine single switches, eight cycle failures, rank 4 and the partition `[[1,2,3,7],[4,5],[6,8]]`. |
| Parent helper certificates | PASS for all 15 local/exterior pairing records. |
| I180 helper connectivity | PASS for the full retained graph: 130 overlays, 123 moves, five nodes, path edges `[[0,1],[1,2],[2,3],[3,4]]`, 24 witnesses and 99 rejects. |
| E181 actual six-cycle helper | **UNRESOLVED**: local reattachment is proved, actual survivor-helper existence is not. |

These replay verdicts do not broaden any predecessor claim. In
particular, I178's 15 entries are lost-fibre completeness records, not
survivor-count equality; I180's 24 witnesses are port-state moves, not a
global Hamiltonian-completion theorem.

## Mandatory replay

`run181.py mandatory` succeeded on `mandatory-attempt-05` in
3.455264144926332 seconds. It evaluated the mandated controls in the
exact order

```text
0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539,
431, C171, G6/G10, first_P8, I176_k6,
I177_child_absorption, I178_relations_completion,
I179_lock, parent_helper, I180_helpergraph
```

The successful payload is 1,935,398 bytes with SHA-256

```text
29c2240943d5f45b2ad44558e6c2fea9012d31e2823a157844c121d908f6aa94
```

Fresh exact arithmetic used integer primitive-row elimination and an
independent reversed transpose Fraction elimination for ranks; a
Fraction determinant independently checked nonsingularity where
applicable. The payload rechecks the twelve indexed controls, C171
(`F=1/14`, distinct `T=-1/2`, valid extension and signature data),
G6/G10, both nonbraces, the first I175 P8, and all ancestor controls.

The I180 replay recovers

- path distances from `p4`: `[8, 8, 8, 6, 0]`;
- state ranks `[4, 5, 5]`;
- 99 rejects, all through a cycle in the lost-side output;
- 12 exact-sum forward witnesses in the independent prescribed-port
  enumeration, matching the retained witness directions.

## Local six-cycle theorem

Label the common edge `xy` and the simple boundary

```text
C = (x,a,b,y,d,c,x).
```

The alternating halves are

```text
A = {xa, by, dc},      B = {ab, yd, cx}.
```

Every vertex of `C` is internal and cubic. At `x` and `y`, the only
incident edges inside or leaving the two-face disk are the two boundary
edges and the chord `xy`. At each of `a,b,c,d`, the third incident edge
is the unique continuation leaving the disk.

Suppose a lost packing `p` uses exactly `A` on `C`. Degree two forces
`xy` and the four continuation edges. A helper `u` for which `C` is a
whole alternating component must use exactly `B`; degree two forces the
same chord and same continuation edges. Hence the third edge at every
vertex of `C` is common to `p` and `u`, and `p triangle u` contains `C`
as an entire component.

On the four continuation terminals, the two local sets induce the same
abstract pairing:

```text
A + xy:   a-x-y-b   and   c-d
B + xy:   a-b       and   c-x-y-d.
```

Thus both connect `a` to `b` and `c` to `d`. Replacing one local
routing by the other preserves the component partition of every
unchanged segment decomposition. The fresh topology certificate also
checks this with loops and parallel two-edge components retained rather
than contracted away. Its routings are

```text
A -> [[1,0,3,2],[4,5]]
B -> [[1,2],[4,3,0,5]]
```

so both have two components and no closed segment cycle.

Therefore, if `u` is an actual spanning cycle-free packing in a survivor
type, then `v=u triangle E(C)` automatically:

1. is spanning and degree-correct;
2. uses the opposite local routing;
3. has the same number of components and the same port pairing as `u`;
4. remains cycle-free; and
5. satisfies `p+u=q+v` coordinatewise when `q=p triangle E(C)`.

The topology payload is 102,060 bytes with SHA-256

```text
4c0ab64811a25094a5f001466695a036128742bb07a39e2e70afcd148b38320f
```

It ran in 0.025397118995897472 seconds and is a formal
segment-incidence lemma, not an existence proof.

## Precise unpaid condition

The missing graph-structural condition is a **controlled
three-edge alternating-half extension**.

A global Hamiltonian completion of the lost toggle `q` has a
complementary perfect matching containing the three disjoint edges of
`A` (the half used by `p`). This proves that the three-edge set is
matchable, but the known complement has local restriction `q`, a lost
packing. E181 requires a perfect matching `M` containing those same
three edges such that:

1. `G-M` is one Hamiltonian cycle;
2. its restriction to `X` has the opposite-half local data required
   above; and
3. that restriction lies in one of the eleven stipulated nonempty
   survivor fibres.

Brace extension supplies perfect matchings through two disjoint edges,
not this controlled three-edge class. The pinned P4 theorem can force
one three-edge path such as `c-x-y-d`, but it does not also force the
separate edge `ab`, the four continuation edges, a cut condition, or
membership in a surviving pairing fibre. Edge avoidance is likewise an
existence statement without those simultaneous controls. No reduction
to a smaller instance preserving the exact H180 interface and lifting an
actual packing was established.

This is sharper than merely saying "helper existence is missing": the
reattachment side is automatic, and only the controlled matching/helper
existence statement remains.

## One bounded next action

Prove or refute the controlled alternating-half extension lemma above
under the exact H180 hypotheses. A positive proof must produce the
A-containing perfect matching with Hamiltonian complement and identify
its local restriction in a survivor fibre; a counterexample must satisfy
the complete H180 graph/interface/brace hypotheses and have a lost pair
`p,q=p triangle E(C)` for which every such matching complement has a
lost local restriction. No broader census, parameter sweep or parent
verdict should be bundled with that test.

## Failure and attempt ledger

All failed attempts and empty captures are retained under the I181
experiment package:

1. a pre-diagnostic schema probe treated the retained `I176_k6` object
   as a list;
2. `mandatory-attempt-01` treated retained edge-index extension records
   as nested endpoint pairs;
3. `mandatory-attempt-02` searched for analytic witness name `6(n-1)`
   where the retained certificate uses `6r4`;
4. two read-only schema probes failed while locating `embed` and scalar
   fibre cardinalities;
5. `mandatory-attempt-03` treated retained cardinality fields as
   vectors/lists;
6. `mandatory-attempt-04` completed the controls but hit a
   relative/absolute exclusive-output guard bug;
7. `mandatory-attempt-05` then passed.

No failure artifact was overwritten or resealed. `failures.md` gives the
exact observed causes and empty-output status.

## Package links

- [I181 brief](iteration181-six-cycle-helper-brief.md)
- [I181 experiment package](../experiments/i181_six_cycle_helper/)
- [I181 source receipt](../sources/i181_six_cycle_helper/literature.md)
- [analytic record](../experiments/i181_six_cycle_helper/analytic-attempt.md)
- [failure ledger](../experiments/i181_six_cycle_helper/failures.md)
- [frozen inputs](../experiments/i181_six_cycle_helper/inputs.json)
- [mandatory payload](../experiments/i181_six_cycle_helper/mandatory-attempt-05.json)
- [topology payload](../experiments/i181_six_cycle_helper/topology-attempt-01.json)
- [I180 report](i180-survivor-helper-connectivity.md)
- [I180 parent disposition](i180-survivor-helper-connectivity-parent-disposition.md)

Detached report, seal and verifier hashes, with final replay runtime,
are returned outside this file so the report need not embed a
self-referential digest.
