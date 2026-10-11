# I182: controlled three-edge alternating-half extension

2026-10-11. Research iteration following I181. This is not an upstream
truth audit, a completeness claim, or a literature-priority claim. All
OpenAI results at the pinned commit are stipulated true.

## Verdict

**E182 remains UNRESOLVED.**

The controlled three-edge alternating-half extension is reduced to an
exact, checkable predicate on one derived graph, and the reduction
splits the problem into a topological half that is *always* payable and
a survival half that remains unpaid. Precisely: under the exact E182
hypotheses, an `A`-containing perfect matching with one Hamiltonian
complement always exists (the completion of the lost toggle `q`
certifies it); the entire open content is whether any member of that
provably nonempty population has a surviving local fibre. No proof of
that survival and no actual refuting construction was obtained. On the
one retained authenticated instance population (six directed instances
on three two-square patches of the I177 graph), the conclusion holds:
each instance has exactly five controlled matchings, realizing exactly
survivor fibres 5, 6 and 9, and these are precisely the products of the
three known witness helpers with their exterior partners. This finite
confirmation is not a general proof, and no counterexample graph is
available within the authorized scope.

The accepted count remains **8**; this report claims no ninth accepted
finding. E181, H180 and L179 remain separately UNRESOLVED.

## Authenticated inherited state

The supplied detached I181 anchors authenticate exactly:

- report SHA-256
  `446f5bbb28e249744903ad32d04e9b264979ff2e9a77ef2f107bce93e36d4e46`;
- seal SHA-256
  `22c454fbfd8806aaaa061ddf997e298fec1c27b5e4d9f4d8b6af2202219374e3`;
- verifier SHA-256
  `dd9a02176ef4f6c94e1f732f3c89dd39a59277cbaac72caffe5b6910c897f47b`.

Before any I182 mathematical diagnostic, `auth182.py` froze
`inputs.json` with **1,014 strict bindings and four context bindings**
(29 I181 owned files + 972 I181 strict external + 16 I182-bound parent
evidence files, less three overlaps already counted). It verified all
I181 package bytes, the 972 strict ancestor bytes, the I181 seal /
prevalidation / inventory cross-hashes, the exclusive membership of the
I181 package (29 files plus the three generated control files), and the
ancestor inventory/control/membership chain for iterations
175–181 (94/59/78/81/122/44/29 owned). All sixteen i181-parent evidence
files are bound: disposition, both briefs, the dispatch archive,
validator, integrator, replay script, replay stdout/stderr, precheck,
verification, certificates and the I181 final integration receipt —
which arrived before this freeze, so no supplement was needed and the
freeze was written once. Ancestor Python was read only for schemas and
certificate interpretation; it was never executed, imported, compiled or
copied as implementation.

## Scoped replay verdicts

| Scope | Verdict |
| --- | --- |
| Twelve indexed controls 0,520,…,431 | PASS, recomputed fresh from the retained I169 audit rows and checked against both the I180 and I181 retained payloads; actual `b`, `beta`, `c` and residual identities with vertex-sum vanishing; `ell - t = delta_V + epsilon - delta_R`; two exact rank methods agree on every rank. |
| C171 F versus T | PASS: `F = 1/14` distinct from `T = -1/2`, both two-component factors, valid extension and switch data; 1,032 extensions re-validated. |
| I172 G6/G10 | PASS: both remain nonbraces with the explicit unextendible pairs; full perfect-matching exhaustion. |
| First I175 P8 | PASS, with graph and brace checks. |
| I176 k6 | PASS: words, witnesses, anchors, local minor determinant `-2`, image minor determinant `1`. |
| I177 child/absorption | PASS: 64 cycles, 46 survivors, rank 16, loss zero, three absorption equations with actual `tau` transports. |
| I178 relations/completion | PASS: four relations, kernel `W_X + <K1..K4>`, 22 anchor changes, complete residual checks; the fresh presentation section is byte-equal to the retained I181 section. |
| I179 lock | PASS: 18 masks, nine single switches, eight cycle failures. |
| Parent helper | PASS: twelve identities, three single-cycle states 5/6/9. |
| I180 helper graph | PASS: 130 overlays, 123 moves, 24 witnesses, 99 lost-output cycle rejections, path `p0-…-p4`, distances 8,8,8,6,0, ranks 4,5,5. |
| I181 patch/reattachment | PASS fresh: ten degree-correct abstract local subsets, exactly one per exact alternating half, chord and continuations forced, terminal pairing `{a'b',c'd'}`; the 120-row reattachment table recomputes byte-identically; loops and parallel pairs retained as cycles. |
| E182 controlled extension | **UNRESOLVED**: reduced to CPTP-survival (below); topological half always payable; survival half unpaid; retained instances all confirm the conclusion. |

These replay verdicts do not broaden any predecessor claim.

## Mandatory replay

`run182.py mandatory` succeeded on `mandatory-attempt-05` in
3.456681738025509 seconds, evaluating the mandated controls in the exact
order

```text
0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539,
431, C171, G6/G10, first_P8, I176_k6, I177_child_absorption,
I178_relations_completion, I179_lock, parent_helper,
I180_helpergraph, I181_patch_reattachment
```

The successful payload has SHA-256

```text
c3806b7572ef3a6ddc6729436c9bfe6edd55c7d877d60351cc46fce1644f7cd6
```

Every rank is computed by primitive integer row elimination and
independently by reversed-transpose Fraction elimination, with equality
asserted at every call; determinants are checked by exact Fraction
elimination with a full-rank assertion.

## The reduction lemma (new, proved)

Write the patch boundary as `C=(x,a,b,y,d,c,x)`, chord `xy`, halves
`A={xa,by,dc}`, `B={ab,yd,cx}`, and let `a',b',c',d'` be the external
endpoints of the four continuation edges. Let `G' = G - V(C)`.

**Lemma.** Deleting `A` is a bijection from `A`-containing perfect
matchings of `G` to perfect matchings of `G'`. Under it,
`G - M = (G' - M') + S` with `S` the forced two-path local set
`B + xy +` continuations, and `G - M` is one Hamiltonian cycle if and
only if `G' - M'` has no closed component and consists of two paths
pairing the terminals crosswise (`{a',c'}&{b',d'}` or
`{a',d'}&{b',c'}`). The used cut labels and port pairing of `G - M`
are determined by `G' - M'`. If continuation terminals coincide, the
same statement holds on the quotient multigraph.

*Proof.* `A` saturates exactly `V(C)`, giving the bijection. Every
vertex of `G'` is cubic except the four terminals (degree two), so in
`G' - M'` all vertices have degree two except the four terminals, which
have degree one; hence `G' - M'` is a disjoint union of cycles and
exactly two paths on the terminals. `G - M` is obtained by joining
`a'-b'` and `c'-d'` through the forced paths; the result is a single
cycle exactly when the two paths pair the terminals crosswise and no
closed component survives. The cut edges and ports lie in `G'`, so the
port data is read off from `G' - M'`. ∎

The extension diagnostic verifies both directions of the equivalence on
**all 626** perfect matchings of the three retained instances' derived
graphs, with no exception.

## Why E182 reduces to survival alone

Since `q = p triangle E(C)` is in the *complete* lost fibre, any
compatible exterior partner of `q` glues to a Hamiltonian cycle `H0`;
`M0 = G - H0` contains `A`. So an `A`-containing perfect matching with
one Hamiltonian complement **always exists** under the E182 hypotheses —
but its local restriction is the lost packing `q` itself, of type
`(01;01)`. The precise missing graph-structural condition, sharper than
I181's three-control formulation, is:

> **CPTP-survival.** In the derived graph `G' = G - V(C)` with terminal
> quadruple `(a',b',c',d')`, the nonempty population of perfect
> matchings with acyclic cross-paired two-path complement contains a
> member whose used cut labels and pairing form one of the eleven
> survivor types (equivalently, avoid `P=(01;01)` and
> `D=(0134;01,34)`). Equivalently: `G'' = G' + {a'b', c'd'}` has a
> Hamiltonian cycle through both contracted edges with surviving cut
> usage.

The pinned `cor:pfaffian-paths` forces one three-edge path, not two
disjoint contracted edges plus a port-survival condition; brace
two-extendability and edge avoidance are existence statements without
these simultaneous controls; the D168 bidirectional shortcut remains
false and unused. No local reduction preserving simplicity, planarity,
bipartition, brace connectivity and the exact five-port interface while
lifting an actual surviving cycle was found. A refutation would require
an actual written construction meeting every H180 graph/interface/brace
hypothesis in which all cross-paired complements are lost; no such
construction was obtained, and no new graph test was authorized or run.

## Finite certificate on the retained graph

The retained I177 glued graph has exactly three port-disjoint internal
two-square patches; their boundaries are the retained six-cycle moves
`C0=(14,15,16,24,23,22)`, `C1=(15,16,17,25,24,23)`,
`C2=(16,17,18,26,25,24)`. (A fourth ladder patch meets port 19; three
other quadrilateral pairs are not internal to `X`.) Each supports both
directed lost–lost instances, six in total. On each instance the
diagnostic enumerates every perfect matching of `G'` (111, 111, 102,
102, 100, 100 respectively) and finds:

- 8 matchings with Hamiltonian complement, of which exactly **5
  controlled** (survivor fibres 5, 6, 9 with multiplicities 2, 1, 2)
  and **3 lost**, all of type `P` (one being the `q`-completion);
- the remaining matchings fail topology only: 26/26/22/22/22/22 with
  parallel terminal pairing and 77/77/72/72/70/70 with closed
  components;
- conversely, the three survivor packings using the opposite half on
  each instance, completed by their compatible exterior partners, give
  exactly the 5 controlled matchings (9 equal-pairing products per
  instance are correctly two-cycle and excluded).

So on the only authenticated instance population the controlled
extension exists and coincides exactly with the helper products. This
confirms the conclusion finitely; it decides nothing universally.

The extension payload has SHA-256

```text
8f5bc21ed73f55582b1dcf7014f246c95558e7c70aad5d9fc16c67f6dc2812fa
```

and ran in 0.10486502596177161 seconds.

## One bounded next action

Decide CPTP-survival for the derived quadruple `(G'; a',b',c',d')`:
prove that the lost `(01;01)` exterior routing of the `q`-completion can
always be re-routed inside the fixed exterior `Y` to one of the eleven
surviving pairings while preserving the cross pairing of the two
terminal paths, or refute it by an actual written `X` meeting every
H180 graph/interface/brace hypothesis in which every cross-paired
acyclic two-path complement has lost port pairing. No broader census,
parameter sweep or parent verdict should be bundled with that test.

## Failure and attempt ledger

All failed attempts and empty captures are retained under the I182
experiment package: three pre-freeze read-only scoping probes (two
schema inspections, one face-adjacency enumeration; uncertified and
re-derived post-freeze), one abstract-patch debug print, and four
retained mandatory failures — the I180/I181 `image_minor`
string-versus-integer cross-check, the degree-correct-subset count
(ten, not two), the subset-versus-exact-half forcing predicate, and the
routing word ordering — with empty stdout captures and retained stderr.
`mandatory-attempt-05` and `extension-attempt-01` are the successful
payloads. `failures.md` records the exact causes. No ancestor artifact
was edited, repaired, rolled back or resealed.

## Package links

- [I182 brief](iteration182-controlled-extension-brief.md)
- [I182 experiment package](../experiments/i182_controlled_extension/)
- [I182 source receipt](../sources/i182_controlled_extension/literature.md)
- [analytic record](../experiments/i182_controlled_extension/analytic-attempt.md)
- [failure ledger](../experiments/i182_controlled_extension/failures.md)
- [frozen inputs](../experiments/i182_controlled_extension/inputs.json)
- [mandatory payload](../experiments/i182_controlled_extension/mandatory-attempt-05.json)
- [extension payload](../experiments/i182_controlled_extension/extension-attempt-01.json)
- [I181 report](i181-six-cycle-helper.md)
- [I181 parent disposition](i181-six-cycle-helper-parent-disposition.md)

Detached report, seal and verifier hashes, with final replay runtimes,
are returned outside this file so the report need not embed a
self-referential digest.
