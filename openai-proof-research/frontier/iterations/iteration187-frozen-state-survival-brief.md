# I187: frozen matching survival through global paired-state cancellation

Work only in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md, `sources/upstream.json`, the relevant family-180 catalogue
entry and complete manuscript-path listing. All OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
Eight accepted, two remaining. Correctness and contribution are separate
gates; technical deductions and restatements do not increase the count.

## Focused inputs and the stopping decision

Read all five I186 outputs and the
[finalized parent disposition](i186-theta-region-balance-parent-disposition.md).
Read the [I184 exact target brief](iteration184-alternating-cycle-brief.md)
and [I183 final analytic review](../experiments/i183_cptp_finalization/analytic-review.md)
for the original problem and paid reductions. Its historical wording
"strictly stronger in scope" does not prove strict logical separation
between Z184 and E183.

The single-ear mechanism is now **PARKED**. I186 proves strict-interior
matching closure, boundary-stub color balance and exclusions for two
short retained arcs. Its length-five data pass only symbolic incidence
conditions, not graph realizability. No improving ear is forced.
Do not reopen this route as another pairing inequality, plateau rule,
theta bookkeeping task, or bounded dual-tree transfer.

## Exact original target, without the single-cycle restriction

For every finite connected simple bipartite locally cubic disk $X$,
require five distinct degree-two ports $b_0,\ldots,b_4$, boundary order
$(0,2,1,4,3)$ and colors $(1,1,1,0,1)$ in label order. All other vertices
are cubic. The cut edges $e_i$ join these ports respectively to
$(1,5,6,28,29)$ in the fixed exterior $Y$, whose vertices are
$\{1,\ldots,11,28,29\}$ and whose internal edges are exactly

```
1-7,1-28,2-3,2-8,2-29,3-4,3-9,4-5,4-10,5-11,
6-7,6-11,7-8,8-9,9-10,10-11,28-29.
```

Require the glued $G$ to be simple, planar, bipartite and a brace.
Retain all eleven complete nonempty survivor local types:

```
02;02  12;12  14;14  24;24  0123;02,13  0123;03,12
0134;03,14  0234;02,34  0234;03,24  1234;12,34  1234;14,23.
```

The complete lost types are $P=(01;01)$ and $D=(0134;01,34)$.
Packings span their side, have degree one precisely at used ports and
degree two elsewhere, and have no isolated cycles. All fibres and
compatible exterior products are complete, not representative lists.

The internal port-disjoint patch has simple boundary
$C=(x,a,b,y,d,c,x)$, chord $xy$, and
$A=\{xa,by,dc\}$, $B=\{ab,yd,cx\}$.
For every $p\in P$ using exactly $A$ on $C$, with
$q=p\triangle E(C)\in P$, E183 asks for **some perfect matching
$M\supseteq A$ whose complement is Hamiltonian and has one of the
eleven survivor local types**.

Do not prescribe cut 2, a reference completion, a single difference
cycle, or a sequence of individually Hamiltonian-preserving moves.
Any survivor type is allowed, including those omitting cut 2.
Holding the local packing fixed and changing only $Y$ cannot change
its type. The four continuations have distinct terminals outside $C$;
removing $A$ bijects prescribed matchings with matchings of $G-V(C)$.
The lost completion pays nonemptiness, not survival.

## One distinct mechanism to investigate

Use the actual paired-state construction of the pinned manuscript
*Paired states and Hamiltonian cycles in cubic bipartite planar graphs*.
Retained source:
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
SHA-256 `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.
Pinned path:
`preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex`.

Read the actual statements and proof operations used, particularly
`prop:pairs`, `lem:disk`, `prop:forest-state`, `lem:cancel`,
`lem:circulation`, `eq:group-product`, `eq:leading-coefficient`,
`lem:root-components`, `lem:P-forest` and separating-triangle assembly.
No audit of their stipulated truth. Do not substitute catalogue summaries.
Check the focused companion paths and the I164 Section 5 state-count
discussion to distinguish this prescription question from its old
$c_{\min}+1$ multiplicity bound. No recursive audit of unrelated history.

For a sphere dual $T$, the desired Hamiltonian cycle corresponds to
two induced trees, whose selected same-class edges are dual to $M$.
Use different symbols for the source's black-face set and selected-edge
forest: its letters $A$ and $P$ otherwise collide with our patch half
and lost fibre. The source's opposite-edge forest $Q_s$ is **not**
the recovered selected-edge forest.

Investigate whether the global cancellation can retain both the
prescribed dual edges $A^*$ and survivor local type:

1. Verify every source hypothesis for this exact graph/dual. If using
   "no separating triangle", prove why it follows here or explicitly
   handle assembly. Brace status must not silently replace a required
   connectivity or simplicity argument. Do not assume the two patch
   squares are faces without proof.
2. Track the source's rooted white-face-tree recovery exactly. Determine
   how $A^*$ containment and the **full lifted five-port path type**
   constrain the second state and its recovery. One root-edge
   prescription does not supply the other matching edges or survival.
   A forest-state injection into Hamiltonian cycles is not surjectivity;
   a known lost completion need not automatically have a paired-state
   preimage. Pay any such claim if used.
3. Attempt a restricted/marked version of the finite exponential sum.
   Fixed-second-state cancellation can survive a multiplier depending
   only on that state, but a restriction involving its partner may
   destroy the involution. Conversely, changing orientations within an
   undirected group changes the second state: the original product over
   independent cycle orientations and common leading phase cannot be
   assumed for a filtered population.
4. Derive the actual restricted group contribution and try to prove
   nonvanishing for the survivor prescription under the exact hypotheses.
   Explain how a surviving term gives the required actual matching and
   Hamiltonian complement. Allow a global change of the cycle rather
   than a local improving move. This is the intended new bridge.

These are obligations in one research route, not assumed lemmas.
A sum defined by "keep exactly the desired solutions" and declared
nonzero merely renames E183. If the argument stops, provide a concrete
proved restriction on the mechanism or a precise failed implication,
with its full calculation and scope. Abstract cancellation patterns do
not become exact-instance counterexamples. Do not promote a nonzero
unfiltered sum or nonempty lost population into survivor nonvanishing.
Do not replace the fixed exterior, complete fibres or arbitrary disk
by a ladder census. No automatic frozen-matching descent, P4 upgrade,
typed affine fullness, or bounded-transfer spanning claim is available.

Return PROVED, REFUTED by a fully hypothesized written counterexample,
or UNRESOLVED for original E183. State separately any implication for
Z184, exchange, (T), or Q164; none is automatic. If the route only
reformulates the target, say so and do not commission a sequel yourself.

## Five-file proof-only policy

Exclusive output paths:

- `frontier/iterations/i187-frozen-state-survival.md`
- `frontier/experiments/i187_frozen_state_survival/analytic-attempt.md`
- `frontier/experiments/i187_frozen_state_survival/reading-and-failures.md`
- `frontier/experiments/i187_frozen_state_survival/input-authentication.json`
- `frontier/sources/i187_frozen_state_survival/literature.md`

No other writes. No graph generation/construction tests, enumeration,
matching/state scans, numerical experiments, research implementation,
historical replay/control rebuild, source copies, snapshots or seal
framework. Written symbolic reasoning about arbitrary admissible graphs
is allowed. No agents, ancestor/shared-ledger edits, staging, commits or
publication. Preserve failed written routes and honest source-reading
limits. If an external theorem is needed, read its actual statement,
record its locator and check every hypothesis.

Before proof work authenticate the five I186 inputs:

| Output | SHA-256 |
| --- | --- |
| Report | `28cc7156e7a069e6e821b21d190fb4e0e188b4b6e45dd22a62fc1255f5320bc8` |
| Analytic attempt | `bc757e5332bccdebb16368890a6939fdf8e180f265ac09ca542e53520dc7cf53` |
| Reading/failures | `1f74a79202454d2cd6a2bb759d7b517bb7216fcc56af3093f297a8bfede0c2d3` |
| Authentication | `15e1c00e28da7279c4d0921a64c64af64e551dee256d1c0b44e7c8a479902cc0` |
| Literature | `6e5fbcfbb2fadb978b2165acea00bcdca36cb0449e361c1b5795538b25e1cd3a` |

Also hash this brief, the finalized I186 disposition and actual additional
inputs read. Hashing is not whole-file reading. The parent's inherited
23-stage I183 replay passed in about 8.59 seconds, with eight probes and
source positive control; twelve facial and 626 matching controls remain
finite. Do not rerun or rebuild them. Your five outputs remain unsealed.
Return detached output hashes, the original-target verdict, full proof
or precise gap, source dependencies and contribution limits.
