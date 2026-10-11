# I184: a focused alternating-cycle proof attempt

Work in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md and the pinned source contract, relevant catalogue entry
and manuscript path listing. All OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
Eight accepted, two remaining. No lowered contribution gate.

## Scope and reading

Read the full [I183 final analytic review](../experiments/i183_cptp_finalization/analytic-review.md),
[final report](i183-cptp-finalization.md),
[parent disposition](i183-finalization-parent-disposition.md), and
sections 1--6 of the [resumed analytical attempt](../experiments/i183_cptp_survival/resumed/analytic-attempt.md).
Read actual source statements before applying them, not just summaries.
Consult earlier mathematical definitions only as needed; do not turn this
round into another recursive history audit.

This is one **proof-only** research task, not a verification-framework
implementation. No new graphs, attachment changes, numerical tests,
parameter sweeps or matching-population scans. No agents, shared-ledger
edits, staging, commits or publication.

Exclusive output paths:

- `frontier/iterations/i184-alternating-cycle.md`
- `frontier/experiments/i184_alternating_cycle/analytic-attempt.md`
- `frontier/experiments/i184_alternating_cycle/reading-and-failures.md`
- `frontier/experiments/i184_alternating_cycle/input-authentication.json`
- `frontier/sources/i184_alternating_cycle/literature.md`

No other writes. Preserve all ancestor and sealed bytes. Failed written
routes belong in the reading/failure record rather than being erased.

## Exact original setting

For every finite connected simple bipartite locally cubic disk $X$,
require five distinct degree-two ports $b_0,\ldots,b_4$, boundary order
$(0,2,1,4,3)$ and colors $(1,1,1,0,1)$ in label order, with all other
vertices cubic. Glue the five cut edges to the fixed thirteen-vertex
exterior $Y$ at vertices $(1,5,6,28,29)$, whose vertices are
$\{1,\ldots,11,28,29\}$ and internal edges are

```
1-7,1-28,2-3,2-8,2-29,3-4,3-9,4-5,4-10,5-11,
6-7,6-11,7-8,8-9,9-10,10-11,28-29.
```

The glued graph $G$ must be simple, planar, bipartite and a brace.
The eleven complete nonempty survivor local types are

```
02;02  12;12  14;14  24;24  0123;02,13  0123;03,12
0134;03,14  0234;02,34  0234;03,24  1234;12,34  1234;14,23.
```

The lost types are $P=(01;01)$ and $D=(0134;01,34)$.
Packings span their side, have degree one precisely at the used ports
and no isolated cycles. Fibres and compatible exterior products are
complete, not representative lists.

The internal two-square patch has simple port-disjoint boundary
$C=(x,a,b,y,d,c,x)$, shared chord $xy$, and halves
$A=\{xa,by,dc\}$, $B=\{ab,yd,cx\}$. For every $p$ in complete $P$
using exactly $A$ on $C$, require $q=p\triangle E(C)$ also in complete
$P$. E183 asks whether some $A$-containing perfect matching has a
Hamiltonian complement of survivor local type.

## Single target Z184

Let $G'=G-V(C)$ and let $e_2$ be the cut edge with label 2. For every
admissible $(X,p,q,C)$ above, does there exist **some** Hamiltonian
completion $H_0$ of $q$ and a simple $M_0$-alternating cycle
$Z\subseteq G'$, where $M_0=E(G)\setminus E(H_0)$, such that
$e_2\in E(Z)$ and $H_0\triangle E(Z)$ is connected?

The quantifier is some completion, not every completion. All such
$H_0$ omit $e_2$, so $e_2\in M_0$. Alternation preserves the perfect
matching; avoidance of $V(C)$ preserves $A$. Connectedness then gives
a Hamiltonian complement using cut 2, hence a survivor. This is a
sufficient prescription for E183. Equivalence or strict separation
has not been proved.

Try to prove Z184 by actual structure, or give an actual fully
hypothesized counterexample by a written construction. If neither is
possible, report UNRESOLVED and isolate one precise failing implication,
not a renamed version of Z184.

Separate two genuinely different obligations:

1. An $M_0$-alternating cycle through $e_2$ contained in $G'$. Brace
   extendability in $G$ alone does not automatically give this after
   freezing the three matching edges $A$.
2. A choice whose toggle leaves one complement component. An alternating
   cycle can preserve all degrees but split a Hamiltonian complement.
   Use the explicit segment-reconnection multigraph if helpful,
   retaining singleton segments, loops and parallel edges.

Changing local edges away from the forced patch is allowed and necessary;
holding the local packing fixed and rerouting only $Y$ cannot change
local type. Do not make that failed inference again. A survivor outside
the single-cycle or cut-2 prescription would prove E183 but need not
prove Z184. Failure of Z184 would not by itself refute E183.

## Prior results and boundaries

I183 finalization is complete: parent replay passes all 23 stages,
562 owned files, 1,153 strict bindings, eight live probes and source
positive control. Independent parent code rebuilds all twelve facial
controls and all 626 matching cases. The retained graph has three
patches, six instances and five controlled matchings per instance;
these are finite evidence, not a universal proof.

Continuations leave $V(C)$ and have distinct terminals by the cut/brace
arguments in the analytic review. Deleting $A$ bijects the relevant
matchings with matchings of $G'$. Complement Hamiltonicity is exactly
the cross-paired, cycle-free incidence condition. A completion of $q$
pays topological nonemptiness but remains lost. The auxiliary graph
with two distinguished contracted edges is not automatically simple
or a brace. P4 prescribes one three-edge path; two-extendability
prescribes two matching edges. Neither can be silently upgraded to
the combined matching, connectivity and survival prescription.

All earlier failures stay binding: D168/M168 transfer/fullness shortcuts,
deleted-coordinate shortcuts, failed containments, isolated toggles.
E183/E182/E181/H180/L179, exchange/(T)/Q164 remain open.

## Lightweight evidence policy, overriding inherited control workloads

Do NOT implement or rerun the 23 historical controls, recreate their
snapshots, build a new seal framework, or import historical Python as
research implementation. This brief replaces those previous-round
workload requirements for I184 only. The parent retains the sealed
reference and will replay it during integration.

Before proof work, hash and record these three input anchors, together
with this brief and the new parent disposition:

- final report: `be011c8f9ae99899ad6c2ae4fa2cd4c1b882e6750e07b4c7ad4dc859527abd35`;
- final seal: `b3450f344ef4e173cd5bae916f5ead7bf066675698033080b6386b73d8f057f8`;
- final verifier: `9f0781077de3699a891a5e1bc843d7bfa14cf51071919509d6e50352405d883d`.

Record exact source dependencies and honest reading limits. If a new
lemma needs an external theorem, read its actual statement and check
every hypothesis. Do not audit stipulated upstream truth. No global
novelty claim without a separate contribution review.

Deliver a concise verdict on Z184 and its implications for E183, a full
written argument or precise gap, a reading/failure record and source
receipt. Return detached hashes of your five allowed output files.
This proof-only record is not a sealed computational package, and must
not be called one. A substantial candidate requires subsequent
independent correctness and contribution gates.
