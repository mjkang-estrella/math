# I184 parent disposition: cycle existence proved, reconnection unpaid

2026-10-11. **The first matching-cycle obligation passes parent review.
Z184 and E183 remain UNRESOLVED. Eight accepted, two remaining.**
The elementary lemma is technical progress, not a ninth finding.

## Original proof review

The parent read all five I184 outputs in full. The proof retains the
original graph/interface/brace/complete-fibre hypotheses and existential
completion quantifier. Its local lemma actually holds for every residual
perfect matching and each matching edge, without asserting that the
residual graph is a brace or two-extendable.

The parent independently checked the key argument:

1. Delete the matching edge $uv$, with $u$ black, and orient the other
   matching edges white-to-black and nonmatching edges black-to-white.
   A simple directed path from $u$ to $v$ closes with $uv$ to a simple
   alternating cycle. The original graph's simplicity excludes a
   parallel-edge two-cycle.
2. If $v$ is unreachable, let $S,T$ be the reachable black and white
   vertices. The matching is a bijection from $T$ to $S\setminus\{u\}$,
   so $|S|-|T|=1$. The only black-to-outside edge is $uv$.
3. The residual graph has exactly two degree-deficient black terminals
   and two degree-deficient white terminals, all deficits one. If
   $r,s$ count these in $S,T$ and $h$ counts white-to-outside edges,
   degree subtraction gives $1-h=3-r+s$. Thus $r-s=2+h$.
   Bounds $r\leq2$, $s,h\geq0$ force $(r,s,h)=(2,0,0)$.
4. Restoring the patch leaves precisely the cut $\{uv,aa',cc'\}$.
   Every cut edge leaves the majority black color of this shore.
   Each perfect matching crosses it exactly once, because all minority
   white vertices must match internally.
5. The continuation edges $aa',cc'$ are disjoint by the previously
   proved terminal-distinctness lemma. Two-extendability supplies a
   perfect matching containing both, contradicting that crossing count.

No substantive repair is needed. The argument explicitly pays the
three-edge-frozen descent issue instead of assuming extendability
descends. Applying it to $e_2$ pays cycle existence for **every**
completion of $q$, but pays connectedness for none by itself.
Equivalently, no residual edge is present in every residual perfect
matching. This does not imply every residual edge is usable in a
perfect matching, nor residual two-extendability.

## Reconnection and the exact remaining gap

For a simple alternating cycle $Z$, let $R$ be the removed Hamiltonian
edges and $T_Z$ the added matching edges. The edges of $R$ form a
matching, so deleting them from $H_0$ gives disjoint non-singleton
paths. In a more general deletion, singleton paths must be retained.
Contracting the retained paths preserves components, with loops and
parallel edges counted. The resulting 2-regular multigraph is connected
exactly when the toggled complement is Hamiltonian.

Thus $R\cup T_Z$ being connected does not imply that the retained-path
pairing $S_H\cup T_Z$ is connected. The four-incidence example in I184
correctly has component counts one and two. It is only an abstract
pairing calculation, not a realizable counterexample at the exact
brace/exterior/fibre hypotheses, and does not refute shortest-cycle
selection using additional graph structure.

Z184 still asks for **some** completion and a connected toggle.
It implies E183; neither the converse nor strict separation is proved.
The new lemma alone yields a spanning 2-factor using cut 2, which may
have isolated cycles and need not define a valid survivor packing.

## Authentication and validation

The [parent validator](../experiments/i184-parent-validate.py) checks
all five detached output hashes, exact output membership, the five
pre-proof input records, seven additional source hashes and the actual
retained upstream manuscript hash. It reuses the committed I183 parent
validator for the sealed reference, not as I184 research implementation.

The [verification receipt](../experiments/i184-parent-verification.json)
passes: all 23 inherited stages replay in **8.888603 seconds**, with
empty stderr, all 562 owned and 1,153 strict bindings checked, and all
eight live probes blocked with the authentic-source positive control.
The parent also checks the unique terminal-deficit solution and the
four-label pairing component counts. These are small formal bookkeeping
checks, not graph tests or substitutes for the written proof.

The child did not run these inherited controls. I184 remains a
**proof-only, unsealed record**. No computational seal is implied by
parent verification. Integration rechecks the same reference after
ledger updates; the four current contexts must stay stable within
each replay.

The source receipt is honest about actual statement reading, absent
external novelty review and no complete upstream/GSW proof reread.
Pinned OpenAI results remain stipulated true. No literature priority or
substantial contribution is claimed for the elementary matching lemma.

## Next action

[I185](iteration185-connected-reconnection-brief.md) attempts a specific
alternating-ear improvement of a component-minimizing candidate cycle.
The new existence lemma guarantees that the candidate set is nonempty;
the unpaid point is whether a suitable ear can improve reconnection
while retaining a single alternating cycle through cut 2.

This is a proposed proof mechanism, not an assumed local-improvement
theorem or an equivalent reformulation. If it fails, record the precise
obstruction without calling Z184 or E183 false. Keep the five-file
proof-only policy and reuse the existing sealed controls.

E183/E182/E181/H180/L179, universal exchange, (T) and Q164 remain open.
