# I185 parent disposition: exact splice criterion, no improving-ear theorem

2026-10-11. **Original technical claims PASS at their stated scopes.
Z184 and E183 remain UNRESOLVED. Eight accepted, two remaining.**
No substantial contribution is nominated.

## Written proof assessment

The parent read all five outputs in full and checked the original
argument without substantive repairs:

- At an ear endpoint on $Z$, its unique matching edge is already on
  $Z$. A proper alternating ear therefore starts and ends with
  nonmatching edges, has odd length, and has opposite-color endpoints.
  A degree-two continuation terminal cannot be an endpoint.
- There is exactly one replaceable arc $I$, with nonmatching endpoint
  edges. The retained arc $J$ has matching endpoint edges. Internal
  disjointness makes $J\cup Q$ simple and alternating; it contains
  $e_2$ precisely when $e_2$ is not removed with $I$.
- With $F=H_0\triangle E(Z)$, the update removes
  $L=T_I\cup R_Q$ and adds $N=R_I\cup T_Q$. The difference cycle is
  $I\cup Q$, not the new reference-difference cycle $J\cup Q$.
  The edge sets $L,N$ alternate on it and saturate its vertices.
- If $a$ old cycles meet $L$, its $k$ deleted matching edges leave
  exactly $k$ paths. Restoring $N$ creates $b$ cycles. The untouched
  $c-a$ components persist, giving exactly $c'=c-a+b$.
  Loops and parallel-edge identities remain components, not artifacts
  to discard.
- The common refinement of the two decompositions of $H_0$ correctly
  retains singleton paths at the ear endpoints. The old and new
  added-edge sets in equation (2) restore the two complements exactly.
- If every deleted edge lies in a different old component, replacing
  the retained paths by the corresponding $L$ pairs shows $b=1$.
  This is a conditional improvement statement, not ear existence.

The length counts, length-one exclusions, secondary objective and
the forced edges in the exact exterior also check out. In particular
the reference completion remains fixed during a splice; the global
minimum was originally taken over all allowed completions and cycles.
No existential completion quantifier was silently strengthened.

## Obstruction scope

For
$L=\{12,34,56\}$, $N=\{23,45,61\}$ and
$S=\{12,36,45\}$, the parent independently checks that
$L\cup N$ is connected but both $S\cup L$ and $S\cup N$ have two
components. Prospective ear endpoints 1 and 4 lie in different old
components. Opposite-color pairings and local noncrossing of $S$ hold.
Joining and fragmentation can therefore cancel in this formal data.

This does **not** give a proper embedded ear in an admissible graph.
The example supplies no retained arc $J$, simultaneous Hamiltonian
$H_0$, complete matching, patch placement, fixed exterior or brace
proof. Local noncrossing on one side of a difference boundary is weaker
than simultaneous realizability of $I,J,Q,H_0,M_0$.

The unsupported step is still existence of an eligible ear with $b<a$.
Component-conditioned reachability is not ordinary vertex reachability:
it gives no matching-closed shore or sole-exit condition to which the
I184 contradiction can automatically be applied. No plateau-escape
rule follows from the secondary length minimum.

## Validation and provenance

The [parent validator](../experiments/i185-parent-validate.py) authenticates
all five detached outputs, exact output membership, seven input records
and six additional source records. The prior I184 proof record remains
unchanged. All new proof content is Markdown; no child research
implementation or computational seal exists.

The [verification receipt](../experiments/i185-parent-verification.json)
passes. The inherited I183 sealed reference replays all 23 stages in
**8.702633 seconds**, with empty stderr, unchanged 562 owned files and
1,153 strict bindings, eight blocked live probes and the source positive
control. Small parent checks confirm the six-label counts, bipartite/
noncrossing pairing data and formal path-type arithmetic. These are not
graph generation, exact-instance tests or a universal theorem proof.
Integration repeats the reference replay after ledger updates.

The child accurately labels that replay and the twelve facial/626
matching controls as inherited finite evidence. It performed no new
graph computation. Source statements are stipulated, not truth-audited.
No external ear-theory survey, full upstream/GSW proof reread, formal
proof-assistant verification or contribution/priority clearance was
performed. Historical failures and incomplete records remain preserved.

## Next step and stopping rule

[I186](iteration186-theta-region-balance-brief.md) checks a specific
geometric constraint omitted from the abstract pairing data: matching
closure and color balance in the three regions of the full embedded
theta $I,J,Q$, working in the original cubic graph rather than silently
ignoring residual terminal deficits. It must track where $H_0$, the
patch and the retained arc $J$ actually run.

This is one final bounded examination of the local-ear mechanism.
If the region constraints give no genuine improvement or exclusion,
park that mechanism explicitly instead of commissioning another round
that merely renames $b<a$. Parking this sufficient route does not
resolve or refute Z184/E183, and the broader ten-finding program continues.

E183/E182/E181/H180/L179, universal exchange, (T) and Q164 remain open.
