# I185: an alternating-ear attempt at connected reconnection

Work in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md, source contract and the relevant family-180 catalogue/
manuscript entries. All OpenAI results at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.
Eight accepted, two remaining. No lowered contribution gate.

## Focused reading and exact retained target

Read the full [I184 brief](iteration184-alternating-cycle-brief.md),
[I184 report](i184-alternating-cycle.md),
[analytic attempt](../experiments/i184_alternating_cycle/analytic-attempt.md),
[reading/failures](../experiments/i184_alternating_cycle/reading-and-failures.md),
[source receipt](../sources/i184_alternating_cycle/literature.md), and
[parent disposition](i184-alternating-cycle-parent-disposition.md).
Read actual external theorem statements before using them. Do not
perform a recursive audit of unrelated history.

All exact universal hypotheses and labels in I184 remain unchanged:
the locally cubic bipartite disk $X$, five ports with fixed order/colors,
the exact thirteen-vertex exterior $Y$, the simple planar bipartite
brace $G$, all eleven complete nonempty survivor fibres and the
complete lost fibre $P$, and the internal two-square patch
$C=(x,a,b,y,d,c,x)$ with $A=\{xa,by,dc\}$ and $B=\{ab,yd,cx\}$.
For each $p\in P$ using exactly $A$, require
$q=p\triangle E(C)\in P$.

The target remains Z184: for every such instance, find **some**
Hamiltonian completion $H_0$ of $q$ and a simple
$M_0$-alternating cycle $Z\subseteq G'=G-V(C)$ through cut edge
$e_2$, where $M_0=E(G)\setminus E(H_0)$, such that
$H_0\triangle E(Z)$ is connected. Do not silently require every
completion. Z184 implies E183, but neither converse nor strict
separation is proved.

## Paid progress, objections and parent response

I184's original matching-cycle lemma passes parent review without
substantive repair: for **every** perfect matching $M'$ of $G'$
and every $e\in M'$, a simple $M'$-alternating cycle through $e$
exists in $G'$. Failure of reachability gives
$|S|-|T|=1$ and $r-s=2+h$, forcing $(r,s,h)=(2,0,0)$.
The resulting three-edge shore has a one-crossing matching condition
contradicting two-extendability on the disjoint continuations
$aa',cc'$. This does not prove $G'$ two-extendable or that all
nonmatching edges are usable.

For any candidate $Z$, write
$R=E(Z)\cap E(H_0)$ and $T_Z=E(Z)\cap M_0$. Let $S_H$ pair the
endpoint incidences of the retained paths of $H_0-R$. Then
$R\cup T_Z$ is connected because $Z$ is one cycle, but the toggled
complement is connected exactly when $S_H\cup T_Z$ is connected.
Keep all edge identities, loops and parallel edges. Simple-cycle
$R$ is a matching; generalized deletions must also keep singleton
paths.

The four-label counterpattern is only an incidence calculation, not
an admissible graph refuting Z184. No minimal-component improvement
rule was proved. Further toggles may change the reference packing or
make the net difference multiple cycles. A survivor complement need
not contain $A$, and extracting only its difference component through
$e_2$ need not preserve Hamiltonicity. Fixed-local exterior rerouting
still cannot change local type.

## One concrete proof mechanism to attempt

The set of pairs $(H_0,Z)$ in the exact target, without the final
connectedness condition, is finite and nonempty by the paid lemma.
Choose a pair minimizing the number

$$
c(H_0,Z)=\#\operatorname{comp}(H_0\triangle E(Z)),
$$

and then minimizing $|E(Z)|$ among those pairs. This minimization is
over **all** allowed completions as well as their cycles.

If $c>1$, try to construct an $M_0$-alternating ear $Q$ in $G'$:
a path with two distinct endpoints on $Z$, all internal vertices
outside $Z$. Replace an appropriate arc of $Z$ by $Q$ to obtain a
single simple $M_0$-alternating cycle $\widehat Z$ still containing
$e_2$, and prove

$$
c(H_0,\widehat Z)<c(H_0,Z).
$$

This would contradict the minimum and finish Z184. It is a proposed
sufficient mechanism, **not an available theorem**. Determine the
actual endpoint edge types and parity needed for such an ear splice;
do not assume any alternating ear is eligible. Prove the change in
component count through the retained-path pairing, not merely degrees
or connectedness of the new alternating cycle.

The main unpaid step is to use the exact brace/embedding/fibre/exterior
structure to force an eligible *joining* ear, or derive a forbidden
matching shore when no such ear exists. The I184 reachability proof
does not already do this: its degree count has no Hamiltonian endpoint
order. Do not assert that all pairs of complement components have an
ear, or that a nonempty supply of alternating cycles is enough.

Use this mechanism as the focus of the round. If the required ear is
not forced, isolate precisely the structural obstruction or failed
implication. A formal transition pattern alone is not a fully
hypothesized counterexample. Failure of this stronger local mechanism
does not refute Z184 or E183. A genuine proof or actual counterexample
must check every original hypothesis.

## Proof-only scope and evidence policy

No graph generation, graph tests, numerical experiments, attachment
changes, parameter sweeps or matching-population scans. No agents,
shared-ledger edits, staging, commits or publication. Do not rebuild
or rerun historical controls, duplicate their snapshots, implement
research code, or build a seal framework. The parent retains the
complete sealed reference and replays it during integration.

Exclusive output files:

- `frontier/iterations/i185-connected-reconnection.md`
- `frontier/experiments/i185_connected_reconnection/analytic-attempt.md`
- `frontier/experiments/i185_connected_reconnection/reading-and-failures.md`
- `frontier/experiments/i185_connected_reconnection/input-authentication.json`
- `frontier/sources/i185_connected_reconnection/literature.md`

No other writes or ancestor edits. Preserve failed written routes in
the failure record. Hash the five I184 inputs against these detached
anchors before proof work:

| I184 output | SHA-256 |
| --- | --- |
| Report | `4d2ad390caaf9d40ccdc3a78caf15a12eddeb043f44952b6eaf712f5794066ca` |
| Analytic attempt | `7db93dbcbe08ef158dae0502fdf4261539e03d967a9bdb4fc4a03c950be7fd52` |
| Reading/failures | `47cae7389ff0e083df4128bd978847551a731c4b26ebd4077af099e28e6d453f` |
| Input authentication | `d6718b21ad9e24f86e3de2120578b044cf5e0cc8aa1660e8f05e5488077cbe3c` |
| Literature receipt | `c4978526287a4d869e4bf8ab1fd375290315d39786e2b35690f83504bd5c3fe6` |

Also record this brief and the finalized I184 parent disposition.
The parent's latest inherited I183 replay passed all 23 stages in
about 8.89 seconds; twelve facial controls and 626 matching cases
remain finite, not universal evidence.

Deliver the exact Z184/E183 verdict, the complete ear argument or
precise unpaid implication, reading limits, source dependencies and
retained failures. Return detached hashes of your five outputs.
This is an unsealed proof record, not a computational package.
Any substantial candidate still needs separate independent correctness
and contribution review; technical partials do not increase the count.
