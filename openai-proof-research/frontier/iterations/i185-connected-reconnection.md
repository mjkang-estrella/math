# I185: the ear-splice criterion is paid; forcing a joining ear is not

2026-10-11. **Original Z184 UNRESOLVED; E183 UNRESOLVED.**
Eight accepted findings remain eight, with two remaining.
All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
are stipulated true.

## Scope and result

The [full written attempt](../experiments/i185_connected_reconnection/analytic-attempt.md)
retains the exact I184 hypotheses and labels: arbitrary locally
cubic bipartite disk with the specified five-port order and colors,
the exact thirteen-vertex exterior, simple planar bipartite brace,
all eleven complete nonempty survivor fibres, complete lost $P$,
and the internal patch and prescribed $p,q$.

The target still asks for **some** completion $H_0$ of the given
$q$ and one simple alternating cycle through $e_2$ avoiding the
patch, with connected toggle. It is not strengthened to every
completion.

I184's parent-approved lemma makes the candidate set nonempty.
This round minimizes $(c(H_0,Z),|E(Z)|)$ over **all** allowed
completions and cycles, and analyzes only the proposed ear
replacement with that selected $H_0$ unchanged.

### Exact elementary deductions

1. An alternating ear has nonmatching endpoint edges, odd length
   and opposite-color endpoints. An endpoint cannot be a
   degree-two continuation terminal.
2. Exactly one arc $I$ of $Z$ can be replaced: it starts and
   ends with nonmatching edges. The retained arc $J$ starts
   and ends with matching edges. The new cycle $J\cup Q$ is
   simple and alternating, and retains cut 2 exactly when
   $e_2\in J$.
3. Put $F=H_0\triangle E(Z)$ and let $R_K,T_K$ denote the
   $H_0$ and $M_0$ edges of a path $K$. The splice removes
   $L=T_I\cup R_Q$ from $F$ and adds $N=R_I\cup T_Q$.
   If $a$ is the number of old components cut by $L$ and
   $b$ is the number obtained by pairing the retained paths
   with $N$, then

   $$
   c(H_0,J\cup Q)=c(H_0,Z)-a+b.
   $$

   Strict improvement is exactly $b<a$. The proof keeps all
   edge identities, loops and parallel edges. A common
   refinement of the two Hamiltonian path decompositions also
   keeps the singleton paths at the ear endpoints.

If each deleted edge is in a different old component, the splice
does join them into one. No existence of such an ear is proved.

## Precise remaining gap

The full hypotheses have not been shown to force an eligible
ear with $b<a$ when the global minimum has $c>1$.
Different endpoint components are insufficient **as pairing data**:
the attempt gives a six-incidence calculation with $a=b=2$ and
$|I|=|Q|=3$. Part of one component joins another while a piece
splits off, so neither component count nor the length tie-breaker
improves.

That calculation is only a formal obstruction to the suggested
inference. It is not a graph construction, an exact-hypothesis
counterexample, or a proof that this ear route must fail.

The I184 reachability shore does not follow from absence of a
component-reducing ear: ordinary directed paths may exist, and
rejecting them on retained-path pairing grounds does not produce
the matching-closed reachability sets or sole exit used in its
degree count. No forbidden shore is derived. Basic planarity,
the written forced-edge consequences of the exact exterior,
and complete-fibre comparisons do not complete that missing
argument.

## Implications and evidence

Z184 still implies E183: a connected toggle gives an
$A$-containing matching with Hamiltonian complement using cut 2,
which both lost types omit. Neither the converse nor strict
separation is proved. E183/E182/E181/H180/L179, exchange/(T)/Q164
remain open. No ninth finding or lowered contribution gate is
claimed.

All five detached I184 hashes matched **before proof work**.
The I185 brief and finalized I184 parent disposition were also
hashed. The [authentication receipt](../experiments/i185_connected_reconnection/input-authentication.json)
records the inputs and source bytes.

The parent's approximately 8.89-second, 23-stage sealed I183
replay with eight probes and source positive control is inherited,
not rerun. The twelve facial and 626 matching controls remain
finite evidence. This is an **unsealed proof record**, not a
computational package.

Only the five authorized outputs were written:

* This report.
* [Analytic attempt](../experiments/i185_connected_reconnection/analytic-attempt.md).
* [Reading and failures](../experiments/i185_connected_reconnection/reading-and-failures.md).
* [Input authentication](../experiments/i185_connected_reconnection/input-authentication.json).
* [Literature receipt](../sources/i185_connected_reconnection/literature.md).

Validation is internal written checking and file authentication,
not independent mathematical review or formal verification.
No graph computation, historical replay, research code, agents,
ancestor edits, shared-ledger edits, staging, commits or
publication occurred. Any substantial candidate still requires
independent correctness and contribution gates. Detached output
hashes are returned separately.
