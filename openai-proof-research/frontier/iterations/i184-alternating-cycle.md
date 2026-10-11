# I184: alternating-cycle existence paid, connectedness unresolved

2026-10-11. **Z184 UNRESOLVED; E183 UNRESOLVED.**
Eight accepted findings remain eight; two remain.
Pinned OpenAI results are stipulated true.

## Result

At every exact hypothesis in the
[brief](iteration184-alternating-cycle-brief.md), including the fixed
13-vertex exterior, all eleven complete nonempty survivor fibres,
complete lost $P$, brace condition and prescribed $p,q,C$, the
[written argument](../experiments/i184_alternating_cycle/analytic-attempt.md)
proves the **first** obligation:

> For every perfect matching $M'$ of $G'=G-V(C)$ and every $e\in M'$,
> a simple $M'$-alternating cycle through $e$ exists entirely in $G'$.

In particular this holds for $e_2$ and **every** Hamiltonian completion
$H_0$ of the given $q$. It does not assert connectedness after toggling
for any completion. Z184 still asks for **some** completion and some
cycle satisfying both requirements.

The proof does not assume that brace extendability descends after
freezing $A$. Failure of an alternating path forces a shore with one
more black than white vertex and exactly the cut
$\{e,aa',cc'\}$. Every perfect matching crosses it once, whereas
two-extendability extends the disjoint edges $aa',cc'$ together.
That contradiction proves cycle existence. Distinct continuation
terminals are justified by the prior seven-vertex-shore argument.

## Precise gap

Let $R$ be the deleted edges of $H_0$, $T_Z$ the added matching edges,
and $S_H$ the endpoint pairing of retained Hamiltonian path segments.
A simple alternating cycle certifies that $R\cup T_Z$ is connected.
The toggled complement is connected exactly when
$S_H\cup T_Z$ is connected, with singleton paths and all edge
identities retained.

**Replacing $R$ by $S_H$ in that connectedness conclusion is the
failed implication.** A four-incidence calculation in the attempt
shows why alternation or shortest-cycle length alone does not
justify it. That calculation is not a fully hypothesized graph
counterexample. No argument selects a connected reconnection using
the remaining exact hypotheses or the freedom to choose a completion.

## Exact implications

* **Z184 implies E183:** the toggle preserves a perfect matching
  containing $A$; connected complement makes it Hamiltonian; use of
  cut 2 excludes both lost types $P,D$, giving a survivor.
* The proved cycle-existence lemma alone gives only a spanning
  2-factor using cut 2, not a Hamiltonian complement.
* No converse or strict separation is proved. Failure of Z184 would
  not alone refute E183; several toggles or other survivor types
  could still suffice.
* E183/E182/E181/H180/L179, exchange/(T)/Q164 remain unresolved.
  D168/M168 shortcuts, failed containments and isolated-toggle
  failures remain binding.

## Evidence, limits and files

All three supplied detached I183 report/seal/verifier hashes matched
before proof work; the brief and finalized parent disposition were
also hashed and recorded. The parent's 23-stage completion,
562 owned files, 1,153 strict bindings, eight blocked probes,
authentic-source positive control and roughly 8.76-second replay
are inherited, not rerun. Its twelve facial controls and 626 retained
matching cases remain finite evidence, not a universal theorem.
The original provider failure and incomplete unsealed checkpoint
remain historical.

Only these five assigned files were written:

1. This report.
2. [Analytic attempt and proof](../experiments/i184_alternating_cycle/analytic-attempt.md).
3. [Reading and unsuccessful routes](../experiments/i184_alternating_cycle/reading-and-failures.md).
4. [Pre-proof input hashes](../experiments/i184_alternating_cycle/input-authentication.json).
5. [Source dependencies and reading limits](../sources/i184_alternating_cycle/literature.md).

No graphs, attachment changes, numerical tests, sweeps, matching scans,
historical control implementation/replay, Python imports, agents,
ancestor edits, shared-ledger edits, staging, commits or publication.
The argument was checked internally, not independently reviewed or
formally verified. Actual pinned theorem statements were read; no
full upstream proof reread or external novelty review was performed.

This is **not a sealed computational package**. The elementary
matching-cycle lemma does not lower the contribution gate and is
not nominated as a ninth finding. Any substantial candidate requires
later independent correctness and contribution gates. Detached
hashes of these five outputs are returned separately.
