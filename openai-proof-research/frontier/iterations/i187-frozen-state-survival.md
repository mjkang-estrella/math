# I187: fixed-state cancellation survives marking; survivor nonvanishing is unpaid

2026-10-11. **Original E183: UNRESOLVED.** Eight accepted, two remaining.
One proof-only attempt; no substantial finding is nominated.
All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
are stipulated true. The single-ear mechanism remains **PARKED**.

## Scope and outcome

The [full written attempt](../experiments/i187_frozen_state_survival/analytic-attempt.md)
retains the arbitrary five-port disk, exact thirteen-vertex exterior,
all eleven complete nonempty survivor fibres, lost $P,D$, and internal
patch with $A=\{xa,by,dc\}$. The target is any $A$-containing perfect
matching with a Hamiltonian complement of any survivor type.
There is no fixed completion, cut-2, single-cycle or local-move prescription.

The five I186 output hashes matched before proof work. The new brief,
finalized I186 disposition and pinned retained manuscript were hashed
at the same stage. No ancestor authentication or historical replay was
repeated.

## Technical deductions, at their stated scopes

1. **Source hypotheses are paid.** A direct cubic bipartite cut count
   and two-extendability exclude cuts of size one or two and nontrivial
   three-edge cuts. A separate argument pays 3-vertex-connectivity.
   The sphere dual is therefore a simple properly face-two-colored
   triangulation with no separating triangle. No assumption that the
   patch squares are faces is needed.
2. **The opposite-edge forest is not the matching forest.** Call the
   selected-edge forest $K_s$. The source recovery gives
   $Q_s\cap K_s=\varnothing$, by unique black-face edge ownership.
   Forcing frozen edges into $Q_s$ would impose the opposite of the
   desired matching condition.
3. **Exact recovery constraints are explicit.** Choose outer face
   $t_x$, root edge $(xa)^*$ and white-tree root $t_a$. The remaining
   frozen edges require incidence at $(by)^*,(dc)^*$ and require
   the associated white-tree edges to be the parent edges of
   $t_y,t_c$. Survival is then tested on the full lifted local
   path type, not just cut membership or four continuation endpoints.
4. **A conditional preimage criterion is proved.** An arbitrary
   Hamiltonian cycle avoiding $xa$ determines a candidate state by
   orienting its selected forest minus $(xa)^*$ toward the three
   roots. It lies in this fixed-root source image exactly when the
   opposite-edge graph of that candidate is a forest with one root
   per component. This condition is not established for the known
   lost completion. Injection is not promoted to surjectivity.
5. **Restricted group contributions are calculated.** A multiplier
   depending only on the second state retains fixed-second-state
   cancellation. In an undirected group with $c$ cycles its
   contribution is instead

   $$
   (-i)^c e^{z\sum_jm_j}
   \sum_{\varepsilon\in\{\pm1\}^c}
   g(s_\varepsilon)\Bigl(\prod_j\varepsilon_j\Bigr)
          e^{z\sum_j\varepsilon_jd_j},
   \qquad d_j>0.
   $$

   The full finite Fourier expansion is in the analytic record.
   Nonconstant restrictions can lower the order and alter the
   leading phase. Even the necessary endpoint-only mark can fix
   orientations on two cycles, replacing difference factors by
   single exponentials. Its exact formula is proved there.

These calculations are restrictions on the attempted argument, not
graph counterexamples or a proof that the global route is impossible.

## Precise gap

No theorem connects the exact exterior, complete fibres and lost patch
toggle to a nonzero restricted sum satisfying both white-tree parent
conditions and the full survivor type. Positive spoke circulation
orders the two orientation weights; it does not control the restricted
Fourier coefficients or fixed-orientation phases. A nonzero unfiltered
sum and a nonempty lost family do not pay this gap.

Marking exactly desired recovered solutions supplies a valid sufficient
formulation, but merely declaring that sum nonzero would rename the
problem within the source image. That declaration is not made.
No universal proof or fully hypothesized counterexample is supplied.
**E183 remains UNRESOLVED.** No sequel is commissioned.

Z184 remains unresolved; its known implication to E183 is unchanged.
Neither the converse nor strict separation is proved. There is no
new implication for exchange, (T), Q164 or E182/E181/H180/L179.

## Dependencies and validation limits

The actual source operations and hypotheses, rather than catalogue
summaries, are used. The retained main TeX text was read through
lines 1--838; its included figure and bibliography were not opened.
I164 Section 5 was read only for the state-count/injection boundary.
Focused catalogue and complete-path-list searches found the single
family-180 manuscript and its companion asset paths, not another
relevant theorem. No broad literature-priority survey is claimed.

The [reading/failure record](../experiments/i187_frozen_state_survival/reading-and-failures.md),
[input receipt](../experiments/i187_frozen_state_survival/input-authentication.json)
and [literature receipt](../sources/i187_frozen_state_survival/literature.md)
record the limits and dependencies. Internal written and document
checks are not independent mathematical review or formal verification.
Document integrity checks passed: valid JSON, all sixteen input
hashes unchanged (including six supplied anchors), exact five-file
membership, four valid local links, and balanced display/fence
delimiters. No mathematical computation was used for these checks.

The parent's reported 8.590879-second first replay and 8.756437-second
post-ledger preflight, all 23 stages, 562 owned/1,153 strict bindings,
eight probes and source positive control are inherited, not rerun.
Twelve facial and 626 matching controls remain finite.

Only the five permitted files are outputs. No research code,
graph/state/matching scans or tests, experiments, historical replays,
source copies, snapshots/seals, agents, ancestor/shared-ledger edits,
staging, commits or publication occurred. Detached output hashes are
returned separately. These technical deductions do not add a ninth
finding or establish new-to-literature novelty; both acceptance gates
remain unchanged.
