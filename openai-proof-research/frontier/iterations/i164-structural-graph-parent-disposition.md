# I164 parent disposition: exact counting interfaces, unresolved linear target

Date: 2026-10-10. **Gap report retained; no substantial nomination.
Eight accepted findings remain eight.**

The parent read the complete [I164 report](i164-structural-graph-discovery.md)
and reproduced its sealed evidence. Its positive deductions remain
**author-level technical/supporting results**, not an independently
passed universal theorem. The follow-up below reviews the interfaces it uses.

## What remains unresolved

For every finite simple cubic, bipartite, planar, 3-vertex-connected graph
$G$, count Hamiltonian cycles as unoriented edge sets. The target is

$$
h(G)\ge |V(G)|/2+2.
$$

This is neither proved nor refuted by I164. Its status in the full
literature is not certified; no MathDB importance score was established.
The source's prescribed-three-edge-path/Pfaffian theorem and its published
equivalence are already available inputs, not new findings.

The report gives a complete prism count $h(C_m\square K_2)=m+2$ for even
$m\ge4$. Its examples rule out universal exponential growth, growing
multiplicity through an arbitrary prescribed three-edge path, unrestricted
remote pattern extension, and arbitrary two-edge resilience. The stronger
incompatible-pattern example with a common spanning 2-factor uses
$m\ge10$ and the specified opposite parity. These are scoped obstructions,
not counterexamples to the linear target.

The two developed approaches expose precise remaining obligations:

- The classical square expansion has the author-proved identity
  $h(G')=h(G)-N_{00}+P_{ux}+P_{vy}+D_{11}$, with all terms defined in I164.
  Source-prescribed paths make the three new families nonempty, but do not
  pay for the lost $N_{00}$ cycles. The sufficient inequality
  $P_{ux}+P_{vy}+D_{11}\ge N_{00}+2$ remains unproved.
- The signed-state/Vandermonde argument gives
  $h\ge3(c_{\min}+1)$ with explicit witness recovery. Actual even
  bipyramids have $c_{\min}=1$ and only two forest second states, so that
  fixed-root count does not grow with graph size. The alternative full
  affine-span criterion also remains unproved.

The technical reductions do not justify declaring the **entire linear
target** routine. That would require a full-scope proof which is not present.

## Parent replay and separate coverage correction

The [parent verification receipt](../experiments/i164-parent-verification.json)
records a successful isolated, bytecode-disabled replay. The parent checked
the exact inventory, payload hashes, seal and prevalidation hash **before**
executing the inspected owned scripts. The original verifier's inventory
check itself occurs after diagnostics; its order is not misrepresented.
No ancestor script was executed.

The replay reproduces 41 inventoried payload files, three source blobs,
113 labelled graph encodings, 198 expansions, seven prism orders,
1,680 directed path checks, four boundary-count identities and 465 exact
Vandermonde tests. Both historical diagnostic failures occur at their
expected assertion lines. They remain failures; the corrected third
diagnostic is a separate file.

**Coverage correction:** I164 twice describes the 198 expansions as tests
of seven selected minima. The actual `expansion_probe.py` skips orders above
20, so these expansions use **six** selected graphs, of orders
8, 12, 14, 16, 18 and 20. The seventh representative, order 24, is included
in discovery and affine-rank checks only. The number 198 and the observed
minimum gain two reproduce. This corrects a coverage description, not a
universal proof or the counting identity. All sealed original bytes,
including that wording, remain unchanged.

Report SHA-256:
`19142c6dd6ba3758006b6bd4390ce10408f3648e5f3d2ea72a07e22d01e565cd`.
Seal SHA-256:
`dbf9aff37eb3fbd30270ea3de0992a02fe185e46ed8236ac2a0c45bc4f9fe14d`.

The search record is frozen lexical evidence, not a replayed full-corpus
search or semantic novelty certificate. The source check additionally
requires the ignored complete preprint-tree cache and three original
source-cache copies. Clean-clone reconstruction and PDF re-extraction
were not tested. The [integration receipt](../experiments/i164-parent-integration.json)
records exact dependency, syntax and staging scope checks.

## Focused continuation

[I165](iteration165-square-expansion-multiplicity-factory-astra-task.json)
is a fresh Factory/Astra round. It first independently checks the original
prism, square-expansion, source-path and splice interfaces used in its
argument. It then attacks the missing inequality by a recoverable
counting map or a class-preserving counterexample, emphasizing graphs with
many lost cycles and varied construction histories. A separate global
exchange or adaptive-expansion approach is required if that route stalls.

A counterexample to the sufficient square-step inequality would defeat
that induction, **not** the linear target. Any proposed complete theorem
still needs renewed primary comparison and separate acceptance gates.
The parent read back the complete dispatch without truncation. No existing
task, I31 work, or closed oracle/BFSS contribution gate is duplicated.
