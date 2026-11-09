# Round 2b semantic handback — partial, not acceptance

MathDB 338887 remains conditional. No credit or self-acceptance is requested; root decides.

The seven frozen round-1 modules are copied byte-identically from the bound archive. No Count modules were created.

Completed unconditionally in new Sem modules:

- `canonicalTest : CanonicalTest`: the explicit representative meets every facing pair and both Hamiltonian tests, and its modular weight is exactly i. The weight proof counts the interval of left rotors, including i = 0 and wraparound.
- `LegalWord`, a labelled finite legal execution, its conversion to/from Reach, and `recurrent_closed_word`, derived directly from the literal signed Definition 5.2.
- Nonnegativity preservation through legal executions, and nonnegativity at the endpoint of any word that fires the vertex.
- A finite trace construction and a periodic diverse infinite walk from a nonempty closed legal word covering all vertices. Membership in the literal component and the arbitrary-time diversity quantifier are proved.

Conditional targets in SemFinal.lean:

- `cycleTestBridge` depends on exactly `ClosedWordRecurrence`, `CycleTestWord`, and `ClosedWordCycleTest`.
- `connectedFibres` depends on exactly `RecurrentNormalization`.
- `ambientBridge` depends on exactly `ClosedCoverage`.

These five obligations are ordinary Lean Prop definitions, not asserted facts. None is discharged by finite tests. Normalization is still the substantive uniqueness bottleneck; the decomposition does not solve it. The three count/arithmetic obligations remain outside this lane.

Next round:

1. Prove `ClosedCoverage` by counting firings in a closed word: rotor restoration forces even counts; conservation and two-neighbour emission propagate positivity of counts around C_n. This immediately closes AmbientBridge using the compiled periodic construction.
2. Formalize cycle-specific word commutation and removal to prove `ClosedWordRecurrence`.
3. Use the bounded two-firings-per-vertex greedy execution to prove `CycleTestWord` and its empty-cycle obstruction converse `ClosedWordCycleTest`. No invocation of general Theorem 7.4 is needed.
4. Prove sink stabilization at vertex 0, classify sink rotor trees by weight, and use reversibility of recurrent trajectories to prove `RecurrentNormalization`.

Validation results and any audit limitations are recorded in results.json. Development failures are retained in logs. Kernel-decided fixed n = 3 through 8 canonical checks and a three-vertex period convention check accompany the reviewer's independent 18 definition-level SCC comparisons. They are regression checks, not a general semantic proof.

Audit interpretation: all local declarations and their full type/body dependency closure are inspected. Upstream extern implementations of kernel-defined arithmetic/container primitives and three Lean.Name implemented_by entries are recorded, not claimed absent. This packet does not certify the complete imported tactic/compiler environment as executable-safe. The proof terms are kernel checked; no unsafe or partial dependencies were found in the audited closure.

Audit development correction: the first two extraction runs used ConstantInfo.value? without allowOpaque, which omitted theorem bodies. Their closure totals are superseded. The final verified extraction explicitly uses allowOpaque := true and independently checks the resulting dependency graph. Earlier logs are retained as failed audit development evidence, despite their compilation checks passing.
