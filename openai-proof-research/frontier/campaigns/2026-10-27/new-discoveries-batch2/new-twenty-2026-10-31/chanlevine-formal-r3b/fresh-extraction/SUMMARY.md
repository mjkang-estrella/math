# Round 3b semantic handback — partial, root decision required

MathDB 338887 is still conditional. No credit or acceptance is requested.
All 13 bound round-2b modules are frozen byte-identically. No Count modules were created.

New unconditional proofs:

- `ChanLevine.Sem3.closedCoverage : ClosedCoverage`.
- `ChanLevine.Sem3.closedWordRecurrence : ClosedWordRecurrence`.
- `ChanLevine.Sem3.closedWordCycleTest : ClosedWordCycleTest`.
- `ChanLevine.Sem3.ambientBridge : AmbientBridge`, also exported as `ambientBridge_unconditional`.
- `ChanLevine.Sem3.recurrent_cycleTest`: the forward half of CycleTestBridge.

The final assembly is `formal/SemFinal2.lean`. Its `cycleTestBridge` has exactly one remaining premise, `CycleTestWord`. Its `connectedFibres` has exactly one remaining premise, `RecurrentNormalization`. The inherited canonicalTest is unconditional. Namespace `ChanLevine.Sem3` avoids redefining frozen theorem names.

## Proofs

Coverage uses the integer potential `2 * x(v+1) + (if q(v) then 0 else 1)`. Along a word that never fires v+1, this potential increases by at least the number of firings of v. A closed word therefore cannot fire v without firing v+1. Iterating successors from any letter of the nonempty word reaches every vertex of ZMod n. This avoids a separate parity/count-conservation development while retaining literal signed dynamics.

Removal proves that distinct firings commute, and firing a different letter cannot invalidate an available letter. Induction removes the first occurrence of a from a legal word and obtains a legal word from `fire c a` to the original endpoint. Applying this to a closed covering word returns any one-step successor to c. Appending the removed letter supplies a nonempty closed word at that successor. Induction on Reach returns every descendant to c, which proves literal Definition 5.2 recurrence for every common-descendant-related configuration.

Obstruction works backwards. If a nonnegative legal step ends with an empty facing pair, neither endpoint of the pair fired: its restored rotor would otherwise have delivered a chip to its empty partner. The previous state has the same empty facing pair. Induction shows a returning word cannot fire a vertex of such a pair, contradicting coverage. A nonempty legal word also supplies a positive initial chip, giving both Hamiltonian conditions. No general Theorem 7.4 is invoked.

## Exact remaining Props and next round

Both residuals are ordinary Prop definitions already frozen in `formal/SemFinal.lean`:

```lean
def CycleTestWord : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ c : Config n,
    CycleTest c → ∃ w, w ≠ [] ∧ LegalWord c.lift w c.lift

def RecurrentNormalization : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ c : Config n, NatRecurrent c →
    Reach c.lift (canonical (chipLevel c) (chipWeight c)).lift
```

Next prove the bounded execution construction: extend legal words while each vertex fires at most twice; prove a maximal such word fires every vertex twice using the cycle test, then prove its endpoint equals the start. The missing argument is completion under the firing caps, not finite existence of a maximal word. The first-occurrence removal and commutation lemmas are now available.

Normalization remains a substantive, separate bottleneck. Introduce a sink at 0, prove termination of sink stabilization, classify sink rotor trees (rotors away from 0 have one transition from left to right), and connect equal-weight recurrent states to the same explicit representative. No sink stabilization or rotor-tree classification proof is supplied here. The Laplacian/torsion route is also not formalized.

## Validation

The source archive is replayed from a fresh empty lane-local directory with strict Lean compilation and leanchecker on all 18 modules. Full local-declaration dependency audit uses `allowOpaque := true`, including generated declarations and constructor dependencies, and independently recomputes closure equality. Upstream extern and implemented_by entries are disclosed separately; local declarations must have none. Only propext, Classical.choice and Quot.sound are allowed. Final numerical totals and log paths are recorded in results.json. All development logs, including failed attempts, remain in logs/.

The inherited kernel-decided fixed checks for n = 3 through 8 and independent reviewer SCC comparisons are regression evidence only. They do not discharge either residual. No source, shared ledger, git state, network service or external application was changed outside this lane.
