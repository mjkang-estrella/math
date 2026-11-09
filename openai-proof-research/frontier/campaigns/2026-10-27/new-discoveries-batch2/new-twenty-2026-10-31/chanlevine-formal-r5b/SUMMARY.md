# Round 5b semantics handback — pending root review

All four requested round 5b semantic targets are proved unconditionally, with no remaining semantic Props:

- ChanLevine.Sem5.recurrentNormalization : ChanLevine.RecurrentNormalization.
- ChanLevine.Sem5.cappedDeficitTrap : ChanLevine.Sem4.CappedDeficitTrap.
- ChanLevine.Sem5.cycleTestBridge : ChanLevine.CycleTestBridge.
- ChanLevine.Sem5.connectedFibres : ChanLevine.ConnectedFibres.

The final bridge module is formal/SemFinal4.lean. This does not close the independent counting obligations or assert the full MathDB endpoint. Root alone decides acceptance; no credit or acceptance is requested here.

## Normalization, the priority

Sem5Sink proves termination of sink-at-zero legal dynamics by finite acyclicity. The finite fixed-chip-level state space is inherited from Cardinality. A positive sink execution cannot return to its initial state, because the frozen closedCoverage theorem forces every nonempty closed legal word to fire vertex zero. Transitivity and irreflexivity therefore give a well-founded finite relation. Induction on this relation constructs a terminal sink state. This supplies a decreasing well-founded rank without introducing an infinite scheduler or a separately chosen numerical potential.

Recurrence propagates along forward reachability using the frozen closed_reach and closedWordRecurrence reversal results. If rotor zero points left after stabilization, fire zero once (it holds all the positive-level chips) and stabilize again. Rotor zero now points right.

Sem5Classify proves a Boolean path without a right-left transition is a left prefix. The frozen necessary cycle test forbids every such transition away from zero in a recurrent sink state. Its nonzero rotors therefore have the canonical left-prefix/right-suffix pattern. The prefix length is strictly less than n; frozen canonical_weight identifies it uniquely with the configuration weight. Chip-level and weight invariance finish recurrentNormalization. No CappedDeficitTrap or cycle-test sufficiency is used in normalization.

The reviewer-based finite check covers n = 3 through 8, m = 1 through 3: every cycle-test state reaches exactly the canonical state after this procedure. The separate inherited SCC regression checks the cycle-test predicate against source Definition 5.2 on the same 18 parameter cases. These finite checks are diagnostics, not general proofs. The initial diagnostic accidentally sent the extra zero firing left; the convention was corrected to advance-then-move right before any formalization depended on it.

## Capped deficit trap

Sem5Flux defines each vertex's missing departures: at count zero, one departure to each neighbor; at count one, the last departure along the initial rotor; at count two, none. Induction on the actual legal word proves the exact integer identity

  d.x k = c.x k + (2 - count(w,k)) - sum_v residual(c,count(w,v),v,k).

The residual rows are nonnegative and have total 2 - count(w,v). Sem5Trap proves a finite cut-conservation lemma. On the deficit set S, terminality gives d.x = 0; all residual sources outside S vanish. Summing forces both the initial chip mass on S and all residual flux exiting S to be zero. Each deficit row has a positive entry along the initial rotor, so S is closed under it. This proves the exact frozen CappedDeficitTrap, independently of CycleTest, and the frozen assembly then proves cycleTestBridge.

## Validation

All 24 frozen modules are byte-identical to the bound round 4b archive. Six new modules are added; no Count modules were created. The source-only archive extracts safely into a fresh directory. The replay script serially runs Lean 4.34.1 with -j1 -M3500 -DwarningAsError=true and leanchecker on all 30 modules, then the declaration audit, negative controls, SCC checks and normalization checks. Exact validation results and hashes are in results.json and fresh-extraction/logs/replay-result.json.

Sem5Audit starts from every declaration (including generated declarations) in the local SemFinal4 import closure, then visits type, opaque-body (allowOpaque := true) and constructor dependencies. Replay independently verifies closure equality. LOCAL executable flags are separated from upstream metadata. The only permitted axioms are propext, Classical.choice and Quot.sound.

All writes are lane-local. No child agents, git, network, external messages, uploads or browser tabs were used. Development logs are retained. No background work is left at handback.
