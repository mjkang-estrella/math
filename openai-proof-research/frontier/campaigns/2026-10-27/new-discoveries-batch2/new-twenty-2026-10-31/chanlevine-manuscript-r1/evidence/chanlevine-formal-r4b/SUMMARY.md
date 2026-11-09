# Round 4b partial semantic handback

MathDB 338887 remains conditional. Root decides; no acceptance or credit is requested.
All 18 modules in the bound round 3b archive remain byte-identical. No Count modules were created.

New unconditional proofs in namespace ChanLevine.Sem4:

- quota_terminal_exists: every signed starting state and finite per-vertex quota have a terminal legal execution within the quotas. Strong induction on the sum of remaining quotas gives existence without selecting an infinite trajectory or relying on recurrence.
- capped_terminal_exists and capped_terminal_empty: with cap 2, an uncapped vertex is empty at termination from a natural starting state.
- no_empty_rotor_closed_set: the cycle test excludes any nonempty chip-free set closed under the initial rotors. Starting from any vertex in such a set, absence of an empty facing pair forces its rotor direction to propagate around the entire cycle. This contradicts the corresponding Hamiltonian condition.
- execute_perm: executions of permuted words have the same endpoint, including executions whose intermediate states need not be legal.
- double_fire, execute_doubleWord and balanced_return: firing every vertex twice restores the full signed configuration. Pairing equal letters gives the cycle Laplacian; summing the paired increments cancels both neighbor terms against the two departures.

## Exact remaining obligations

The new final module is formal/SemFinal3.lean. Its theorem cycleTestBridge is CONDITIONAL on exactly ChanLevine.Sem4.CappedDeficitTrap, defined in formal/Sem4Residual.lean. Its theorem connectedFibres is CONDITIONAL on exactly the frozen ChanLevine.RecurrentNormalization. Neither requested target is unconditional. The original CycleTestWord has been reduced to CappedDeficitTrap, not proved unconditionally; cycleTestBridge_of_word preserves the original interface.

CappedDeficitTrap says: for every n >= 3, natural configuration c, and terminal legal word w with each count at most 2, if some vertex has count less than 2, there is a nonempty set S on which c has zero chips, closed under c's initial rotors. This is an ordinary Prop definition, not a postulate. Combining it with the proved rotor-set obstruction forces all counts to be 2; balanced_return then closes the legal word. No cycle-test premise is included in the trap statement.

RecurrentNormalization remains exactly the original reachability-to-canonical statement. No sink termination or sink-tree classification proof is supplied. This lane does not claim to have reduced that separate bottleneck.

## Next round

Prove the residual firing-flux identity for a capped word. If r(v)=2-count(w,v), then its endpoint chip vector equals the initial chip vector plus r minus the residual incoming chips. On S={v:r(v)>0}, terminality makes the endpoint zero. Summing on S forces the initial chips there and residual flux escaping S to vanish. Every positive r(v) includes the last rotor departure, whose direction is the initial rotor. Thus S is closed under those rotors and proves CappedDeficitTrap. The balanced-return algebra is already complete.

For normalization, formalize a separate sink-at-zero process, its decreasing potential, and the classification of sink rotor trees by weight, then use the frozen closedWordRecurrence reversal theorem. The bounded execution helpers do not prove uniqueness of recurrent components.

## Validation and limitations

The source-only zip includes all frozen and new Lean sources, scripts, and reproduction instructions. Fresh extraction is rebuilt serially with strict warnings and leanchecker on every module. Sem4Audit visits all declarations, including generated declarations, in the local SemFinal3 import closure and all their type/body dependencies using allowOpaque := true, including constructor edges. Replay independently reconstructs that closure and checks equality. LOCAL and upstream executable metadata are reported separately; only propext, Classical.choice, and Quot.sound are permitted axioms. Exact totals are in results.json.

Regression checks compare source Definition 5.2 SCCs with the cycle test for n=3..8, m=1..3, and now check the capped greedy execution for every enumerated natural configuration, including the predicted deficit trap and balanced endpoint. These computations are evidence only, not a proof of the remaining Prop. Inherited fixed kernel-decided checks are retained unchanged. Negative controls reject omitted residual premises as well as wrong-weight, empty-cycle and missing-coverage claims.

All writes are lane-local; no child agents, git, network, external messages, uploads or browser tabs were used. Full failed development logs remain. No background process is left at handback.
