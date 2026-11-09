# Round 7 proof construction

The new packet restarts from normalized certificate addition zero. It retains the round 6 geometric and normalization modules byte-identically. Older list-replay modules are preserved separately in inherited.zip; they are not dependencies of this new endpoint. This is an implementation experiment, not an acceptance claim.

Each input literal list is independently matched to the hash-pinned normalized DIMACS bytes. Its generator entailment proof is assembled from the inherited proved gate/normalization lemmas. No generator proof is assumed. `mask_input` constructs a reflexivity proof of the exact literal-list mask encoding equality and applies `input_sound`. `input_sound` uses the proved literal/mask semantic equivalence. Thus its emitted theorem is a closed normalized-generator consequence.

For each certificate addition, the data preparer computes the mask and the successive unit-propagation choices. `mask_chain` emits an ordinary Eq.refl proof of `check clause hints = true`. The kernel must reduce the actual check to accept that proof. It constructs the membership-based hypothesis function by repeated applications of `cons_hints`, ending with `nil_hints`. Each head proof applies a particular earlier `clause<ID>` theorem to the current valuation and normalized-generator premise. Finally it applies `MaskRUP.check_sound` and abstracts over those two arguments. No hint assumptions survive.

The expression builder uses metaprogramming to assemble ordinary proof expressions. It is itself imported and included in the metadata audit. Neither compiler evaluation nor data preparation is used as a proof oracle. Every emitted declaration is checked by Lean.addDecl and separately by leanchecker.

The partial endpoint assumes `MaskChain.RemainingSuffixUnsatR7`, whose exact definition is printed in EndpointR7.lean. This says that no structured valuation satisfies both the normalized generator and the final proved frontier clause. The proved named entailment supplies that clause, contradicting the assumption. The unchanged normalization bridge then gives `¬ Conjecture20`. This does not prove normalized unsatisfiability or NoMinimalTwoRound5 unconditionally. The remaining certificate additions are explicitly unclaimed.

Fresh replay counts and timings, the actual frontier and any resource failures are reported in SUMMARY.md and results.json. Source presence alone never establishes completed replay.
