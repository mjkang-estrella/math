# Proof construction

The inherited definitions, PG5 geometry, percolation dynamics, finite CNF generator and normalization bridge are unchanged. Only named input proofs and named mask-RUP consequences are extended. This lane performs implementation work and makes no new source-fidelity or novelty clearance claim.

Each numeric input clause is independently matched against the hash-pinned normalized DIMACS file. Its literal-list proof follows from the inherited gate or normalization lemmas. A kernel-checked reflexivity equality identifies its encoded mask; input_sound transports the proved literal semantics through encode_cnf. No input entailment is assumed.

For each addition the data preparer computes masks and successive propagation choices. MaskChainBuild assembles ordinary proof expressions. A reflexivity proof requires kernel reduction of the actual MaskRUP.check. The builder supplies each hint with the actual earlier named clause theorem, using cons_hints and nil_hints to assemble membership hypotheses. MaskRUP.check_sound gives the new named entailment. The builder is included in the local declaration metadata audit.

Deleting clauses is unnecessary: retaining previously proved consequences is sound. No SAT solver or Python result is a proof oracle. Every delivered module is strictly compiled and separately checked by leanchecker with an explicit module argument.

Conditional on exactly RemainingSuffixUnsatR8: no valuation satisfies normalizedCNF5 together with the final proved clause, mask (5754986057962046098875290843988827640455757824, 2787593149816327892691964784081045188247552). The actual unreplayed suffix is zero-based additions [106061,129671), 23610 additions.

The endpoint uses the unchanged normalized_unsat_implies_noMinimal5 and not_conjecture20_normalized bridges. Only the three allowed foundational axioms occur.
