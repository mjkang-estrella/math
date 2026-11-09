# Statement correspondence, round 2

The primary-source correspondence from round 1 is unchanged: arXiv:1608.00531v1, Conjecture 20, lines 674–675 in that packet's cached source, asserts existence of an inclusion-minimal time-2 percolating set for every finite projective plane of order q and every 4 ≤ r ≤ q. The allowed instance is PG(2,5), r=5. The source and bibliography were read from the prior packet and review; this implementation made no network requests. Final journal retention remains outside this offline lane's verified claims.

The entire Definitions.lean is byte-identical to round 1, including Plane, Subset, Full, countOn, step, rounds, Percolates, Minimal, TimeIs, time and Conjecture20. Plane5.lean, Structure.lean and Endpoint.lean also compare byte-identically, as recorded in provenance/unchanged-definitions.txt. The original positive controls and their deletion certificates are re-exported unchanged. No replacement finite-time definition is substituted into Conjecture20 or Minimal.

closure_stable is a theorem about the original unbounded synchronous dynamics. minimal_deletion_separator uses the original inclusion minimality against every proper subset. It supplies the canonical 31-round B_v needed by the CNF for PG5. It does not assume that deletion failure can be detected in two rounds.

finite5_iff_target states equivalence between an explicitly finite Boolean system and the original ∃ a, Minimal PG5 5 a ∧ TimeIs PG5 5 a 2. The forward implication reconstructs full inclusion minimality via closed separators; the reverse constructs the separators by the closure theorem.

inputCNF5 is a new Lean-side unnormalized incidence-based clause generator. The typed SatVar has 1,085 Boolean variables. witness_satisfies_inputCNF5 establishes the direction necessary for refutation: every literal hypothetical witness supplies an assignment satisfying every generated clause. It imposes no fixed triple, hidden general-position premise, cardinal-minimum surrogate or coordinatizability premise on the general conjecture. Only PG5 is the coordinate plane counterinstance.

The final new endpoint is conditional:

```lean
Percolation.not_conjecture20_generated
  (h : Percolation.GeneratedCNFUnsat5) : ¬ Percolation.Conjecture20
```

GeneratedCNFUnsat5 is exactly the nonexistence of a satisfying Boolean assignment for inputCNF5. There are no additional residual hypotheses on that theorem. The CNF UNSAT theorem itself is not proved. Accordingly this is not the requested unconditional negation, and no theorem named not_conjecture20_unconditional is supplied.
