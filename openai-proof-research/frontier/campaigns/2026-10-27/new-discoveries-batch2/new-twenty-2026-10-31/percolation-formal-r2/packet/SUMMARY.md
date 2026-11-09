# Round 2: closed semantic CNF bridge, conditional endpoint

This packet is partial. It does not prove the unconditional refutation and claims no acceptance or campaign credit.

The new endpoint is
`Percolation.not_conjecture20_generated : Percolation.GeneratedCNFUnsat5 → ¬ Percolation.Conjecture20`.
Its exactly one remaining hypothesis is:

```lean
Percolation.GeneratedCNFUnsat5 :=
  ¬ ∃ val : Percolation.SatVar → Bool,
    ∀ c ∈ Percolation.inputCNF5, Percolation.CNF.Holds val c
```

`inputCNF5` is a new unnormalized, Lean-side truth-table clause generator over PG5 incidence. No copied DIMACS file or LRAT certificate is used in any theorem. The semantic bridge to EVERY generated input clause is closed and kernel checked. `NoMinimalTwoRound5` remains unproved.

New closed pieces: finite closure stabilizes by q²+q+1 rounds; canonical closed deletion separators follow from literal Minimal; a finite Boolean system is equivalent in both directions to existence of a minimal time-2 witness; a general local truth-table CNF soundness theorem; and all clause-family satisfaction proofs for that system's CNF. The inherited definitions, original endpoint, controls, geometry and structural lemmas remain byte-identical. Audit.lean is extended to audit the new modules.

There are 38 modules (34 inherited, 4 new). The fresh extracted compiler/checker measurements and exact statuses are in results.json and fresh-extracted/logs/. Full development logs are retained under packet/logs/. Only propext, Classical.choice and Quot.sound occur in the new endpoint's transitive axiom list. Root alone decides acceptance.

Remaining work: prove UNSAT for this exact generated unnormalized CNF, or replace it with a smaller normalized CNF after proving normalization and exact generator correspondence; then provide kernel RUP replay, unconditional NoMinimalTwoRound5, and the unconditional endpoint. No certificate replay throughput is claimed: zero certificate additions were implemented or replayed.

Measured fresh replay: 38/38 strict compilations and 38/38 explicit-module checks passed. Compiler wall total 58.03 s; checker wall total 41.54 s; longest process 12.22 s; maximum reported peak RSS 1,635,432 KiB. Metadata audit: 258 local declarations passed. Source scan: 38 files, zero findings. The source-only archive extracted for these results has SHA256 27b5fa4f32aaa457c1290194a5938747b85acd268c49f8ff8bcdb017d2ae3887.
