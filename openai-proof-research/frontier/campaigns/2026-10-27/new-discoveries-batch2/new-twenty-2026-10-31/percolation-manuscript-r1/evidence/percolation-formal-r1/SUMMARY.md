# Partial formalization — MathDB 333709

Status: conditional, not an accepted refutation. No novelty or campaign credit is claimed.

Endpoint: `Percolation.not_conjecture20 : Percolation.NoMinimalTwoRound5 → ¬ Percolation.Conjecture20`.

Exactly one remaining Prop:

```
Percolation.NoMinimalTwoRound5 :=
  ¬ ∃ a : Percolation.Infection 5,
      Percolation.Minimal Percolation.PG5 5 a ∧
      Percolation.TimeIs Percolation.PG5 5 a 2
```

Closed pieces: general synchronous percolation definitions and least-time characterization; order-5 projective-plane incidence axioms and explicit quadrangle; dot-product correspondence; two-round minimal control at threshold 4 (mask 70588740); three-round minimal control at threshold 5 (mask 241579737); general monotonicity and fixed-separator soundness; and the structural exclusion of a fully initially infected line in a minimal threshold-5 set. All these are theorem proofs, including minimality against arbitrary proper subsets and percolation over unbounded natural rounds.

The finite nonexistence theorem is NOT proved. No CNF semantic bridge, symmetry normalization, or kernel LRAT replay is claimed. The original external SAT evidence has not been promoted to a Lean theorem.

See `results.json` and the fresh extraction logs for measured replay results. The source packet uses Lean 4.34.1 and its bundled Std only; no mathlib imports. The self-contained incidence structure avoids importing a much larger geometry library for this finite instance.

Fresh extracted strict replay: all 34 modules compiled and passed explicit-module leanchecker. Total measured compiler wall time: 49.75 seconds; total checker wall time: 37.74 seconds. The metadata audit passed for 121 local declarations; the 34-file source scan found no forbidden tokens. Per-module timing and peak RSS measurements are in `results.json` and `fresh-extracted/logs/`. No limits were raised.
