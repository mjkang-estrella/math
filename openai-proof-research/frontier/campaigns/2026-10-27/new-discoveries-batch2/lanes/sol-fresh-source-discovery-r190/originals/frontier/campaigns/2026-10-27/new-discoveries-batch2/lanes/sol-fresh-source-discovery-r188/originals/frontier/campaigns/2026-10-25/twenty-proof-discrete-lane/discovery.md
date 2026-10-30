# Discrete research lane — 2026-10-25

## Completed outcomes and counting

Exactly **two distinct MathDB question IDs** have complete Lean certificates in this lane. Auxiliary lemmas are not counted separately.

| MathDB | Outcome | Prior status and novelty limit | Packet |
|---|---|---|---|
| **354537** | Universal proof of the scaled Tepper identity; strengthened from positive integer steps to every nonzero real step. | Source Conjecture 4.5 remains labeled conjectural in arXiv:2205.04237v1. The API snapshot has no solutions, comments, formalizations, or attempts. This is an elementary consequence of finite differences, and also follows immediately from source Theorem 4.3 by scaling; no worldwide-priority claim. | `scaled-tepper-354537/` |
| **317856** | Universal positive-semidefiniteness proof via an exact Gram factorization; generalized to any finite color set and any nonnegative feature size. | **Already resolved in 2017** by Cooper–Forst, arXiv:1704.01644v2, Corollary 3 and Proposition 4. The MathDB snapshot incorrectly labels the question open and lists no solutions. This is a formalized verification, not a newly solved open problem. | `monochromatic-box-317856/` |

If the campaign counts only previously unresolved questions, this lane supplies **one candidate resolution plus one known-result formal verification**, not two new open-problem resolutions. The stronger real-step result and finite-color generalization do not add question IDs.

## Screening and exclusions

Read the repository AGENTS.md. All modifications, downloaded records, proof code, build output, and scratch work are confined to this lane. No agents spawned, no shared indexes edited, no staging or commits.

The saved public API listing snapshots cover combinatorics, graph theory, set theory, and combinatorial games. Screening prioritized empty solution lists and smaller finite descriptions. Initial highly active entries often already had posted solutions; those were not chosen for recomputation. Named major open problems were excluded as unrealistic lane targets.

- Games #375237 and #323014: exact source statements read; small bounded exploration is insufficient for a general period conclusion, so not selected.
- Games #371181–#371184: source arXiv:2510.24280v1/v2 read. #371181's MathDB formula has a transcription mismatch with corrected v2 Conjecture 12. This is a source correction, not a result. Bounded tests of #371183/#371184 found no counterexample and are not proofs.
- Finite grid #333040/#333041: original Conjectures 1–2 of arXiv:1605.00180v5 read. Exact bounded constraint searches found no violating small grid; larger runs timed out. No numerical-only claim counted.
- Higher-dimensional queens #363467: original Conjecture 3 of arXiv:2406.06260v1 read; small cases were already known in that source. Not selected.
- Z-curve questions #365145/#365147/#365148/#365149 and various algebraic/combinatorial candidates were screened but not promoted. None contributes a claimed outcome here.

Only #354537 and #317856 were promoted to proof packets. Saved screening records do not represent attempted or solved question counts.

## Validation

Both source files compile with Lean 4.34.1 and the provided pinned mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. Each packet has a rebuild driver adapted from the premagic certificate: clean local output, exact dependency-pin checks, warnings as errors, forbidden-proof-token check, and `#check` / `#print axioms` coverage for every definition and theorem.

Each build audit lists only `propext`, `Classical.choice`, and `Quot.sound`. No admitted proofs, custom axioms, or native decision procedure are used. See each `formal/build/audit.json` and `formal/build/Checks.log`.

Paper sources are included; no PDFs were generated, as requested.
