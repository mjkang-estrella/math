# Verification record

Verified locally on 2026-10-25 with Lean 4.34.1 and the dependency pins in
`formal/pins.json`.

- **Main mathematical claim:** a strictly positive real 3-by-3 premagic
  matrix is not diagonalizable, even over the complex field. Its exact
  entries are fixed by `PremagicCounterexample.M`.
- **Compilation and trust:** all 37 local Lean declarations were compiled
  with warnings treated as errors. Their transitive axiom sets are subsets
  of `{propext, Classical.choice, Quot.sound}`. The audit checks every
  local definition/theorem and rejects omitted or duplicate reports.
- **Clean local replay:** the parent ran `formal/rebuild.py` with explicit
  executable and dependency paths. It removed old local compiled outputs
  and rebuilt the proof and audit modules successfully.
- **Archive replay:** a separate extracted release copy passed all file
  hashes and rebuilt the same 37 declarations from its own source files.
  The replay reused the pinned external compiled dependencies, as disclosed
  in the formal audit. It did not rely on the original local proof's object
  file.
- **Mutation controls:** changing one matrix entry or asserting a false row
  sum caused Lean to reject the modified proof sources. These checks
  prevent a vacuous success report from being mistaken for verification.
- **Independent arithmetic:** exact rational computations checked the
  Jordan chain, row/column sums, ranks, characteristic-polynomial values,
  change of basis, four shifted/stochastic examples and 30 larger examples.
  Finite computations supplement rather than establish the universal proof.
- **Sources:** the parent verified all six recorded downloaded source
  hashes and inspected the original premagic definition and conjecture.
- **Paper:** Tectonic 0.17.0 built a four-page PDF with no unresolved
  references or overfull boxes. The parent inspected all four final pages.
- **Final independent review:** `notes/final-review.md` reports PASS with no
  substantive findings after checking the source match, written proofs,
  definitions and exact formal-coverage distinctions. This review used the
  explicitly requested ultrafast service tier.

The release contains the full Lean type/axiom transcript and machine-readable
build receipts under `verification/receipts/`. Mathematical review is in
`notes/math-review.md`, source review in `notes/source-review.md`, and formal
audit in `formal/notes/formal-audit.md`. These are internal AI-assisted
reviews; they do not establish human peer review or worldwide priority.

The verified main result has no dependence on the stipulated OpenAI
research corpus. The written and formal coverage boundaries are detailed
in `COVERAGE.md`.
