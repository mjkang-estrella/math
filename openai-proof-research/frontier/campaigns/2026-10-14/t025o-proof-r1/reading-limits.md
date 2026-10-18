# T025O54 proof review r1: exact reading and limits

## Read in full

* Campaign rules: `AGENTS.md`, plus the "Acceptance and publication" section and status header of `frontier/NEW-TEN-2026-10-14.md`. The rest of that 1705-line ledger was only searched for headings and T025O/PASS strings. It was not read in full, and it contains no T025O entry.
* Frozen author packet `fresh-arithmetic-discovery-r54/`: `scope-status.md`, `candidate-proof.md`, `constrained-descent.md`, `alternative-route.md`, `contribution-comparison.md`, `reading-limits.md`, `chronology.md`, `checkpoint.md`, `selection.md`, `exact-checks.json`, `source025-receipts.json`, `source-family-inventory.json` (entry list), `manifest.json` and `verify.py`. `verify.py` was read before running.
* Source025 at the pin (packet copies, identities rechecked against the repository tree): `README.md`, `main.tex` (preamble), and in full `introduction.tex`, `elementary.tex`, `residues.tex` (every lemma and proof, including reciprocal-phase and deterministic), `random.tex`, `divisors.tex`, `descent.tex`, `counting.tex` and `prescribed.tex`.

## Not read or only partially read

* `references.bib`, `unicode-mappings.tex` and the source PDF were not read. Citation keys appearing in the read text were taken as they appear.
* Primary bodies (`private/primary/*`: Webb, Graham, Elsholtz): only a keyword search of `webb.txt`. These bear on contribution, not on proof correctness. No proof step depends on them, and the proof review makes no claim about them.
* `primary-identities.json` was authenticated by the author verifier but not read line by line.
* Not read: the parent intake `t025o-parent/`, any parallel or contribution review, I204/I205 and other iteration notes. Their absence does not affect any proof step.
* External theorems invoked by source proofs (Erdős–Turán, PNT, van der Corput differencing) are credited through the stipulated source and were not re-audited.

## Scope of the verdict

* PASS_FULL_T025O is relative to the stipulated truth of the pinned source025 lemmas, whose statements were read and whose hypotheses were rechecked at every use. The proofs of `lem:deterministic` and `lem:random` were re-run with the new parameters, because the author modifies them.
* No contribution, novelty, acceptance or count judgement is made.
* The finite checks in `independent-checks.json` are illustrations and identities only.
* Scratch: `/var/tmp/t025o-proof-r1-*` (copy of the author packet for the verifier replay, and review controls), removed on exit. No file outside this review directory was written, and the frozen packet's anchors were rechecked after all runs.
