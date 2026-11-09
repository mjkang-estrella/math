Corrections applied in the root-review copy (lane common-basis-final-replay-pi-r1), 2026-11-05

1. Section 7 of the paper said the conjecture is printed "in five arXiv versions". v1 predates the
   formulation (only White Conjectures 1-2); the conjecture with identical quantifiers appears in
   v2/v3 (Conjecture 13) and v4/v5 (Conjecture 2.5), plus the journal and the 2016 workshop list.
   Corrected to "arXiv versions v2-v5, the journal, and an independent 2016 workshop problem list".
   The correct fine-grained history elsewhere in the paper (v2/v3 Conjecture 13, v4/v5 Conjecture 2.5,
   v1 predates) is retained unchanged.

2. Section 8 of the paper and the old REPRODUCE.md overclaimed replay.sh: it inherits PATH/HOME/Lean
   env and enforces no affinity/CPU/wall/RSS/AS limits, no nonempty-build-dir rejection, no dependency
   hash verification. The paper now describes replay.sh honestly as a historical convenience script and
   points to the enforced wrapper capped_replay.py; a corrected REPRODUCE.md ships in the root-review
   lane; the original script is retained here and in source-only/ with an honest history note
   (CORRECTIONS.md in source-only/).

3. Status corrections: the independent strict Lean-fidelity audit (common-basis-fidelity-pi-r2) is
   COMPLETE (verdict PASS on all gates) and a fresh enforced final replay was performed in the
   root-review lane (24/24 strict stages + 106-declaration body-presence audit + negative controls;
   see verification/). The narrow module-origin/full-type audit supplement and final root acceptance
   remain pending and are NOT claimed anywhere in the corrected materials.

Original reviews, the raw record, primary-source receipts, and the original scripts are retained
byte-identical; new verification evidence is additive under verification/ and paper-root-review-copy/.
