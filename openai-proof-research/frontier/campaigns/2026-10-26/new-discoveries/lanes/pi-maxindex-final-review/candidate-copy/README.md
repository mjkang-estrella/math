# Sharp maximal index for arithmetic and geometric entry arrays

**Candidate, discovery credit0.** One combined general outcome is proposed for Caro–Graswald Conjecture4.19 (published IV.19), MathDB347947: for every dimensiond≥5, the largest index with the universal inequality is exactly2d−5. All indices0≤k≤d² are classified. Universal strict sufficiency also holds for d≥3. The full probability simplex, ordered d²entries with multiplicities, and independent arithmetic/geometric sorting are used.

The complete proof is in PROOF.md and the three-page manuscript main.tex/paper.pdf. All76declarations in12Lean modules passed a fresh isolated strict replay with Lean4.34.1, pinned mathlib/dependencies, warningsAsError, no proof holes or new assumptions and only propext/Classical.choice/Quot.sound. Every declaration type and axiom inventory was read. The final `MaxIndex.source_index_classification` is an actual sorted-array iff statement; selection attainment, exact cardinality, largest-entry exchange with ties, sorting bridge, incidence constraints, geometric normalization, the full sharpness family and reindexing onto Fin d are all proved. No residual finite-array or numerical-certificate premise remains.

Reproduce from this directory, using exact pinned dependencies:

```sh
python3 verification/verify_candidate.py . --lean-bin /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean --packages /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
python3 scripts/check_bounds.py
```

The parent manuscript build has zero reported issues; all three pages were rendered and visually inspected. A preliminary independent source/math review found no mathematical gap and checked the actual published paper embedded in Caro's thesis. That review predates the full Lean development and manuscript, so its formal/manuscript-pending statements describe the frozen artifact reviewed then. It read only abstracts of the three indexed citing papers; full-body coverage and independent formal/manuscript review are still required. See reviews/preliminary-review.md, unchanged provenance, and the parent addendum. The final extracted proof-packet replay is also pending. Accepted campaign tally remains11/30.

Elementary incidence counting, selection maxima and Cauchy–Schwarz are standard ingredients. One source-question conclusion is proposed, with no per-dimension, direction, helper or sharpness-family extra counts. The research-only full small-dimensional classification is not claimed by this Lean endpoint or manuscript. Source/citing searches are bounded and cannot certify worldwide priority. No external posting, publication, author contact, messages, upload or push occurred.
