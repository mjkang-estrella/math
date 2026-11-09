# irpath-manuscript-r1: DRAFT manuscript and dossier for MathDB 350452

Lane irpath-manuscript-r1 (Claude, claude-opus-5-5). Status: **DRAFT**, not self-accepted, zero credit; root decides.

## Manuscript

- **Title:** *The path P_9 is an IR-graph: a nine-vertex counterexample to the Mynhardt–Roux path conjecture*.
- **Files:** `paper/manuscript.pdf` (7 pages, sha256 `07ca3a45…459f`) and source `paper/manuscript.src`, built by `scripts/build_pdf.py`.
- **Authorship:** no human author is listed. The manuscript states its draft status and AI assistance explicitly and makes no priority claim. Part (ii), on cycles, is not claimed.
- **Content:**
  - the source definitions, quoted from arXiv:1812.03382v3;
  - the known results;
  - both conjectures verbatim, with the authors' "we believe this to be true", and the MathDB conjunction;
  - Theorem 1, that G(IR) ≅ P_9, with a complete hand-checkable proof (see the outline below);
  - Figure 1, showing G and the path;
  - Tables 1–4, generated from fresh outputs;
  - the search census through order 9 (Table 5);
  - the Lean correspondence (Table 6), audits, replay and trust limits;
  - related work and the bounded prior-art screen, with the unread journal versions stated as a limitation;
  - modest significance, and provenance.
- **Proof outline** (Theorem 1):
  - heredity, plus the identity PN(v,D) = U(D−v) − U(D), where U = undominated vertices;
  - the 9 dominating pairs;
  - triples in classes (a) 54, (b) 21 with witnesses, and (c) 9 = the IR-sets;
  - no irredundant 4-set, because the sets W_i share two vertices only along the path. Explicit witnesses are also given: 121 four-sets via a dominating triple, plus the 5 sets U(w);
  - the 36 IR-set pairs: 8 share two vertices, and all 8 are swaps along edges.

## Fresh recomputation (all capped, sequential)

- **Finite facts** (`outputs/graph-facts.json`):
  - G has 20 edges, degrees 4/5, is connected, and |Aut| = 2.
  - Irredundant sets by size: 1, 9, 36, 9, 0. So IR = 3, with 9 IR-sets.
  - Triple classes are 54/21/9; four-sets split 121/5; the IR-graph is the path W_0..W_8.
- **Search:**
  - The class counts 1, 2, 4, 11, 34, 156, 1044, 12346 match the known numbers.
  - None of the 13,598 graphs of order ≤ 8 has an IR-graph P_m (m ≥ 3) or C_m (m ≥ 5).
  - Order 9: 3,160,576 labelled extensions give 21 hits in 3 classes: P7 (6, 22 edges), P8 (10, 21 edges) and P9 (5, 20 edges, the class of G). There are no cycles.
  - This matches the discovery lane and the review.
- **Numbers check:** `receipts/numbers-receipt.json` checks 68 claims (text fragment plus computed predicate); all pass.

## Lean

- **Packet:** `lean/source.zip` is byte-identical to `irpath-formal-r1/source.zip`, sha256 `953331d0a5ed9984657fdfb8f35822e8383c19c7adf10a31c6390e0e961439ee`.
- **Safe-extraction test:** PASS. There are 16 members; the 8 modules match `module-order.txt` and equal the formal lane's final extraction. The endpoint `IR350452.conjecture_false : ¬ IR350452.Conjecture` and the control `nonvacuity : IsIRGraph (pathGraph 2)` were located.
- **Lean not run:** this lane did not run Lean. The root replay was PASS and the registry refresh CLEAN (copied in `inputs/root/`).

## QA

All 7 pages were rendered (`qa/page-1..7.png`) and inspected. See `qa/visual-qa-receipt.json`. Earlier layout defects were fixed.

## Integrity

- The inputs were hash-bound before and after: 560 files, unchanged.
- `MANIFEST.sha256`, `paper-source.zip`, `full-dossier.zip` and `archives.sha256` are produced by `scripts/package.py`.
- Deviations are listed in `receipts/process-record.md`. Initial reads preceded hashing; one inline text edit was not capped; trial builds were deleted.

## Limits

- The journal versions (DAM 2022, DM 2022) are unread.
- The prior-art screen is bounded.
- The search results are computational.
- The order-10/11 growth observations (up to P_14) are UNVERIFIED and not claimed.
- P_6 and all cycles C_n (n ≥ 5) remain open.
