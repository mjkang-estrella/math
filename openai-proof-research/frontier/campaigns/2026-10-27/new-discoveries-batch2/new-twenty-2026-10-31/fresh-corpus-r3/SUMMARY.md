# Fresh corpus r3: research handback (Claude Opus 5.5 lane)

**One full-scope candidate with a complete literal Lean endpoint: MathDB 324342.** It refutes the Etzion–Vardy–Yaakobi conference-matrix MDS conjecture. It is NOT accepted: independent fidelity, novelty/significance review, a paper and the final replay are still pending. I do not self-accept and I do not update any counts.

## Coverage of the 40 reserved IDs

All 40 literal statements were read from the r301 corpus. `literal-records.json` records each one's chunk, line, chunk sha256 and line sha256; `scripts/provenance.py` re-verifies them. `results.json` is keyed by all 40 IDs and gives the review depth for each.

| Review depth | Count |
|---|---|
| Literal statement only | 30 |
| Primary statement read | 2 (324487, 324488) |
| Primary statement and relevant proof bodies read | 8 (323832, 323834, 324342, 324518, 324570, 324701, 324750, 324788) |

The routing `reviewed:false` flags were not treated as evidence of anything. No earlier human or technical notes on these 40 IDs were found in the project tree. Grep hits were numeric noise in OCR coordinate data, and keyword scans for the subjects found nothing relevant. This bounded search does not show that the old repository has no related work.

## Main result: 324342 refuted (literal Lean endpoint)

**Source.** Etzion, Vardy and Yaakobi, arXiv:1210.5725 v1/v2, Conjecture 5. It is unchanged as Conjecture 1 in the ISIT 2013 version. It asserts that the F_p row code of *any* conference matrix of order p+1 is MDS, with dimension (p+1)/2 and distance (p+3)/2. The authors verified it only on Paley matrices up to n = 23.

**Counterexample.** Take the Goethals–Seidel skew conference matrix W of order 20, built from circulants of order 5. Its F₁₉ row code is a [20,10,9] code:

- The dimension agrees with the source's Theorem 4.
- The distance is 9, not 11, so the code is not MDS. The exact value 9 was checked exhaustively by computer; Lean proves d ≤ 9.

**Context.** By a short Reed–Solomon argument, every Paley-equivalent conference matrix gives a doubly extended RS code, which is MDS. So the conjecture holds exactly on the class that was tested, and fails at the first order (20) where a non-Paley Goethals–Seidel matrix exists. Of the order-20 Goethals–Seidel matrices, 2,767 were tested exhaustively before a 30-minute background limit stopped that sweep (it was not restarted); all 2,767 are non-MDS. At order 12, all 432 tested Goethals–Seidel matrices give MDS codes.

**Lean packet: `conference/lean/`.**

- File: `ConferenceMDSCounterexample.lean`, sha256 `1b355df8…7f21`.
- Definitions: the source's weighing and conference matrix definitions, the row code, a literal minimum distance via `hammingDist`, and MDS as the Singleton equality.
- Main theorem: `conjecture5_false : ¬ Conjecture5`.
- Also proved: `counterexample_full`, stating the matrix is a conference matrix, finrank = 10, minDistance ≤ 9, and ¬IsMDS.
- `#print axioms` gives only [propext, Classical.choice, Quot.sound].
- The forbidden-token scan is empty.
- Finite checks use `decide +kernel`; there is no native_decide or ofReduceBool.
- Fresh extracted rebuild under `env -i`: rc 0. `leanchecker` replay: rc 0.
- Toolchain: Lean 4.34.1 (5045d005…) and Mathlib d13f23b7…, via the read-only `leanpath.txt`.
- An independent pure-integer replay (`conference/replay.py`) rebuilds W from the sequences and checks every certificate against the data embedded in the Lean file.
- Full dossier and fidelity points: `conference/PROOF.md`.

**Prior art (bounded, receipts kept).**

- The 2015 IEEE TIT version itself was not read (paywalled). The arXiv versions and the ISIT 2013 version all keep the conjecture open.
- OpenAlex lists 13 TIT and 3 ISIT citing works. A Semantic Scholar citation list was also fetched. None concerns this conjecture.
- Web searches found only adjacent work on self-dual codes from weighing matrices.
- The live MathDB page (HTTP 200) shows 0 solutions.
- openai/math head is `4eaee87548250b2682affda7d05d947c05554bae`, unchanged. Its truncated tree and the local preprints tree have no relevant paths.
- **Palomar is uninformative.** Revision 651 returns a body byte-identical to the empty `Hoge` receipt for every query, so the `q` parameter appears to be ignored.
- **Novelty is not certified.** Finite searches do not establish worldwide priority.

**Significance caveat for reviewers.** This is a single explicit counterexample of order 20 to a 2012–2013 coding-theory conjecture. Its value rests on the conjecture being stated for all conference matrices while tested only on Paley ones, on the dichotomy just described, and on the exact [20,10,9] parameters.

## Other selected targets

Full notes are in `SELECTED-NOTES.md`.

- **323834 / 323832 (Elder / Broadhurst third category).**
  - The primary statements were read, including the author's explicit invitation to find a small pseudocyclotomic counterexample.
  - An exact Φ̃_{p,q,r} search was run, using periodicity so that one r per residue class suffices. It covered odd p ≤ 15 with q ≤ 60, odd p ≤ 7 with q ≤ 150, and even p ∈ {4,…,12} with q ≤ 50. No violation was found. Both conjectures are **parked**.
  - The literal pseudocyclotomic domain includes p = 2. There, Φ̃_{2,q,r}(x) = Φ̃_{q,r}(−x) is always flat, and the "Moreover" clause fails exactly when q ≡ 1 (mod 2w); for example (2,7,17).
  - I assess this p = 2 case as a domain-edge/trivial-identity refutation with **zero credit**. It was not formalized.
- **324570 (Arratia–DeSalvo).**
  - New short proof that sup D ≤ 1 − c₀ ≈ 0.6557 < 1, which settles the source's Conjecture 1. That conjecture is still open in the published 2015 AAP version, and OpenAlex shows no citing works.
  - The MathDB literal also asserts that a global maximum is attained, which the source never claims. That part is unresolved, so this is a **partial result with no credit**. No Lean.
- **324701 (Hartke–Liu–Petříčková Conjecture 1.1).**
  - Exact SAT search with m = 3 (CaDiCaL): only the prism C₃□K₂ fails. The search covered all 1,253 atlas graphs up to 7 vertices and all connected cubic graphs on 8 and 10 vertices. **Parked.**
  - m = 5 results: see the **m = 5 search** section at the end of this file.

## Compact exclusions (detail in results.json)

| ID | Reason |
|---|---|
| 324788 | Proved in the source itself (Boussaïri–Ille: "We answer the conjecture positively"). |
| 324750 | Proved by Lu–Guo, arXiv:1503.07226, Theorem 2. |
| 324518 | Contradicted by the source's own Table 1 under its Definition 2.6 order; the EJC version drops it. |
| 324020 | Refuted by Balogh–Solymosi (2018). |
| 324821 | Refuted by Göös (2015). |
| 324822 | Routine corollary of Göös, since bp_or ≤ bp. |
| 324487 | Proved for large n (Csaba–Kühn–Lo–Osthus–Treglown), as the source itself states. |
| 324087, 324470 | Ill-posed. |

The remaining IDs are famous open problems or lack precise or restorable statements. They are parked at literal depth.

## Access and integrity

- arXiv, the EJC PDF, the Cambridge AAP PDF, the Yaakobi homepage PDFs, OpenAlex, GitHub API and the live MathDB page all returned 200.
- Semantic Scholar paper metadata returned 429 once and was not retried.
- Every request was made once. There was no bypass, no browser tab, no child agent, no git operation, and no shared-ledger edit. All writes are inside `fresh-corpus-r3/` and `/tmp`; the `/tmp` files are a networkx venv and scratch CNF files.
- Downloads are hashed in `artifact-receipts.json`, `sources/receipts.json` and `registry/receipts.json`.
- Experiments ran in at most 2 single-threaded processes.
- One exhaustive order-20 sweep hit its 30-minute background cap and was not restarted. Its partial log is `conference/exhaustive_m5.log`.
- A first m = 5 fractional-power run stalled on a complete-graph SAT instance; complete graphs are already proved in the source, so it was stopped. It was rerun with complete graphs excluded and a per-instance solver limit.

## Replay

Run from `fresh-corpus-r3/`:

    python3 scripts/provenance.py
    python3 extract_records.py
    (cd conference && python3 replay.py && python3 verify_cex20.py && python3 rank_cert.py)
    (cd conference && OMP_NUM_THREADS=1 python3 exact_distance.py)
    (cd conference/lean/clean-rebuild && env -i HOME=$HOME PATH=/usr/bin:/bin LEAN_PATH="$(cat ../leanpath.txt)" \
        /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean ConferenceMDSCounterexample.lean)
    (cd pseudocyclotomic && OMP_NUM_THREADS=1 python3 pseudo.py 9 30 odd)

The fractional-power scripts need networkx; it was installed in `/tmp/venv-r3`.
