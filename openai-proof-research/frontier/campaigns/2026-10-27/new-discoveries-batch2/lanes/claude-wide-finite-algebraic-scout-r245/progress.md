# progress (r245)

1. Read ancestor and batch AGENTS.md, then ledger.json and prior-campaign-context.json as structured summaries. Read the r245/r246 root STATUS. Snapshotted admin hashes into `administrative/admin-snapshot-sha256.txt` (no copies).
2. Built the guarded tool `work.py` (fetch, freeze, extract, read, history, seen) and `g.sh`. `g.sh` wraps the fixed helper_guard with OPENBLAS/OMP=1 and PYTHONDONTWRITEBYTECODE=1. Built the seen-id index of 20,403 ids.
3. Ran arXiv searches in recent and older finite/algebraic families. Froze and extracted 26 PDFs plus 3 HTML pages.
4. Candidate A (2305.00279):
   * Identified the GCM class with cographs.
   * Wrote a canonical graph generator and a Young-orthogonal-form spectrum screen.
   * Ran it exhaustively for n ≤ 9 (n = 9 needed resumable levels after a MemoryError on merge). No hit.
   * First-failure irreps recorded; K3□K3 is the exception.
5. Candidate F (Das Conj 5.1):
   * Random greedy search found an n = 5 counterexample immediately; I verified it by hand.
   * Exhaustive n = 4 gives 6.
   * Local search gave lower bounds for n = 5..10.
   * MILP: three failed attempts (abort and bad_alloc), traced to locale-archive VmSize; fixed with LC_ALL=C. Exact f(5) = 10. The n = 6 MILP failed with bad_alloc.
   * Derived the family F_n (4n−10) and its cut-set proof. Verified n = 4..30. Searches seeded at F_n found no improvement.
   * Proved the 6n−6 upper bound.
6. Prior art for F: history (0 hits), arXiv follow-ups, two web searches, ISI repository and IIT thesis landing pages. The ScienceDirect body was not attempted (denied route).
7. Candidate DBG Conj 3.3: exact F_q counts, 28/28 agree.
8. Wrote SCOUTING.md, discovery.md, SUMMARY.md and provenance.json. Final manifest and separate verification are via `verify.py`.
