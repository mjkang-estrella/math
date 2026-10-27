# progress.md — pi-discrete-discovery-r7 (2026-10-27)

1. Read campaign context: RESULTS.md, NEXT.md, ledger.json (25/30 accepted;
   exclusions list; counting standard), pi-discrete-discovery-r2/FINDINGS.md,
   pi-discrete-discovery-r3 sources, pi-next-discovery progress (corpus cache).
2. Live-fetched all five MathDB records (sources/m37*.json): all open, 0
   solutions, 0 comments. Corpus cache cross-checked (1708 open / 0-solution
   metadata); corpus-open-0sol.json known-empty (not an openness result).
3. Fetched primary PDFs: vatter-2602.16355 (5pp, Conj 2.1 read in full incl.
   Pouzet–Rosenberg half-increase theorem, composition case ≤ 34, Murphy data),
   bbk-2601.04014 (18pp, Conjectures 1.1/5.1/5.2/5.4 and Appendix A read),
   xie-2303.14671, tura-2006.03136, later survey-2610.22838 and
   positivity-2601.19845.
4. Built exact machinery for G_{k,n}: series division (gkn_series.py);
   cyclotomic factored pole decomposition and exact eventual-periodic tail
   (gkn_tail2.py); validated against direct series on 15 (k,n) cases
   (validate_tail2.py) — all OK.
5. Derived and proved (short counting argument) that all poles are simple
   (s_c ≤ 1); confirmed by exhaustive scan (n ≤ 299, k ≤ 599): max s_c = 1.
   Hence the coefficient sequence is eventually exactly periodic — no
   polynomial-growth escape route for counterexamples.
6. Massive exact scans: (k ≤ 200, n ≤ 20) and (k ≤ 60, n ≤ 25), every
   coefficient checked (initial segment exact division + full-period tail):
   zero counterexamples, zero inconclusive. Margins recorded (margins.json):
   k ≥ 2 min-tail/C ≥ 0.6; k = 1 tight at 0.
7. Established H_{3,5} counterexample-to-the-stronger-H-form (negative
   coefficients) — the (1−q^{2n+1}) division is essential.
8. Ruled out: naive k/n inductions, Chern–Wang substitution-of-one transfer,
   half-integer q-binomial route.
9. Prior-art: S2 citations of 2601.04014 (5 records) — Chern–Wang 2601.19845
   resolves the *implied* m=1 conjecture for all k but not the G-refinement
   (full text read); others off-topic (bodies of two unread, documented).
10. 346778: resolved by Tura LAA 612 (2021) per survey Theorem 3.8 + Crossref
    — excluded as stale.
11. 373197: exact search — all n ≤ 10 + 210 larger, unimodal; one spurious hit
    from a buggy DP refuted by brute force (documented).
12. Wrote FINDINGS.md, discovery.md, provenance.json; no counts, no shared
    edits, no commits.
