# Progress — G contribution audit r1

- Created owned directory and initial status. No candidate code executed yet.
- Hash-only authentication of frozen r9 (inline python, bytes only, no stored code run): seal.json SHA256 matches external 13658895…85c4; seal.sha256 consistent; inputs manifest 111 files, outputs manifest 19 files, all sizes/SHA256 match; exact membership (no extras/missing/symlinks); 13/13 pinned upstream blobs match Git blob SHA1 in preprints-tree.json at fd4aeeb2…; candidate.md SHA256 5c339f83…7144; original-scope.md d8686a39…34a6.
- Read full candidate.md (738 lines), original-scope, source-contracts, literature-screen, working-math.
- No pinned OpenAI catalogue/preprint path matches barrier/Pareto/random-resistance CRT operator (grep CONTENTS.md + preprints-tree directory names).
- ADN 2009.08185v1 read: lines 1-420 (Thm 1.1, Rem 1.2, (1.6)-(1.8), Thm 1.3, Cor 1.4, Prop 1.5-1.6), 600-940 (Prop 3.2 coarea proof, Prop 3.3 continuity, Lemma 3.4, start of proof), 1265-1504 (Cor 4.7, Lemma 4.8, Lemma 4.9, Cor 4.10, Rem 4.13), 2625-2824 (Prop 7.1 + proof, Lemma 7.2, Thm 7.3 statement).
  Checkpoint finding: ADN (1.8)/Prop 3.2 is exactly the coarea identity of candidate (4.6); ADN Prop 3.3/Lemma 4.8/Cor 4.10 is the unmarked, unlocated version of (4.3)/(5.1); ADN Thm 1.1(i)/Prop 1.5 gives the alpha>1/2 finiteness (5.2). Location (preorder interval) and link thinning are not in ADN statements.
- Croydon 1609.05666v1 read lines 24-153 (Assumption 1.1 requires boundedly compact resistance spaces), 1462-1531, 1800-1830. CHK 1609.02120v1 Section 6 lines 1460-1669 (Assumption 6.1, Lemmas 6.2-6.3, Prop 6.4): resistances omega^-1<=1 homogenize; heavy conductances give FIN speed under CSRW clock. Not G.
- Bounded web screen (7 queries, 2026-10-16), results title/abstract level only; no barrier-on-CRT operator theorem found. Yang 2408.07139 abstract: homogenized segment regime only.
- Faggionato 2012 read lines 540-599 (Thm 2.5) and 2067-2211 (proof Sec. 9). Pinned trees.tex full, blocks.tex 1-60/180-237, metric.tex 1-135. Fill-Janson lines 120-299 (Thm 1.3 needs E xi^{2+delta}; candidate does not use it as premise). Archer/Andriopoulos abstract + assumption locations only.
- ADN additional lines 240-259 ((1.8), Thm 1.3) and 1835-1859, 2245-2269 (Sec. 6.1 straddling-excursion coding T^-_{r,s},T^+_{r,s}; (6.17) Z_f=int ds int dr f(sigma_{r,s},h_{r,s})). Finding: interval location of candidate (4.4)-(4.6) is ADN's straddling-excursion coding with f depending on endpoints instead of length.
- Prior F contribution review (history) and parent corrections P1-P4 read for campaign standard; fk-stable-cut-proof-r1 still not read.
- reviewer_checks.py extended with exact preorder interval coarea (4.4) on 61 trees N<=9 plus a drop-self control; rerun receipt all true, all controls rejected.
- Tentative verdict: TECHNICAL. Writing review.md.
- Final: verdict TECHNICAL for full unchanged G. review.md written; manifests and detached seal built after this line. No commits, no edits outside this directory.
