# T165P135 contribution review r1 — REPORT

Provenance: Factory Droid / claude-opus-5-5 / high, 2026-10-20. Reviewer author of original prose:
Myeongjin Kang (no affiliation), CC BY 4.0; original code MIT. Role: independent SUBSTANTIAL-CONTRIBUTION
review, conditional on correctness, at the entire unchanged frozen scope. No correctness verdict, no
acceptance, no count, no priority finding. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated true.

**Verdict: SUBSTANTIAL (conditional on correctness)** for the entire unchanged frozen scope: for all
positive m, n, every even-adjacent (weakly semisimple) drawing of K_{m,n} has at least d_m d_n oddly
crossing unordered edge pairs, d_r = floor(r/2) floor((r-1)/2), with balanced-axis exactness and the
corollaries ocr±(K_{m,n}) = ocr+(K_{m,n}) = pcr+(K_{m,n}) = d_m d_n = cr(K_{m,n}) (last equality via pinned
thm:main). Unrestricted ocr/iocr/pcr and Harborth tripartite are outside scope and remain so.

Basis, in one paragraph: no located statement or composition yields the theorem — the pinned bipartite
preprint and its complete-graphs companion contain no parity content; Pach-Toth 2000, Szekely 2004/2008,
FPSS 2012, BFK 2015, and the DS21 survey contain no exact odd/pair crossing value for K_{m,n} in any class;
the classical GF(2) theory (Tutte/Levow via the record) is documented as not precise enough to decide exact
values. The pinned mechanism's two load-bearing operations fail verbatim in characteristic 2 (two-sided
averaging divides by 2; the detector input is signed with division). The author's transport replaces them
with a one-sided shift plus exact diagonal bookkeeping annihilated downstream by Phi (Lemma 3), a 0/1 order
matrix feeding the pinned factorization (Lemma 8), and the identification of even-adjacency with
diagonal-block invertibility (Section 8) — constructed steps, not citations.

- Not REDISCOVERED: no prior statement of the theorem, of the exact values, or of the transport located
  (full bodies read: Pach-Toth 2000, FPSS 2012, BFK 2015, Szekely 2008; DS21 entries; arXiv:2610.25204v1;
  both pinned preprints; bounded web and project-history searches in packet/public/review.md Sections 7-8).
- Not TECHNICAL: unlike t184i134 (operative step = Kang's Lemma 2.2) and t106o133 (archived routine
  transfer), the operative steps here are constructed because the pinned steps they replace have no
  characteristic-2 image; consistent with SUBSTANTIAL precedents t088p133, t205m, t117q.
- Correctness NOT assessed: parent-recorded attention items (Lemma 2 apparent t(u1,·)=0 typo cancelling
  mod 2; Lemma 1 round-disk/no-reentry normalization for arbitrary continuous arcs) remain for the
  correctness gate. Verdict is conditional on correctness; the next required gate is an adversarial
  correctness review.
- Freeze-timing disclosure preserved: author-recorded freeze 2026-10-20T18:22:29Z with substantial
  characteristic-2 feasibility prefreeze; no independent timing certification.

Artifacts in this root: packet/public/review.md (full review), packet/public/reading-limits.md, FINAL.json,
anchors.json, unchanged.json, CONTROL-RESULTS.json, controls/control-runs.log, work/input-hashes.txt,
work/acquisition-register.json, integrity-report.json, check-originals.py, fetch_pinned.py, primary/,
scratch/. Author detached anchors recomputed and matching: FINAL.json
9e01e0dbcdab7665d6ce58c904291cb3caeaef9e54f5befb023336abe21f6be6; packet/MANIFEST.json
6b997e3d8605220fc4845528d8213356c792e7d674eab50d7be9d16d4730eae5; REPORT.md
4ecc09d4de9fe7e2f5e095b7b0ac2215a6665438898378e6ee8c91de6b0e037e; frozen-statement.md
1000a115e013b3bc28247fdc03f33b8d4ae3ee8ee2a41ce4da55c79e1081a99d; proof.md
a12854336cc118cc9a49dd96bb72aeb142e618ab3466a2e1dc648ff77bf98f10.
