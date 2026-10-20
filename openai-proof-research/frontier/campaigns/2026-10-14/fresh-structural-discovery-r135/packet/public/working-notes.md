# Working notes — fresh-structural-discovery-r135

Provenance: Factory Droid / claude-opus-5-5 / high. Round start 2026-10-20T17:24:43Z
(notes/start-time.txt). Two session segments: ~17:24–18:00Z (prior segment, survived via
context summary) and ~18:00Z–end (this segment). Durable notes were kept at
notes/working-notes.md from 18:05Z onward; this file is the consolidated final version.

## Mandate
Round r135 (campaign 18/20). One substantial full-scope result or honest PREFREEZE/no nominee;
freeze exact scope before proof drafting; no self-gates/count/priority claims; write only this
root; active rounds fresh-arithmetic-discovery-r99 and fresh-analytic-discovery-r133 excluded
(not entered, not read). Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated true.

## Phase 1 (prior segment): direction search
- Read r134 parent disposition, adoption, T184I134 review and reading-limits as directed.
  Registered lesson: identify the operation left unpaid after the strongest integrated
  primary/source reduction; no grade-shopping of T184I134/T106O133.
- Screened family list against prior structural rounds (157,170,167,171,160,164,166,176,159,175,
  099,089,183,156(R029),165(R027); r134: 181,189,190,118,192,162,248,185). Chose family 165
  (crossing-number formulas), motivated by: (i) the pinned preprint newly proves full Zarankiewicz
  (thm:main), changing the landscape; (ii) proposals/combinatorics.md line ~139 lists
  "unconditional versions of conditional crossing-number results (165)" as a gap; (iii) R027
  occupies only the K_n-minus-edge operation.
- Fetched and authenticated (packet/public/fetch.py; Git blob SHA-1 + size against
  preprints-tree.json SHA256 eeecc1da…09b) 11 files of
  preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026 into
  packet/private/source; all receipts OK.
- First candidate: Harborth's conjecture for K_{2,m,n}, cr(K_{2,m,n}) = Z(m+2,n+2) − mn for all
  m,n. Read Yang–Lu–Chen–Yang arXiv:2201.09465v1 (lines 1–679 of text extraction), Yang–Wang 2021
  (HC for K_{1,m,n} from ZC — excludes the K_{1,m,n} branch as routine), Ho's K_{2,4,n} paper
  (scanned; case analysis on K_{2,4} drawings).

### Prefreeze feasibility computation for K_{2,m,n} (negative)
With apexes a,b and classes M,N, write u = crossings among M–N edges, p,q,r,s for the
apex-edge/MN-edge and apex/apex crossing blocks. The subdrawings (M∪{a,b})×N and M×(N∪{a,b}) are
drawings of K_{m+2,n} and K_{m,n+2}, so the pinned thm:main gives
2u + p + q + r >= d_{m+2} d_n + d_m d_{n+2}. The best one can extract is
cr >= (d_{m+2} d_n + d_m d_{n+2})/2 + (a,b-cross terms). For m=n=4 this gives 12 against a target
of d_6^2 − 16 = 20; generally the subgraph bounds reach only about half of Z(m+2,n+2) − mn, and the
deficit must come from a-star/b-star crossings that an optimal drawing minimizes — exactly the
unproved heart of Harborth's conjecture. Conclusion: not proof-feasible in this round; no new
operation found that the pinned machinery pays for here. (This direction was NOT frozen.)

## Phase 2 (this segment): pivot to the parity strengthening
- Checked arXiv 2610.25204 (Balogh–Layman–Lidický–Pfender–Salazar–Spiro–Volec, 2026-10-18):
  flag-algebra asymptotics (0.96936 Z), explicitly pre-dating the pinned proof; no overlap with an
  exact parity statement.
- Read the pinned introduction precisely: it stresses that "the distinction between crossing
  points, crossing pairs, and parity-based crossing counts is important; we use the ordinary
  point-count convention throughout" — the parity variant is explicitly out of the source's scope.
- Key observation (prefreeze): the source's lower-bound chain is rank R_{ik} <= |{off-diagonal
  nonzero entries of J^{ik}}|. Over the reals this over-counts odd-crossing pairs (a twice-crossed
  pair with equal signs has nonzero signed sum), so the real machinery does NOT give a parity
  statement. But every ingredient has a GF(2) shadow, with four genuine replacements:
  (i) crossing parity chi instead of signed intersection I; a native mod-2 chord formula
      (alternation = sum of four comparison bits);
  (ii) the source's two-sided shift averaging (which kills shared-spoke terms and creates the
      1/2 factors) collapses mod 2 — replaced by a one-sided shift with exact diagonal
      bookkeeping J_2(s,s) = delta_{v,s} + delta_{w,s}; the diagonal values are then annihilated
      by the detector, so they never matter;
  (iii) the half-sign spoke matrix has no mod-2 image — replaced by the 0/1 strict-order matrix,
      whose invertibility under Phi is recovered by an additive row flip turning the support into
      the two-triangle pattern Q_s (verified: Phi(T) = A_Q D A_Q^T over char 2);
  (iv) the subspace lemma's "infinite set" step needs an infinite field — taken of
      characteristic 2 (e.g. GF(2)(t)); every other step is characteristic-free (checked line by
      line: division algorithm, Lagrange interpolation, minor-degree bound, determinant
      divisibility from rank deficiency).
- Hypothesis identification: the diagonal blocks J_2^{ii} are pure order matrices exactly when
  adjacent edges cross evenly (the "weakly semisimple" class, ocr± of Balko–Fulek–Kynčl via
  Schaefer's survey DS21). The axis drawing is in this class with exactly d_m d_n odd pairs, so the
  frozen theorem is exact, full scope (all m,n).
- Literature/history check (details in reading-limits.md): Schaefer DS21 survey entries for
  ocr/iocr/pcr (quadratic comparisons only; no exact K_{m,n} values); web searches for
  odd/pair-crossing Zarankiewicz (no exact determination found; no post-2026-10-06 follow-up
  deriving parity corollaries found); project history greps (no prior odd/pair/parity crossing
  work; R027 is ordinary cr of K_n − e; the kn-minus-edge lineage engaged Sadhu's
  cr(K_{m,n} − e) claim — a different operation; the bipartite preprint was not used by any prior
  contribution).
- Sanity of target on small cases: even-adjacent lower bound d_3 d_3 = 1 for K_{3,3} consistent
  with Hanani–Tutte (iocr(K_{3,3}) >= 1); d_3 d_5 = 2 consistent with cr(K_{3,5}) = 2; K_{4,4}: 4.

## Freeze
Frozen statement written 2026-10-20T18:22:29Z, BEFORE proof drafting:
packet/public/frozen-statement.md, SHA-256
1000a115e013b3bc28247fdc03f33b8d4ae3ee8ee2a41ce4da55c79e1081a99d (recorded in
notes/frozen-sha256.txt). Scope: for all positive m,n, every even-adjacent drawing of K_{m,n} has
at least d_m d_n oddly crossing edge pairs, plus exactness via the balanced-axis drawing, with the
ocrpm/ocr+/pcr+ equalities as frozen consequences and explicit not-claims (unrestricted ocr/iocr/
pcr; Harborth tripartite; no priority/count claims).

## Phase 3: proof and checks
- Full author proof written at packet/public/proof.md against the unchanged frozen bytes:
  Lemma 1 (parity-preserving normalization), Lemma 2 (chord parity), Lemma 3 (cycle pairing over
  GF(2), one-sided shift + diagonal bookkeeping), Lemma 4 (additive block relation), Lemma 5
  (subspace bound over infinite char-2 fields, full proof), Corollary 6 (rank-sum), Lemma 7
  (two-triangle interpolation, any characteristic), Lemma 8 (detector over char 2 with the
  row-flip), Section 8 assembly (odd n), Section 9 deletion (even n, identity n d_{n-1} =
  (n-2) d_n), Section 10 axis drawing (exactness, adjacency, single crossings, genericity).
- Mechanical sanity (packet/public/sanity.py, PYTHONDONTWRITEBYTECODE via -B; writes nothing):
  all checks (a)–(h) passed, including a GF(16) implementation of the detector (tournament
  invertibility for all 6 orders at s=1 and 40 sampled orders at s=2; annihilation; support bound;
  barycentric identity), randomized rank-sum checks over GF(2), the chord formula over all 24
  orders x 4 gaps, and an exact rational-arithmetic simulation of the axis drawing for
  2 <= m,n <= 7 (count = d_m d_n, no adjacent crossings, at most one crossing per pair, no triple
  concurrence). One implementation bug found and fixed during testing (the simulation's first
  counter ignored the anti-diagonal matching); the mathematical formulas were unaffected.

## Isolation / housekeeping disclosures
- Only this root was written. No git operations, no shared indexes, no nested agents, no
  publication/browser UI.
- The harness wrote terminal logs outside the root (/tmp/droid-terminal-* or similar) in both
  segments; not authored packet content.
- python3 -B used throughout; no __pycache__ created.
- grep hit lists displayed file NAMES inside the excluded active rounds (e.g.
  fresh-arithmetic-discovery-r99/work/family-titles.txt appeared as a hit path); their contents
  were not opened.
