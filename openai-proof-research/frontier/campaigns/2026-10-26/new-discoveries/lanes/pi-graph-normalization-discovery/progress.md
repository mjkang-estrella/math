# progress.md — investigation log

Lane: NEW/lanes/pi-graph-normalization-discovery. Solo, standard speed, no children, no
git/ledger/shared edits. NEW = frontier/campaigns/2026-10-26/new-discoveries.

1. Read openai-proof-research/AGENTS.md and NEW/ledger.json (15 accepted, 15/30; exclusions and
   counting standard noted; delegation policy: Pi/GLM5.3 Flash only, none started).

2. Read parent snapshot NEW/lanes/parent-fresh-screen/sources/349070-live.json: record open, all
   solution/comment arrays empty. Re-fetched live from mathdb.com API (same uuid) into my lane:
   `sources/349070-live.json` — identical status, 0 activity.

3. Fetched and read the actual primary source: arXiv:2012.07764v1 PDF (sha256 eaf52a1e…ae2a0),
   author **Laurent Guigues**, title "Concerning Iterative Graph Normalization and Maximum
   Weight Independent Sets", single version, 14 Dec 2020. Read: abstract, Conjectures 1.1/1.2,
   Definition 2.1 (N(x) = x ⊘ (A+I)x), Section 5 (Taco/hypersurface Theorem 5.1, tree
   injectivity Theorem 5.2, fixed points = complete clusters, Bx = 1 equation (8)), Section 8.1
   (Conjecture 8.1 Eq. 19, conditional Theorem 8.1 and its Eq. (27) proof in Appendix A lines
   ~3560–3596), Section 8.2 (Rayleigh/fixed point view).

4. **Verified the parent's provisional identity** — first by hand (two-line symmetrization), then
   an initial numeric mis-check of my own was caught and corrected (I had mis-evaluated
   (1/z_i−1/z_j)²; after correction identity matched to 0), then exact `Fraction` verification on
   300 random symmetric nonnegative B (max diff exactly 0) and 200 exact checks of the
   conjecture on random connected graphs (`verify_checks.py`, `independent-checks.json`).

5. Derived the consequence: source Theorem 8.1 becomes unconditional; ‖x^k‖₁ increasing and ≤ n.

6. Searched MathDB neighbors via /api/search: found **349068** (general convergence, open, 0
   activity) and **349069** (activated IGN → MIS, open, 0 activity). Snapshotted both
   (`sources/349068-live.json`, `sources/349069-live.json`).

7. Literature screen (web): found the **author's own successor preprint arXiv:2605.05330v1
   (6 May 2026)** "Graph Normalization: Fast Binarizing Dynamics for Differentiable MWIS".
   Downloaded (sha256 e998ecdd…525a) and read: Definitions 1–4, Theorems 1–6, Appendices A–F
   proofs. Key determinations:
   - Definition 2 = exact 2020 GN map; WRGN with γ=1, v=1 = exact IGN.
   - Theorem 2 (App. E): global convergence of iterated WRGN for all γ > 0, v > 0 ⇒ covers the
     source's general convergence conjecture (MathDB 349068). Mechanism: exact MM step
     (Theorem 1, App. B/C) on semi-algebraic energy ½yᵗ(I+γA)y − vᵗy; vanishing steps;
     Proposition 1 (App. D) no accumulation on non-normalizable points; Corollary 1 accumulation
     points are fixed points; Attouch–Bolte–Svaiter KL Theorem 2.9 (H1–H3 verified).
   - Lemma 1 (App. F) = the weighted form of the parent's identity; confirmed algebraically
     identical term-by-term (x_i = y_i d_i substitution).
   - Theorem 3 = unconditional weighted mass growth (the 2020 conditional Theorem 8.1).
   - The 2026 paper does **not** cite the 2020 preprint; Semantic Scholar shows only one citing
     work of 2012.07764 (unrelated IWPT 2021). No third-party resolution exists.

8. Independent numerical campaign (`screen_convergence.py`, then a focused re-check):
   200 random connected graphs (n = 3…16), 4 log-uniform starts each, 12 000 iterations:
   - Conjecture 8.1 never violated; energy ½xᵗ(A+I)x − 1ᵗx never increased (worst +1.8e-15 float
     noise) — consistent with 2026 Theorem 1.
   - All projective directions stabilized < 1e-5 drift except one n = 10 case (dev 0.15):
     investigated — a slow transient on a fractional plateau (direction ≈ equal weights on an
     independent 4-set) that snapped at k ≈ 8500 exactly onto the binary fixed point
     (0,0,0,0,1,0,1,1,1,1) — a maximal independent set — and stayed exact through k = 200 000.
     Not a counterexample; consistent with the 2026 convergence theorem and with its remark that
     non-isolated fractional fixed-point manifolds cause long plateaus.
   - No non-convergent orbit found; none claimed.

9. Considered pivoting to 349069: read its exact statement and the 2020 paper's activation
   framework (Definitions 2.3/2.4, attractivity Theorems). Rejected as a counting target: the
   existential "suitable non-linear activation" is scope-ambiguous under the counting standard,
   the 2026 successor deliberately bypassed the activated map in favor of the modified WRGN map,
   and a full resolution is a major open problem, not achievable honestly in this lane. Recorded
   as an open neighbor in PROOF.md §7 / discovery.md.

10. Wrote deliverables: PROOF.md (full identity proof + credit-0 documentation), discovery.md
    (screening outcome), provenance.json (sources + SHA256), verify_checks.py,
    independent-checks.json, screen_convergence.py, sources/* (both papers' PDF+txt, three live
    MathDB records). No ledger edit, no staging, no commits.

Open obligations stated honestly: none of the credit-0 conclusions depends on my proof being
priority; the convergence credit-0 rests on a posted claimed-full proof whose Proposition 1 block
argument I would myself rewrite; if the parent voids it, the question reopens with my screening
as the only new artifact (no counterexample, no proof).
