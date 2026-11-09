# Working notes — fresh-structural-discovery-r135

Start: 2026-10-20T17:24:43Z (notes/start-time.txt). Notes file created 2026-10-20 ~18:05Z (session resumed after context compaction; this file records work done so far from the prior session segment).

## Mandate recap
- Round r135, campaign 18/20. Writable root: frontier/campaigns/2026-10-14/fresh-structural-discovery-r135/ only.
- Pinned source: OpenAI math repo commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; preprints-tree.json SHA256 eeecc1da...09b (13223 entries).
- Deliverable: full author proof of one substantial full-scope theorem in a DISTINCT proof-feasible underexplored family, or honest PREFREEZE/no-nominee. Freeze exact scope BEFORE proof drafting. No self-gates, no count/priority claims, no nested agents, no git, no shared indexes.
- Must not enter active fresh-arithmetic-discovery-r99 or fresh-analytic-discovery-r133 workstreams.
- Lesson from r134 (per brief): Kang Zenodo23351325 Lemma 2.2 paid the counting operation; no grade-shopping of T184I134 or T106O133.

## Reads so far (source, authenticated)
Fetched via public/fetch_source.py (pinned raw GitHub URLs + Git blob SHA1 authentication against preprints-tree.json; receipts in private/source/receipts.json, all OK):
- preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/README.md
- build/paper.tex, references.bib
- sections/: introduction.tex, normalization.tex, intersections.tex, subspaces.tex, detector.tex, conclusion.tex
- figures (2 files)

Read in full except a few elided ranges (detailed in reading-limits.md at seal time):
- thm:main: cr(K_{m,n}) = d_m d_n with d_r = floor(r/2)*floor((r-1)/2)  [Zarankiewicz conjecture, full scope]
- lem:cycle-pairing: for any drawing, z^T J y = 0 over the 2-cycle space
- lem:additive: J^{ik} - J^{i1} - J^{1k} + J^{11} lies in the additive space
- lem:subspace: sum dim(U_i ∩ V_j) ≤ floor(m^2/4) * N
- cor:rank-sum: Σ_{i≠j} rank(X_i - Y_j) ≥ 2 d_m d
- lem:triangular-basis, lem:detector (Φ annihilates additive/diagonal blocks, rank-one per off-diagonal entry, invertible on S_≺)
- conclusion: odd-n lower bound via rank R_{ik} ≤ c_{ik}; even case by vertex deletion (Kleitman/Woodall parity argument); axis drawing gives upper bound.
- normalization lemma: polygonal drawings, no adjacent-edge crossings, standard.

## Primary antecedents read
- Yang–Wang 2021 (Graphs Combin. 37:1083–1088): HC for K_{1,m,n} follows from ZC → family branch K_{1,m,n} is now a routine composition (excluded).
- Yang–Lu–Chen–Yang, arXiv 2201.09465v1 (PDF in private/primary/, sha256 8e45ecb7...8d87; text extracted, 1028 lines; read lines 1–679):
  - (3) cr(K_{1,m,n}) = Z(m+1,n+1) − floor(m/2)floor(n/2)
  - (4) cr(K_{2,m,n}) = Z(m+2,n+2) − mn   [Harborth conjecture for K_{2,m,n}]
  - (5) cr(K_{1,1,m,n}) formula; Lemma 1 vertex-splitting; Theorems 1–2.
  - HC(K_{1,1,m,n}) follows from ZC for m,n both even, but for odd parities requires HC(K_{2,m,n}).
  - Known: (4) true for m=3 (Asano), m=4 (Ho), K_{2,2,n} (Klešč–Schrötter).
- Ho, "The Crossing Number of K_{2,4,n}", Ars Combin. 109 (private/primary/ho-k24n-ars109-40.pdf, sha256 0d51270b...b7ff; scanned, no text layer; read as image): method = case analysis on K_{2,4} drawings; not obviously generalizable.
- CHN survey copy kn-minus-edge-manuscript/work/chn-v5.txt lines 340–560: Table 1 known tripartite values; Ho 2004 K_{3,3,n} conditional on ZC; Ho 2008 Thm 2.7 cr(K_{1,2M,n}) conditional.

## History screening
- Project history searched (counts) for: Seymour, thin trees, Barnette, circulant Hadamard, fixed price, Euclidean Ramsey, Harborth, K_{2,m,n}, tripartite, multipartite, join product, Klešč. No operative project work on K_{2,m,n} found. Accepted findings R001–R040 reviewed; R027 occupies cr(K_n − e) (family 165 "closest" operation per r129 note).
- Families repeatedly screened in prior rounds (from brief + parent intakes r107–r134): 157,170,167,171,160,164,166,176,159,175,099,089,183,156(R029),165(R027), and r134 screened 181,189,190,118,192,162,248,185.
- proposals/combinatorics.md line 139: "Unconditional versions of conditional crossing-number results (165), e.g. join products, cr(K_{1,m,n})" listed as a gap. r129 excluded 165 only because R027 occupies the closest operation. With thm:main (full ZC) now in the pinned source, the unconditional conversion landscape changed.

## Candidate direction (NOT frozen)
Target: Harborth's conjecture for K_{2,m,n}: cr(K_{2,m,n}) = Z(m+2,n+2) − mn for ALL m,n.
- Sanity checks: K_{2,1,1}: Z(3,3)−1 = 0 ✓ (planar); K_{2,2,2}: 0 ✓ (octahedron); K_{2,2,3}: 2 ✓ matches known.
- Consequence: would also give HC for K_{1,1,m,n} all parities via Yang–Lu–Chen–Yang.
- Idea: adapt source algebraic machinery (cycle pairing, additive blocks, detector Φ, subspace lemma) or splitting constructions to the extra 2-vertex class.

## Open item before freeze — resolved
- arXiv 2610.25204 inspected (abstract): flag-algebra bound 0.96936·Z(m,n), predates pinned proof; no parity overlap.
- No post-2022 Harborth K_{2,m,n} progress found. Yang–Lu–Chen–Yang read in full.
- K_{2,m,n} direction developed to a quantified obstruction (m=n=4: subgraph bounds 12 vs target 20) and abandoned UNFROZEN; see packet/public/working-notes.md.

## Final state (sealed 2026-10-20)
Status FROZEN_AUTHOR_PROOF_NOMINEE. Frozen 2026-10-20T18:22:29Z.
Frozen statement SHA-256 1000a115e013b3bc28247fdc03f33b8d4ae3ee8ee2a41ce4da55c79e1081a99d.
Nominee: even-adjacent drawings of K_{m,n} have >= d_m d_n oddly crossing edge pairs, exact via
the balanced-axis drawing; ocr±(K_{m,n}) = ocr+(K_{m,n}) = pcr+(K_{m,n}) = d_m d_n = cr(K_{m,n})
(last equality quoting pinned thm:main). Proof: packet/public/proof.md (characteristic-2 transport
of the pinned machinery: one-sided shift + diagonal bookkeeping, infinite char-2 field,
row-flip detector).
sanity.py: checks (a)-(h) all pass. verify.py baseline: ARTIFACTS_VERIFIED (11 source bodies,
3 primary receipts, 28 payload files). artifact-controls.json: 9/9 copied-control cases behave as
expected, copied inputs unchanged, originals re-verified unchanged after controls.
Anchors: FINAL.json 9e01e0dbcdab7665d6ce58c904291cb3caeaef9e54f5befb023336abe21f6be6;
packet/MANIFEST.json 6b997e3d8605220fc4845528d8213356c792e7d674eab50d7be9d16d4730eae5;
REPORT.md 4ecc09d4de9fe7e2f5e095b7b0ac2215a6665438898378e6ee8c91de6b0e037e (REPORT.sha256).
Authoritative consolidated notes: packet/public/working-notes.md; read limits:
packet/public/reading-limits.md.
