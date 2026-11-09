# Reading limits — fresh-structural-discovery-r135

Honest record of what was actually read, acquired, skipped, and where searches stopped.
Round date 2026-10-20. "Prior segment" = the session segment before a context-compaction
(~17:24–18:00Z); its reads are recorded from its durable notes/summary.

## Pinned source (stipulated true; not audited)
Repo openai/math at commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; tree metadata
sources/preprints-tree.json SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b
(13223 entries). Retrieval: packet/public/fetch.py (pinned raw.githubusercontent.com URLs, Git
blob SHA-1 + size authentication). Receipts: packet/private/source/receipts.json (11 files, all
authenticated). Bodies: packet/private/source/ (flattened file names; receipt records map them to
repository paths).

preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026:
- README.md, build/paper.tex, build/references.bib: read in full (prior segment).
- build/sections/introduction.tex: read in full twice (prior segment; this segment), including the
  explicit sentence separating crossing points, crossing pairs, and parity-based counts.
- build/sections/subspaces.tex, intersections.tex, detector.tex, conclusion.tex: read in full
  (prior segment; re-read in full this segment from the authenticated bodies).
- build/sections/normalization.tex: read in the prior segment; main lemma statement and
  construction steps read; some appendix polishing paragraphs not re-read this segment. The proof
  here (proof.md Lemma 1) does not quote it; it is self-contained.
- build/figures/*.tex (2 files): read (prior segment).
No other preprint bodies were fetched for the nominee. Companion check: the preprint has no
companion in the tree with overlapping parity content (searched the tree listing for crossing
titles; only the complete-graphs companion exists, whose scope is K_n, not read in body).

## Primary literature (bodies in packet/private/primary; receipts with SHA-256 there)
- Yang, Lu, Chen, Yang, arXiv:2201.09465v1 (PDF sha256 8e45ecb7…): text extraction 1028 lines;
  lines 1–679 read (abstract, introduction, formulas (3)–(5), Lemma 1, Theorems 1–2 and their
  proofs for even parities). Lines 680–1028 NOT read (the K_{2,m,n} direction was abandoned
  prefreeze; recorded as a known skip, not a gap in the frozen theorem's support — the frozen
  proof does not cite this paper).
- P. T. Ho, The crossing number of K_{2,4,n}, Ars Combinatoria 109 (PDF sha256 0d51270b…):
  scanned, no text layer; read as page images in the prior segment (method: case analysis on
  K_{2,4} drawings). Acquisition URL not recoverable in the current session log; body
  authenticated by recorded SHA-256. Not cited by the frozen proof.
- M. Schaefer, The Graph Crossing Number and its Variants: A Survey, Electron. J. Combin. DS21
  (2017 version PDF sha256 a03758b9…): read selectively, not cover to cover: the iocr entry in
  full (text lines ~2505–2545), odd-crossing variants incl. semisimple/weakly semisimple
  definitions (lines ~3138–3172, 3219–3228), Hanani–Tutte and crossing-lemma-variant passages
  (lines ~160–215), monotone-variant table excerpt (1393–1400), bipartite-related index hits
  (grep "bipartite", 40 hits scanned). Used for terminology and for the comparison
  cr(G) <= 2 iocr(G)^2 quoted in proof.md Section 11.
- Yang–Wang 2021 (Graphs Combin. 37:1083–1088): abstract and statement read via publisher page
  (Springer link, prior segment); body not read (paywalled); used only to exclude the K_{1,m,n}
  branch of the prefreeze direction search. Not cited by the frozen proof.
- Balogh et al., arXiv:2610.25204v1 (2026-10-18): abstract page read in full this segment
  (flag-algebra asymptotics; explicitly predates the pinned proof). Body not read (not needed).

## Web searches (result snippets only; no other bodies fetched)
This segment: "odd crossing number complete bipartite graph Zarankiewicz iocr(K_{m,n})";
"pair-crossing number of complete bipartite graphs pcr(K_{m,n}) Zarankiewicz"; '"odd crossing
number" "complete bipartite" K_{m,n} exact value conjecture'; "Schaefer survey crossing number
variants odd crossing number K_{m,n} Zarankiewicz open problem"; 'arXiv 2026 "odd crossing" OR
"pair crossing" Zarankiewicz OpenAI proof bipartite corollary'; '"odd crossing number"
Zarankiewicz conjecture bipartite open problem Pach Tóth parity'. Prior segment: Harborth /
K_{2,m,n} / K_{1,1,m,n} / Asano / Klešč queries (exact strings not fully recoverable).
Search limit disclosure: negative results ("no exact parity determination found") reflect these
queries as of 2026-10-20 and are not a worldwide-priority audit; the report states novelty as
"not found in the literature checked", with the pinned preprint itself dating to 2026-09-23.

## Project history (searched, not read in full)
- Accepted findings frontier/findings/R001–R040 skimmed in the prior segment; grep "crossing"
  over frontier/findings (this segment) hits only R027 (ordinary crossing number of K_n − e) and
  unrelated uses of the word. R027 finding body read in the prior segment.
- Grep (this segment, file-path mode) for "odd crossing|iocr|pair-crossing|crossing parity|
  Hanani|weakly semisimple" across the repo: hits reviewed by path; only t027o-manuscript-v1
  (R027 lineage) was content-grepped — no parity content. No prior project work on odd/pair
  crossing numbers found.
- Grep for "The-crossing-number-of-complete-bipartite-graphs": hits are tree-listing copies and
  hash lists; the only operative use found is r134's screening hash lists (t184i134 scratch
  .sha256 files list paths; no body engagement). No prior contribution uses this preprint.
- Grep "Zarankiewicz|brick factory|brickyard": hits are CONTENTS.md snapshots and family-title
  lists (incl. family 165 title "The Harary–Hill and Zarankiewicz crossing-number formulas"), plus
  the kn-minus-edge lineage's paragraph comparing Sadhu's cr(K_{m,n} − e) claim
  (kn-minus-edge-manuscript*/main.tex line 495, read) — a different operation (edge deletion,
  ordinary crossing number), not overlapping the frozen parity statement.
- proposals/combinatorics.md line ~139 (prior segment): the family-165 gap note
  ("unconditional versions of conditional crossing-number results (165), e.g. join products,
  cr(K_{1,m,n})").
- r134 artifacts read: discovery-structural-r134-parent/disposition.md,
  contribution-r1-adoption/adoption.json, t184i134-contribution-r1/packet/public/review.md and
  reading-limits.md (prior segment, as directed by the brief); r134 FINAL.json,
  artifact-controls.json, REPORT.md, packet/public/verify.py (this segment, as seal templates).
- NEW-TEN-2026-10-14.md acceptance rules: lines 1–80 (prior segment).
- Structural parent intakes r107–r134 scanned for screened families (prior segment).
- Hidden/ignored/JSON/large files: greps above were run without size cutoff over the repository,
  which covers JSON/inspection artifacts (e.g. t027o inspection text was among content-grepped
  trees); history searches were by alias families ("odd crossing", "iocr", "pcr", "pair crossing",
  "Hanani", "parity", "Zarankiewicz", "Harborth", "tripartite", "multipartite", "join product",
  "Klešč", "K_{2,m,n}").
- Deliberate exclusions: active rounds fresh-arithmetic-discovery-r99 and
  fresh-analytic-discovery-r133 were not entered or read; their file names appeared in grep hit
  lists (disclosed in working-notes.md). sources/tree.json ignored per AGENTS.md (truncated cache).

## Timing
- Start 2026-10-20T17:24:43Z. Direction search and source/primary reads: prior segment to ~18:00Z.
- Parity-direction feasibility, literature/history checks: ~18:00–18:20Z.
- Frozen 2026-10-20T18:22:29Z (SHA-256 1000a115…; notes/frozen-sha256.txt). Late reads before
  freezing (disclosed prefreeze): arXiv 2610.25204 abstract, Schaefer survey excerpts, the history
  greps listed above, and the r134 seal templates (verify.py, FINAL.json, REPORT.md,
  artifact-controls.json) consulted for packaging format. After freezing: no further
  source/primary/history reads occurred; only packet authoring and mechanical checks.
