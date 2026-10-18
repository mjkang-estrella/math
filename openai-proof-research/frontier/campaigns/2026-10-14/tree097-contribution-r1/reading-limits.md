# Actual reading, search and proof limits

Original prose CC BY 4.0. All line numbers refer to the author packet's
pdftotext -layout texts, which have the recomputed SHA256 values in
provenance.json. This review copied no third-party body. All primary and
source bodies were read in place, read-only, in the author packet's ignored
private/ directory.

## Campaign and author packet (read in full)

* AGENTS.md, sources/upstream.json and the frontier/NEW-TEN-2026-10-14.md
  standards: the acceptance section was read in full. Verdict history was
  read through the visible part, with a grep of all SUBSTANTIAL/TECHNICAL
  dispositions through line 990.
* r44: original-scope.txt, candidate.md, prefix-law.md,
  history-and-comparison.md, reading-and-limits.md, author-assistance.json,
  report.md, checkpoint.md, README.md, verify.py, primary-receipts.json,
  preliminary-dp-screen.md and assembly-author-support.md, all in full.
  The checks/ scripts and results, history-index-pointers.json and
  history097-pointers.json were listed but not read. They are author
  diagnostics and pointers, not contribution evidence.
* r4 candidate.md lines 1–60 (target T2) and a grep for "tree" in r4 and
  two-order r2. Neither has a tree statement.
* The parallel review tree097-proof-r1 was NOT opened. It was excluded from
  every search.

## Pinned source 097 (stipulated true, not audited)

* introduction.tex: read in full (thm:signing, historical context including
  Banaszczyk 2012's O(sqrt d + sqrt log N) and Bansal et al. Conj. 6.3).
* assembly.tex: read in full (prop:adaptive, prop:filtered, lem:slab-energy,
  and the full proof of thm:signing).
* brownian.tex: read in full (lem:brownian-rate,
  lem:gaussian-path-correlation, and the proof of lem:slab-energy).
* references.bib and README.md: read in full.
* A grep of all 097 TeX files for tree/subgaussian/Banaszczyk/Gaussian
  measure found no tree statement.
* NOT read in this review: matrix.tex, survival.tex (grep only),
  signing.tex, consequences.tex (grep only) and main.tex. These hold the
  proofs of the stipulated analytic propositions, which are inputs and not
  contribution claims.
* Catalogue: sources/CONTENTS.md entry 097 (grep). The 749 top-level
  preprint directory names from the complete preprints-tree.json were
  screened by keyword. The only related manuscript is 097 itself.

## Primary bodies (pinned bytes in the author packet)

1. Bansal–Jiang–Meka–Singla–Sinha 2111.07049v1 (full): lines 24–45
   (abstract/contents), 157–260, 361–425 (tree/DAG overview and lower-bound
   idea), 860–984 (Thm 1.5 statement, Lemma 4.1 statement and full proof,
   Thm 1.4 proof), 1115–1139 (Thm 1.5 proof) and 1274–1333 (open problems
   6.1–6.4). The rest is unread.
2. Bansal et al. ITCS 2022: lines 1020–1150, grep only, to confirm Lemma 21
   and Thm 5 (the tree lower bound) are in the author extent.
3. Kulkarni–Reis–Rothvoss 2308.01406v1: lines 1–260 (Thms 1–7, overview of
   cloning) and 420–749 (Thm 15 with full proof, Prop. 16, Lemma 17/18 and
   Thm 19 with full proof and remarks on Nikolov/Meka, plus the start of
   Thm 20). The proof of Prop. 16 was read; the online implementation was
   only partly read.
4. Dadush–Garg–Lovett–Nikolov ToC 2019: lines 150–309 (Thm 1.2 exact
   statement, Lemma 1.3, and the minimax proof idea). The detailed Section 3
   minimax proof (around lines 953–1078) was NOT reread here. Only its
   stated direction is used for classification.
5. Russo–Wei 2610.16715v1: lines 1–369 (introduction, related work,
   Algorithm 1, signer definition (2.2), Thm 2.1 with (2.4)). The proofs of
   Lemmas 2.2/2.3 and section 4 are unread.
6. Aden-Ali 2607.04388v1: lines 60–140 (Thms 1–2 statements and the triplet
   mechanism), plus a grep for tree. The algorithm and proofs are unread.
7. Dutta–Jha–Jiang 2604.13355v1: lines 1–60 (abstract/contents), plus a grep
   for tree. The tree there is a data structure over intervals. The body is
   unread.
8. Dvorak–Yepremyan: not read (irrelevant to TREE097; it belongs to the
   unnominated DP screen).

## External lead (not a dependency)

* Bandeira, "A simplification of the solution to the Komlós Conjecture",
  Randomstrasse 101, retrieved 2026-10-17 through the reviewer's web-fetch
  tool and read in full. The bytes were not retained, so this is a lead
  only. It documents the energy class used in place of Banaszczyk's
  Gaussian-measure class. It does not state the Gaussian-body energy bound
  (operation C). The verdict does not depend on it.
* Guo–Fang–Lu 2609.11189 and Akbas–Sra 2609.27172 were not read. They are
  known only through the source 097 introduction.

## Searches (2026-10-17, bounded)

Web queries:
1. "prefix discrepancy rooted trees number of leaves bound sqrt(d log L)
   vector balancing"
2. "tree discrepancy root-to-vertex paths Euclidean signing heavy path
   decomposition subgaussian"
3. "Steinitz-Bergström theorem consequences trees subgaussian distribution
   prefix sqrt(d) 2026 arXiv"
4. "\"prefix discrepancy\" trees \"leaves\" Banaszczyk Steinitz 2026"
5. "subgaussian coloring distribution supported on colorings with small
   prefix discrepancy Dadush Garg Lovett Nikolov restricted set application"

The hits were the Bansal et al. versions, KRR, DGLN, Russo–Wei, an unrelated
subtree-discrepancy note (2412.04170, which concerns subtree sums with sphere
labels and a different problem) and generic heavy-light pages. None states a
leaf-count tree bound or a hard-supported subgaussian prefix law. Search
summaries are leads only.

Local search: rg over frontier/ for leaf-sensitive/heavy-light/tree-signing
phrases, excluding private/, r44, tree-signing-assembly-r1 and the parallel
proof review. Hits were only the two TREE097 briefs, tasks.json and one
parent-verification pointer.

## Limits

* No complete literature review and no worldwide priority or non-priority
  inference. A prior leaf-sensitive estimate could exist in unread sources,
  for example the Banaszczyk 2012 paper (not read here), Nikolov's
  unpublished manuscript, or Bansal–Nikolov's monograph manuscript cited by
  Russo–Wei.
* Proof correctness was assumed for classification. The hand checks listed
  in report.md are incidental, not a proof gate.
* No Lean, numerical or finite diagnostic was used as evidence.
