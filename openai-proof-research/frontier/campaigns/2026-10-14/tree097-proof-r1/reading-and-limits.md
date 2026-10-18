# Actual reading, search and proof limits

## Read in full

- Brief: tree097-parent/proof-review-r1-brief.txt.
- AGENTS.md; sources/upstream.json (pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).
- Author packet: original-scope.txt, candidate.md, prefix-law.md,
  assembly-author-support.md, history-and-comparison.md,
  reading-and-limits.md, author-assistance.json, README.md, checkpoint.md,
  report.md, preliminary-dp-screen.md, primary-receipts.json,
  checks/validation-note.md, verify.py.
- Source097 (pinned bodies from the author's private copy, identity
  recomputed): build/assembly.tex (1-278), build/brownian.tex (1-139),
  build/introduction.tex (1-206).

## Read in part (exact extents of the pdftotext -layout texts)

- dadush-et-al2019: 150-319 (results, Thm 1.2, subgaussian definition,
  Lemma 1.3, proof idea); 598-612 (convex body = closed, nonempty interior,
  not necessarily bounded); 915-923 (Thm 3.4 statement); 940-1084 (minimax
  theorem and complete proof of Thm 3.4 parts 1 and 2). Lemma 2.3 (Laplace
  to subgaussian) and Lemma 3.2 were not reread; they are inside the cited
  published theorem.
- bansal-et-al2021fullv1: 160-175 (prefix(G) definition), 470-499
  (Definition 2.4, Lemma 2.5), 880-984 (Lemma 4.1, Remark 4.2, full proof of
  Lemma 4.1). bansal-et-al2022 (ITCS): 1026-1037 (Lemma 21 statement,
  identical contract).
- kulkarni-reis-rothvoss2023v1: 85-129 (Thms 1, 2, Cor 3), 640-709
  (Thm 19 statement and cloning proof, start of Section 6).
- online-steinitz2026v1, dutta-jha-jiang2026v1, aden-ali2026v1: first 60
  lines each plus keyword search for tree/leaf/heavy terms and theorem
  labels. No statement about vertex-labeled rooted-tree signing with a
  leaf-count bound was found at this extent. These three are comparators
  only; nothing in the proof depends on them.

## Not read

- source097 signing.tex, matrix.tex, survival.tex, consequences.tex, main.tex,
  README, bibliography (except the Royen2014 entry). These contain the
  proofs of the stipulated inputs; per the brief, upstream truth is not
  audited.
- The 157/184 preliminary-screen sources and dvorak-yepremyan2023v1: not
  relevant to TREE097.
- The analytic worker's separate packet tree-signing-assembly-r1: not
  opened; its copied note inside the frozen packet was read as author-side
  material only.
- The contribution-review brief and any contribution verdict: not used.

## Searches

No web search was performed by this reviewer. No priority, novelty or
literature-completeness inference is made. Contribution and eligibility are
outside this gate.

## Proof limits

- Pinned source097 statements are stipulated true. DGLN Thm 1.2/3.4 and
  Bansal et al. Lemma 4.1 are used as published primary theorems at their
  actual stated hypotheses, which were checked; their internal proofs were
  read (the operative directions) but not audited for upstream correctness.
- No Lean or other formal verification was performed.
- The finite diagnostic in checks/ checks identities on finite samples and
  is not proof evidence for the universal theorem.

## Provenance of third-party bodies

No third-party body is copied into this review directory. All source and
primary bodies were read from the frozen author packet's ignored private/
directory after identity checks (provenance.json). Seven primaries were
re-downloaded to /var/tmp/tree097-proof-r1-dl (outside the repository) only
to confirm byte identity; nothing was uploaded.
