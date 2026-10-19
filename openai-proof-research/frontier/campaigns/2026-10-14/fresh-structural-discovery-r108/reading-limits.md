# Reading, provenance, and limits

The pinned revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
`context-receipts.json` binds the rules, upstream pointer, catalogue, complete
tree, intake ledger and all18 accepted finding records to their accessed
bytes. All13,223 tree entries were parsed and indexed; `truncated` is false.
The ignored truncated `tree.json` was not used. Byte access is distinguished
from semantic reading below.

## Context and history

AGENTS.md and upstream.json were read completely. The complete catalogue was
parsed for all family headings and manuscript paths, with selective semantic
reading of discrete/combinatorial headings and abstracts. No complete reading
of its638,727 bytes of prose is claimed. The intake ledger's first200 lines
and selected recent tail were read; one combined tail display was truncated.
The current R040 acceptance and supplied r107/r71 intake were retained.
All R023–R040 finding bodies were read; R025 and R036–R040 were reread in a
separate untruncated call to eliminate earlier combined-output uncertainty.
Reading acceptance records does not mean rereading every linked manuscript.

Content-search outputs in `history-games.txt` and `history-other-screens.txt`
were read. Additional actual historical passages include I29's active-normal
entropy proof, I22's initial screens, I113's game comparison and G113 proof,
I116 lines117–151 (including its exact extraction audit), r35's scheduling
report/checkpoint, r44's full preliminary DP screen, r75's exclusion note,
r33's checkpoint, r52's README, r54's reading limits, and I17 lines1–155
(especially its complete phase-energy variance obstruction). Broader
combined displays were sometimes truncated; those displays are not counted
as complete semantic reads. No whole-history completeness claim is made.

## Pinned mathematical sources

`source-receipts.json` records52 successful private TeX retrievals. For each
it gives the exact pinned raw URL, full path in the complete tree, Git blob,
SHA256, byte count and actual inclusive reading spans. Git blob identities
were checked using the Git blob header, not by comparing filenames. The
`labels_present_in_body` field is an automated navigation inventory, not a
claim that every listed label was semantically read.

For the target, the complete substantive bodies of both main inputs were
read: all four sections (`introduction`, `discount`, `labeling`, `application`)
of the stochastic manuscript, and all five substantive sections plus history
of the deterministic parity manuscript. This includes the actual statements
and full operative proofs of S `thm:discount`, `thm:labeling`, the application
box shrink, and P `lem:mp-prefix`, `lem:combine`, `thm:determinacy`,
`lem:extract`, `thm:labels`, and the cost proof.

The deterministic ordinary-game companion's entire introduction and §7
(`cor:full-solution`, `cor:randomized-full-solution` with proofs) were read in
the final companion cross-check. The randomized companion's entire
introduction and independent comparison appendix were read. The remaining
ordinary deterministic and randomized recursion sections were retrieved but
not freshly read in full here. Their statements do not supply stochastic
parity, and none of their unread internal lemmas is a new premise of this
packet. Thus this is a precise operative-interface companion comparison,
**not** a claim to have read every body of every family104 companion. A full
candidate would still require any additionally relevant companion reading.

The other four families were rejected screens. Their exact per-file spans
are in the receipts; whole-manuscript/whole-companion completeness is not
claimed for them. Main files, figures, and boilerplate retrieved for inventory
were not automatically counted as proof reading.

## Primary literature

`primary-receipts.json` binds PDF bytes and extracted-text bytes separately.
The PDF skill was used for read-only primary-paper extraction. No authored
PDF, layout review, formal proof or release build was undertaken.

* Chatterjee–Doyen–Gimbert–Oualhadj, *Perfect-Information Stochastic
  Mean-Payoff Parity Games*, conference author PDF: definitions/preliminaries
  and extracted lines290–680, including the full even-priority Lemma2 proof,
  odd-priority statement and algorithm discussion. Full-report production
  PDF: lines1–55 and620–858, including the complete odd Lemma3 proof,
  Algorithm1 and Theorem1 cost argument. The definition was checked:
  limsup average and maximum recurring priority. The full Section5
  positional-Min proof was not read and is not used as a supplied theorem
  for the liminf target. The playground-host report retrieval failed HTTP403;
  the production-host report succeeded. Both attempts are recorded.
* Dantam–Mayr, *Mean-Payoff-Parity and Lifting Strategies from MDPs to
  2-Player Stochastic Games*, arXiv2606.19324v1: extracted lines1–50 and
  430–595; complete Theorem3/proof and Theorem5 statement/outline. The full
  AppendixB.1 proof was not read. Its strict-positive threshold is a material
  scope difference, not permission to use it at zero.

Search hits and abstracts served as navigation. No unread primary body is
used for a new proof or priority clearance. The source's credits to Bouyer
et al., Parys and earlier potential/martingale work are retained as source
ancestry; this packet does not claim freshly reading all those originals.

## Integrity versus mathematics

Private upstream/primary copies stay under `private/`, excluded by the local
.gitignore. They are local evidence, not original work for redistribution.
Root Markdown/Python files are authored research/support; history-search
transcripts are project-context evidence. The manifest classifies them.

The verifier requires a caller-supplied detached manifest hash. It reads
files, checks exact membership, rejects links, validates hashes and pinned
blob identities against the complete external tree, and reports drift of
mutable historical context. It downloads, executes and writes nothing.
These checks authenticate a particular unresolved packet. They do not prove
T104AS, independently review its support lemmas, or award acceptance credit.
