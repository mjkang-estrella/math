# T164F99 contribution r1: reading limits, versions, search record

All timestamps UTC 2026-10-20. Reviewer: Factory Droid / claude-opus-5-5 / high.
Raw search responses are retained in `packet/private/search/`; acquired primary
bodies in `packet/private/primary/`; pinned source bodies in
`packet/private/source/`; history and context copies in `packet/private/history/`
and `packet/private/context/`; immutable author packet copies in
`packet/private/author/`.

## Role/context inputs (read in full)

- AGENTS.md; expanded-target-2026-10-17/research-brief-2026-10-20.txt;
  discovery-arithmetic-r99-parent/contribution-r1-brief.txt (copies retained,
  hashes in `inputs.json`).
- Parent assessment.md / intake.json read as artifact intake only.

## Author packet (read in full; immutable, hash-verified)

scope-freeze.md (original and sealed copy byte-identical), proof.md, report.md,
prefreeze-feasibility.md, reading-limits.md, screens.md. Author FINAL/MANIFEST/
REPORT detached hashes re-verified against the role-brief anchors:
FINAL 8bdd4b88...5ab54f; MANIFEST 21ce5d12...d711e; REPORT bdb418b2...9f065;
scope 2a39e2a3...5a23b7; proof 14d9cd60...75847. All matched.

## Primaries (reviewer-acquired copies; author copies byte-identical where overlapping)

- Alweiss, arXiv:2307.08901v6 (latest listed version; v1-v6 shown on abs page).
  PDF re-downloaded; SHA-256 identical to the author's copy
  (e70f61d1...ec127a). pdftotext -layout, 851 lines; read in full including
  Sections 1-6 and references.
- Bergelson-Leibman, arXiv:math/9907201v1 (only version). SHA-256 identical to
  author copy (8a4cf4ff...ca13ba). 2069 lines; Sections 7.9-7.15 and 8.7-8.8
  read in full; abstract/introduction skimmed; Sections 1-6 (PHJ proof) not
  read. Corollary 7.11 used as stated (stipulated-true posture not required;
  it is public literature).
- Hunter, arXiv:2308.10749v1 (only version). SHA-256 identical to author copy.
  Introduction with Remark 1.1 read; Lemma 6.1 sketch region (lines ~680-730)
  read; remaining sections keyword-searched only.
- Bowen-Sabok, arXiv:2210.12290v1 (only version). SHA-256 identical to author
  copy. Introduction (incl. Corollary 1.2 statement), Claim 4.1 region
  (Moreira "any field" remark), Section 4.3 (compactness proof) and Section 5
  head read; Sections 2-3 not read.
- Alweiss, arXiv:2211.00766; served file is v4 (Discrete Analysis 2024:5).
  SHA-256 identical to author copy. Introduction and Section 4 (including
  Lemma 4.5, characteristic-0 integral domains) read; proofs elsewhere not read.
- Kousek, arXiv:2407.03304v1 (only version on arXiv). SHA-256 identical to
  author copy. Abstract and Section 1.1 read; finite-field Sections 4-5
  keyword-searched and Theorem 1.15 statement region skimmed. The journal
  version (ETDS 46(2), 2026, Cambridge) was located by search but its body was
  not obtained.
- Moreira, arXiv:1605.01469v1 (Annals 185, 2017). Reviewer-acquired
  (1e9e5a78...2628db). Section 1.2 (Theorem 1.4, Corollary 1.5, Example 1.6)
  and Section 7 (LID definition, Theorem 7.2, Lemma 7.4, Theorem 7.5 and its
  "only new ingredient" sentence) read in full; Sections 2-6 not read.
- Bergelson-Moreira, arXiv:1307.6242v3 and arXiv:1509.07574v1.
  Reviewer-acquired. Abstracts and introductions read; bodies not read.

## Pinned source (pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb)

Family 164 `preprints/Monochromatic-finite-sums-and-products-in-the-positive-
integers-September-23-2026/`: README.md, build/main.tex, build/references.tex
and all of build/sections/01-08 fetched from raw.githubusercontent at the pin;
every blob hash verified against sources/preprints-tree.json (13223 entries,
truncated false, tree SHA-256 eeecc1da...5e09b verified). Read:
01_introduction.tex in full; 02_framework.tex lines ~225-330 (finite sums form,
lem:chain-selection, deduction) in full; 08_alignment.tex lines 1-250 (finite
plan, compensating rescalings, cylinder-set compactness paragraph,
lem:finite-word-plan and proof) in full; 03-07 keyword-searched only
(field/characteristic/Alweiss/Bergelson), not read linearly. No other family
bodies read; the campaign catalogue was used for navigation only.

## History (copies retained in packet/private/history/)

Read in full: fresh-structural-discovery-r35/mixed164.md (unresolved integer
read-once question; paid machinery; not a frozen proved candidate);
fresh-arithmetic-discovery-r94/packet/public/other-screens.md;
fresh-structural-discovery-r130/packet/public/other-screens.md and the
positive-characteristic sentence of its report.md; the family-164 item of
fresh-arithmetic-discovery-r1/candidate.md (prescreen only).
Operative alias search: ripgrep -uuu over the repository (hidden/ignored/JSON/
large files included, no size cutoff) for {alweiss, hindman, finite sums and
products, FS..FP, sums and products}, then intersected with
{characteristic, infinite field, function field, F_2(t), positive char,
Bergelson-Leibman, Hales-Jewett}; all authored hits outside copied corpora were
followed (r1, r35, r94, r95, r130, r131 history copies, parent intakes;
remaining hits were Mathlib module-name strings, catalogue/title inventories, or
copied corpora).
Deliberate exclusions, disclosed: ACTIVE roots fresh-analytic-discovery-r133/
and fresh-structural-discovery-r135/ (not entered, not read), this review root,
.git/, copied corpora and environments (frontier/sources/, sources/,
**/private/ third-party bodies except the specific history copies above,
**/inputs/context copies, **/.lake/, **/.venv/, venv site-packages, release zip
binaries). No prior root was mutated.

## Searches (bounded; raw responses in packet/private/search/)

- Reviewer WebSearch x2 (this review): "monochromatic finite sums and products
  positive characteristic field Hindman conjecture Alweiss"; "Hindman
  conjecture sums and products characteristic p / positive characteristic
  partition regular fields arXiv"; plus two follow-up queries on all-fields
  extensions and F_q(t). No prior characteristic-p FS union FP statement found.
- arXiv API (export.arxiv.org): 8 query batches (Hindman+sums+products;
  monochromatic+products+field; "partition regular"+characteristic; Alweiss;
  monochromatic+sums+products; "finite sums and products"; Moreira/Bergelson
  author-title queries; id-list fetch for 2605.24751, 2303.00100, 2212.13100,
  2210.07831, 2110.08052, 1804.05341, 2607.24594, 2510.01301). Closest hits
  inspected: Goswami 2212.13100 (n=2-type, Q, ultrafilters),
  Hindman-Ivan-Leader 2210.07831 (negative infinitary results over Q),
  Ackelsberg-Bergelson 2303.00100 (finite-field density/equations),
  Byszewski-Krawczyk 1804.05341 (linear Rado over rings), Debnath-Goswami
  2110.08052 (IP* weak rings), Griffin 2605.24751 (infinite configurations in
  N), Chakraborty-Goswami-Patra 2510.01301 (random subsets of N). None overlaps
  the frozen statement.
- OpenAlex: 3 title searches (cited-by counts: Alweiss 2307.08901 -> 0;
  Hunter 2308.10749 -> 0; Bowen-Sabok -> 4).
- Semantic Scholar citation API for 2307.08901 (1 citing paper: Hunter),
  2308.10749 and 2210.12290 (both rate-limited, HTTP 429; not retried further).
- Author's six web queries (external-navigation.json) were noted, not re-run.

## Not obtained / not done

Bergelson-Leibman-McCutcheon (J. Anal. Math. 2005) body; Green-Sanders body;
Cilleruelo/Shkredov/Richter bodies; Kousek journal version; MathSciNet and
ZBMath (no access); no exhaustive or worldwide-priority search; no correctness
re-derivation as a gate (this review is conditional on correctness); no
downstream formal/manuscript/release work.
