# Source contracts, reading extents and provenance

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. This package is
private research; retained third-party material keeps upstream rights.

The stipulated source repository is https://github.com/openai/math at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The complete source prefix is

    preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/

Its ten source files are copied under inputs/private/upstream/ with that
prefix. inputs/private/r8/retrievals.json records their exact pinned raw
URLs, upstream paths, Git SHA-1 blobs, SHA256 and byte sizes. This round
recomputed every Git blob as SHA1("blob "+byte_size+NUL+bytes) and compared
it against both that retrieval record and the complete pinned
inputs/private/context/sources/preprints-tree.json. The complete tree is
not the truncated root-tree cache. inputs/private/context/sources/upstream.json
records the pinned revision. Reading source statements is distinct from
authentication and from independent validation of upstream truth.

The project's AGENTS.md was read. The full frozen r8 report and its
source-contracts were read with the user-supplied brief; these are retained
under inputs/private/r8/. Its seal SHA256 is
`6db6112bf4297450c063652b5cc415d8a4f2d20b8b5138753349fcbafbfd3600`.
Both manifests, all 24 inputs and 19 outputs, and the exact 47-file inventory
including metadata authenticated before use. No frozen code was executed.
The copied r8 files are checked against their original manifest entries;
our verifier independently authenticates the original frozen tree too.
Historical accepted-result and catalogue screening from r8 is context,
not claimed as freshly repeated discovery or a new theorem premise.

## Pinned source reading in this round

Common local section path:

    inputs/private/upstream/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/build/sections/

Common primary URL prefix:
https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/

The source file hashes and sizes below are bound mechanically in the input
manifest and the copied original retrievals; they are not inferred from
titles. Exact relied-on interfaces and reading extents are:

- 01-introduction.tex: main statement and its explicit exclusion of elementary
  unimodality; main:theorem/main:witness; main:hessenberg statement and proof
  (lines 160--201), including its last sentence excluding a preferred or
  cup-product-compatible isomorphism. Introduction/history/proof structure
  were inspected in the displayed first-310-line read, whose combined tool
  output was partly truncated; no full reading claim for that entire window.
- 02-graphs.tex: entire 245-line section. graph:digits and reversal,
  graph:form/graph:torus, graph:commutation, graph:kernel/graph:coefficient,
  graph:reciprocity. The proofs fix all weight and elementary conventions.
- 03-reordering.tex: lines 1--155 and 627--812. alg:reordering; shuffle quotient
  and shifted degrees; alg:pbw, alg:strings and output-parameter explanation.
  The intervening separated-center/coproduct construction was keyword-scanned,
  not fully read. Only the stated pinned theorem and the explicit [D,T]=1
  infinite-string contract are used; there is no independent audit of PBW.
- 04-walls.tex: completion, sign factorization and incoming equations through
  wall:incoming-prescription and its uniqueness proof; wall:unit/binomial;
  wall:factors statement/positivity contract; wall:recursion and its full proof;
  wall:positivity, wall:product, all displayed across reads of lines 1--430.
  Lines 90--158 were separately re-read for the rational bar argument.
  Change-of-chart theorem statement and portions of its support/comparison
  proof were inspected in the displayed 430--710 window; that combined output
  was partly truncated and no complete mutation-proof reading is claimed.
  No mutation compatibility is promoted to coefficient Lefschetz preservation.
- 05-triangle.tex: lines 1--200 (chart, phases, embedding and rotation
  comparison), and 470--640 (end of linear-section proof, tri:domination,
  tri:monomial and tri:positivity with proofs). Stationarity/pure-label middle
  proofs are accepted via the pinned interface, not independently checked.
- 06-witness.tex: entire section through route:witness and its proof, as
  displayed in the full section read. In particular route:finite,
  route:switch, route:history-recursion/history-series, route:return,
  route:parity, route:exact and route:witness. The energy-independent history
  choices and independent jump decorations are essential in candidate §3.
- 07-completion.tex: all 42 lines; reversal of the final witness and scope.
- README.md, build/paper.tex, build/references.bib: retained and blob-verified;
  no full reading or additional mathematical reliance is claimed.

All new deductions in candidate §§3--5 are this round's arguments, not
attributed to an upstream theorem under a stronger interpretation.

## Primary literature

1. Shareshian--Wachs, *Chromatic quasisymmetric functions*, Advances in
   Mathematics 295 (2016), 497--551.
   https://doi.org/10.1016/j.aim.2015.12.018 ;
   https://arxiv.org/abs/1405.4629 .
   The r8 privately retained TeX and gzip source were copied after authenticating
   their original inventory. Source URL was https://arxiv.org/src/1405.4629
   (unversioned retrieval; frozen bytes). In this round read local TeX lines
   315--370, 748--780, 1478--1548, 1560--1635: introquasistan/quasistan
   (= published Conjecture 5.1), uniconsprop and proof, recent-developments
   correction to the older representation conjecture, Appendix B tooluni,
   paldef/tooluni2. No full-paper reading is claimed. Current pinned positivity
   supersedes the older conjectural positivity status.

2. Davison--Mandel, *Strong positivity for quantum theta bases of quantum
   cluster algebras*, Inventiones mathematicae 226 (2021), 725--843.
   https://doi.org/10.1007/s00222-021-01061-1 ;
   https://arxiv.org/abs/1910.12915 .
   Retained publisher HTML and its TeX-bearing text extraction copied from r8.
   In this round read extraction lines 1635--1690 and 1810--1865: Theorem 2.15
   and bar-invariance proof, Conjecture 2.17, Theorem 2.18 and actual incoming
   matrix hypothesis, Lemmas 3.4--3.5 and proof. No new generic-theta or
   pre-Lefschetz-to-Lefschetz theorem is assumed. The normalized rational bar
   proof here is compared to this existing symmetry operation.

3. Ben Davison, *Positivity for quantum cluster algebras*, Annals of
   Mathematics 187 (2018), 157--219.
   https://doi.org/10.4007/annals.2018.187.1.3 ;
   https://arxiv.org/abs/1601.07918 .
   Primary source retrieved from https://arxiv.org/src/1601.07918 on 2026-10-16,
   with archive bytes and extracted clusterpositivity3.tex retained privately.
   Read Section 2.1, local lines 306--412: mutation, compatible pair,
   LambdaMult, compatibility, mutFram, LaurentExp, LefDef, mainThm
   (= published Theorem 2.4). Introduction was inspected, not the entire
   mixed-Hodge-module proof. This established theorem is used only to define
   the exact prospective interface; its missing realization is explicit.
   It permits arbitrary compatible skew-symmetric seeds but requires a
   cluster monomial. The rank-two non-monomial argument in candidate §5 is
   elementary and self-contained, using this mutation definition.

4. Abreu--Nigro, *Chromatic symmetric functions from the modular law*,
   Journal of Combinatorial Theory, Series A 180 (2021), 105407.
   https://doi.org/10.1016/j.jcta.2021.105407 ;
   https://arxiv.org/abs/2006.00657 .
   Primary source retrieved from https://arxiv.org/src/2006.00657 on 2026-10-16;
   archive and extracted Algoritmo3.tex retained. Read lines 450--475,
   588--620, 990--1025, 1310--1360: def:modular, prop:relations,
   centered normalization discussion, prop:csfunimodal and proof. Algorithm
   locations were scanned. Used for bounded operation comparison only: the
   abelian hypothesis, network numerator/denominator cancellation and common
   centers are essential; no all-graph positive network theorem is assumed.

literature-retrievals.json records fresh archive URLs/hashes/sizes;
source-reading.json gives each retained primary text's SHA256 and size.
The newer sources were obtained to test a real proof route, not to certify
novelty. Searches covered general cluster-monomial Lefschetz versus theta
Lefschetz and modular-law unimodality. Search-result snippets and secondary
webpages were discovery aids only. No third-party code or TeX was executed.

## Contribution and rights limits

The complete target is already a credited conjecture. Live-support
bookkeeping, rational bar symmetry and the rank-two elementary recurrence
are technical supporting deductions. Nothing is nominated under a new
name. No global mutation obstruction, actual Hessenberg counterexample,
full-U finite-to-infinite inference, or independent PASS is asserted.
All private third-party files retain original copyright/license terms.
Original prose CC BY 4.0 and code MIT apply only to this round's authored
material, not the copied r8 package or its upstream sources.
