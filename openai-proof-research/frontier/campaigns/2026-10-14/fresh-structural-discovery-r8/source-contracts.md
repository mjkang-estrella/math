# Source contracts and reading extents

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. This is a private
research package. Downloaded third-party text retains upstream rights.

## Immutable source and project context

Repository: https://github.com/openai/math . Revision:
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The local research rules, upstream descriptor, catalogue, complete
13,223-entry untruncated preprint tree, campaign ledger, twenty-findings
ledger and R023–R026 records are copied under inputs/private/context/.
The rules and campaign acceptance requirements were read, the catalogue
was screened by result headings/selected descriptions, and accepted-result
statements and historical vetoes were inspected. This is not a claim to
have read every catalogue abstract, every old finding proof or all prior
research. The complete preprint tree was machine-scanned, not human-read
entry by entry. No sibling research package or checker is a dependency.

The entire selected preprint subtree was enumerated. There is one
mathematical TeX body, split into seven sections. All ten text/source files
were retrieved and their Git blob SHA-1 recomputed against the complete
tree, before theorem reliance. Exact pinned raw URLs, SHA256, Git blob IDs
and sizes for every file are in retrievals.json; input inventory hashes
also bind every copy. Retrieval is not a claim of full reading.

Common retained prefix:

    inputs/private/upstream/preprints/
    Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/

Common primary URL prefix:

https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/

## Exact pinned reading

- build/sections/01-introduction.tex: introduction/main theorem,
  `main:theorem`, equation `main:witness`, explicit exclusion of elementary
  unimodality, `main:hessenberg` statement and full proof, history and proof
  structure. Lines 1–309 read; remaining three lines are closing structural
  text, not a relied theorem interface. SHA256
  `10e0c45e1bb975155096768fd77d3d93da69bc4f9d28993d72da03363ed7e64a`.
- build/sections/02-graphs.tex: entire 245-line section read across the
  recorded calls. `graph:digits`, `graph:commutation`, `graph:kernel`,
  `graph:reciprocity`, definitions and their proofs. SHA256
  `0a90807bc64e1d2cfb402826297572f13856be07da344c53c95580b36a562008`.
- build/sections/03-reordering.tex: lines 1–150 and 786–885 read, including
  exact `alg:reordering`, elementary-unit conventions, shuffle/quotient
  setup, primitive-output parameter formula and finiteness bounds.
  Interior PBW/coproduct/primitive proofs were not fully read or used as
  independent new lemmas. Lines 886–889 not relied on. SHA256
  `3d488b3ebcb5623850edd423273776db5159d13481b2e36e959ffd3525511d7e`.
- build/sections/04-walls.tex: lines 1–530 read: completion, incoming wall
  prescription, positive wall-factor statement/proof, incoming section
  coordinates, `wall:recursion` and full proof, `wall:positivity` and full
  proof, positive products, mutation setup and first support bounds.
  The later mutation proof was not read in full, and no coefficient
  preservation under mutation is relied on. SHA256
  `065bcb5c55b336ad0f795993d90c8c7540a4426e5573dd5fe84be8491e73c647`.
- build/sections/05-triangle.tex: lines 1–140 and 430–640 read, including
  exact phases, chart root cone, `tri:embedding` and proof, rotation setup,
  end of linear-section proof, `tri:domination`, `tri:monomial` and
  `tri:positivity`, with their displayed proofs. Stationarity and pure-label
  proofs in the unread middle are stipulated through the theorem; this
  report does not independently certify them. SHA256
  `9e9cfeb7bf0d28a8efd88657a9baa6e3fc91e0162470a640255ca58b962754cb`.
- build/sections/06-witness.tex: lines 146–279 and 431–625 read, including
  packet switch/full proof, required-mask construction, exact-mask
  matching/full proof, individual rule and witness proof through line 625.
  The finite-history middle section was not fully read. No implementation
  of the upstream witness is claimed. SHA256
  `8ef0cd77af2b084746f2be648cb4b92459c6d9b4061c49302c92ccd11feac9c8`.
- build/sections/07-completion.tex: all 42 lines read. Full final theorem
  proof and computational-scope remark. SHA256
  `a556493f222b42dc1e27b77ba47c9845af69cbd4c0a35e83f66992a585ab1cf8`.
- README.md, build/paper.tex and references.bib were retained and
  authenticated, but no full reading is claimed. They introduce no new
  theorem dependency.

All source hypotheses used in candidate.md are the exact h/G class, the
specified forward-gap roots and phase order, the finite cone-interval
coefficient recursion, and the normalized target identity. Theorems are
accepted under the user's instruction, with new deductions checked here.

## Primary antecedents

John Shareshian and Michelle L. Wachs, *Chromatic quasisymmetric functions*,
Advances in Mathematics 295 (2016), 497–551.
https://doi.org/10.1016/j.aim.2015.12.018 ;
https://arxiv.org/abs/1405.4629 .

The successful exact source retrieval is https://arxiv.org/src/1405.4629
(retrieved 2026-10-16; URL unversioned, bytes frozen). Gzip input SHA256
`5269db17869563c762878d6b25cf3c9afec859751e9e96945d214b0bee46178f`;
decompressed TeX SHA256
`a63c2509caff04566bb515f0c984635438ae0fe53537445534594a3f9d7ad0bd`.
Both are retained under inputs/private/literature/. No TeX was executed.
Read local lines 300–370, 748–775, 785–825, 1478–1548 and 1560–1635.
Interfaces: `introquasistan` and `quasistan` (published Conjecture 5.1),
`uniconsprop` (equivariant Lefschetz yields Schur-unimodality),
`tympermcon` (degreewise Young permutation modules), recent developments
crediting Brosnan–Chow/Guay-Paquet, and Appendix B definitions/positive
unimodal sum/product operation. The published web-rendered conjecture and
geometry discussion were also inspected. No full reading of this paper is
claimed. Its older conjectural status for the representation identity is
not substituted for the newer pinned theorem.

Ben Davison and Travis Mandel, *Strong positivity for quantum theta bases
of quantum cluster algebras*, Inventiones mathematicae 226 (2021), 725–843.
Primary full publisher text:
https://link.springer.com/article/10.1007/s00222-021-01061-1 ;
https://arxiv.org/abs/1910.12915 .

Retained publisher HTML SHA256
`3e3f1bf1c2764a8ce4df762b095b740f5dc7912b91bc44d0411288f81d330965`;
text extraction SHA256
`aea3470a8e394c06564144b32bea5823487fc852f8a1ad32a99fd6560b819934`.
The extraction retains displayed TeX from publisher HTML. Read the exact
definitions of centered/pre-Lefschetz polynomials in §2.1.1, Theorem 2.13
and uniqueness explanation, elementary adjoint normalization (23),
Theorem 2.15 and proof, Conjecture 2.17, Theorem 2.18 and its stated
dependency, Lemma 3.5 and complete proof, Proposition 3.12,
Conjecture 3.13, Theorem 3.14, the final acyclic portion of Proposition 7.7
and associated spanning/quotient discussion. Broken-line definition and
Proposition 3.1 were inspected to distinguish conventions. Detailed DT
proofs in Sections 6–7 were not read in full. No general Lefschetz
conjecture or identification with the pinned incoming basis is assumed.
The local extraction line windows include 1068–1090, 1645–1688,
1816–1855, 1950–1976; the primary web reader supplied the larger exact
statement/proof windows identified above.

Discovery-only searches also inspected primary abstracts for Cho–Huh
(https://doi.org/10.1137/18M1216201) and Abreu–Nigro
(https://arxiv.org/abs/2006.00657), which concern explicit special-family
expansions. They are not theorem premises here and no full-proof reading
is claimed. Retrieval failures and alternate transports are recorded in
retrieval-failures.txt. No secondary aggregator is a mathematical premise.

## Bounded contribution comparison

The search topics were chromatic elementary coefficient shapes,
Lefschetz/theta positivity, acyclic versus cyclic hypotheses, and
Hessenberg permutation decompositions. This was a bounded screen, not
an exhaustive bibliography or novelty certificate. The target is a known
conjecture, explicitly credited. The older operations do pay centered
sum/product closure and acyclic Lefschetz jumps; the pinned source pays
shape-specific positive sections. The unproved operation is their full
Lefschetz upgrade on the actual cyclic forward-gap charts. The proved
diagnostics are technical and are not nominated under a different name.

Private source bytes are not release artifacts. Original prose/code
licenses do not apply to them. Every source and derivation is included in
the immutable input/output inventories, with SHA256 and byte size.
