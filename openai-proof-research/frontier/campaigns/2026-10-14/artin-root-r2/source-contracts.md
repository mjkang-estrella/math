# Source contracts, reading and provenance

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
Third-party inputs remain private with their original rights.

## Stipulated upstream

Repository: https://github.com/openai/math
Revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Complete preprints subtree: `df0564b2deaab87e07854b6344d8c2f037682e77`.
The nontruncated `sources/preprints-tree.json`, not `sources/tree.json`,
controls Git identities. `pinned-blobs.json` gives exact immutable raw
URLs, upstream paths, Git blob SHA1, SHA256, size and external local path
for all 78 r11 retrievals. They were all authenticated. That is not a
claim to have semantically read all 78 texts this round.

The final proof depends on only these two upstream interfaces:

* `preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/build/sections/01_intro.tex`,
  `cor:arbitrary-intersections`, with its proof in
  `build/sections/08_stabilizers.tex`. Read the introductory definitions,
  main theorem, arbitrary-intersection corollary and surrounding initial
  interfaces (lines 1–130); in the stabilizer section read lines 1–230,
  including the inside-parabolic/rank descent and the complete
  arbitrary-intersection proof. The exact implication used is existence
  of a smallest parabolic PC({g^m}), not a geometric statement.
* `preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/build/sections/introduction.tex`,
  initial definitions and `thm:main` (lines 1–105), and
  `build/sections/consequences.tex`, complete text including
  `cor:artin-structural` (i) and its proof. Used only for torsion-freeness
  of every finite-rank A. The upstream proof is accepted by stipulation;
  no audit of its general asphericity proof is claimed.

Fresh exploratory readings, not extra premises for the normalizer proof:

* Parabolic `02_category.tex`, entire section: finite label/algebra
  construction, Frobenius duality, twists, action and relative-family
  properties, with proofs. In particular `cat:action` and `cat:family`
  justify the cone computations, endomorphisms and frame test in the
  research notes. `03_layers.tex` lines 1–220: minimality, levels,
  `lay:structure`, adjacent layers, bottom composition and extremal
  test interface. `04_caps_twopoint.tex` lines 1–170: caps,
  accessibility, candidate definition, two-point statement and start of
  hull interface. The later full two-point proof was not freshly read.
* Parabolic `05_null.tex`: `null:hom`, `null:injection`,
  `null:separation`, and their proofs, and the subsequent null-obstruction
  proof. The same-transport hypothesis and actual Hom filtration were
  inspected directly. `06_heights.tex`: spherical sublevel definitions,
  height comparisons, connected minima and stabilizer containment;
  the whole displayed final `ht:minima`/`ht:containment` proofs were
  read. No extension to orbit sums is assumed.
* K(pi,1) companion `height-data.tex` and `rigidity.tex` lines 1–180,
  `global.tex` lines 1–220, `topology.tex` lines 180–310: frame counts,
  same-transport Hom input, global harmonic filtration and the precise
  Salvetti–coset comparison. These do not provide a relative normalizer
  quotient classifying space or an assumed CAT(0) metric.

The CAT(0) companion's r11 reading/provenance remains authenticated;
its proof bodies were not freshly read or used here. Its geometric
action obstruction is not generalized to every Deligne metric.

## New primary retraction input

François Digne, Eddy Godelle, Jean Michel, *Retraction to a parabolic
subgroup and applications*, arXiv:2407.07459v2, 11 September 2024.

* Versioned HTML: https://arxiv.org/html/2407.07459v2
* Versioned source: https://arxiv.org/src/2407.07459v2
* Retained files: `inputs/private/dgm-retraction-2407.07459v2.html`, its
  text extraction, source archive `dgm-2407.07459v2-source.tar`, and the
  extracted original `dgm-source-0.tex` (`retract_soumission.tex` in
  the archive). Archive URL, size, SHA256 and exact TeX membership are
  in `dgm-source-provenance.json`; the input manifest binds every copy.

Actual reading: introduction's definitions and retraction product
interfaces; HTML Definitions 1.2 and 1.14, Proposition 2.4,
Proposition 2.6, Lemma 2.7, Definition 2.8 and Lemma 2.9, including
displayed proofs; original TeX lines 550–596 (Proposition 1.11 and its
root-word calculation), 610–678 (ribbon definition and Proposition
1.16 proof), and 795–913 (descent, Proposition 2.6, Lemma 2.7 and
Lemma 2.9 with proofs). TeX labels are `bien defini`, `fourre-tout`,
`ft6`, `ft2`, `ft3`, `mult2`, `Icoset`, `pi(bb')`, `ribbon`.
The TeX introduction lines 1–150 and the later minimal-parabolic/
conjecture discussion lines 1940–2010 were also read. No full reading
of all double-coset or conjugacy proofs is claimed.

Contract: rho_I is a set retraction. For theta(a) in N_W(W_I),
rho_I(a b)=rho_I(a) alpha_a(rho_I(b)), where alpha_a is the automorphism
from the minimal Coxeter ribbon representative. Arbitrary type and
arbitrary signs are allowed. This exact law, not a general group
retraction and not Artin ribbon generation, is used to prove that its
zero fiber inside N_A(A_I) is a subgroup. The candidate pays that new
subgroup/isomorphism deduction explicitly.

## Other primary reading and its limits

* Garnier–Heng–Licata–Yacobi, *Normalisers of parabolic subgroups of
  Artin–Tits groups and Tits cone intersections*,
  https://ogarnier.github.io/pub/norm_artin_tits_cone.pdf.
  Read the authenticated r11 text extraction pages 1–4 and the normalizer
  setup/Lemma 2.8; checked the currently served primary PDF introduction
  through the browser text tool. Exact old private PDF/text bytes are
  bound by the r11 tree; no claim that the mutable URL pins a version.
  Theorem 1.8 is spherical ambient; Conjecture 1.10 generalizes that
  specific arrangement/classifying-space identification. The current
  proof establishes neither that identification nor finite CW type for
  the quotient. Atomic Matsumoto 1.4 is separate. No full later proof
  audit occurred.
* Heng–Licata–Yacobi, *Periodic elements in finite type Artin–Tits groups
  and stability conditions*, https://arxiv.org/html/2502.20711v1.
  Retained HTML/text are in `inputs/private`; exact retrieval hashes are
  in `literature-retrievals.json` and the input manifest. Read Theorem
  1.1, its introduction/roadmap, the Lemma 2.6 full-twist shift interface
  and Theorem 2.7 covering interface. This is finite type and central-
  power periodicity, not general relative framed-object fixation. It is
  screened context, not a dependency. The first publisher HTML fetch
  failed with an inaccessible redirect; the versioned arXiv text was used.
* CMV large-type Proposition 37/Lemma 38/Corollary 39 and HMS
  Definition 5.9/Theorem 5.10 remain as exactly documented in the r11
  source contracts. This round re-read those contracts and their report
  in full, not the complete articles or Godelle's original proof. The
  source bytes and reading provenance are authenticated externally.
  No statement from them is needed for the normalizer proof.

The HTML-to-text extraction used a standard-library HTML parser and
retained the original mathematical alttext. It did not execute webpage
scripts. A preliminary attempted import of unavailable BeautifulSoup
failed before creating extraction output; no mathematics rests on it.

## Mandatory continuity and ownership

Read in full: applicable repository AGENTS.md; supplied complete current
brief, including its reproduced original r11 brief/report and parent
responses; r11 `original-scope.md`, `candidate.md`, `source-contracts.md`,
`literature-screen.md`, `research-notes.md`; parent `r11-disposition.json`
and `r11-verification.json`; the mandatory historical brief (119315
characters, SHA256 `97f5b23fcd79fa6abc3850e6efdd3e001530665e26e9811fc5a4e61dcef9fb57`);
structural r10 and relative-CI-r2 candidates, both C dispositions; current
campaign ledger; specified F corrections/disposition and G proof/
contribution dispositions. The initially truncated tool windows were
followed by targeted reads of the omitted C/ledger passages. Historical
directory reservations are superseded, and all vetoes remain in force.

`external-inputs.json` gives exact read-only external references, including
the whole 115-file r11 tree and the 91-file r10 and 34-file C-r2 trees.
It avoids copying 100KB of historical prose. Twenty fixed external files
are separately bound, including the original historical brief and parent
records. Authentication of all inventories and all 78 Git blobs preceded
any reliance on archived code; no archived code was executed at all.

The project HEAD recorded in `authentication.json` is a workspace identity,
not the upstream mathematical pin. Only `git rev-parse HEAD` was used;
no staging, commits or intentional index writes occurred. All new writes
are in the assigned r2 directory. No nested agents or external messages
were used. Parent integration and independent gates remain separate.
