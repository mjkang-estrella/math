# Source contracts, actual reading, rights and identifiers

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Third-party material under inputs/private retains its original rights, is
private research input and is not offered for release.

## Immutable catalogue and source identities

Upstream: openai/math, fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
The nontruncated preprints subtree is df0564b2deaab87e07854b6344d8c2f037682e77.
All 13,223 entries were parsed; 749 manuscript directories and 10,373 blob
positions were inspected as an inventory. All numbered CONTENTS headings
were surveyed, with selected summary slices retained. This is NOT semantic
reading of every paper. sources/tree.json was never used for inventory.

source-records.json gives the exact pinned raw URLs, Git blob SHA1,
SHA256, size and private local path for EVERY retrieved text blob. Every
blob was checked against the complete catalogue and its Git framing
before storage. Retrieved bodies not listed below are authenticated bytes,
not claimed readings. The mathematical contracts assume the stipulated
source truth and do not audit it.

## Family 204: selected mathematical input

One mathematical manuscript directory was identified by the full-tree
companion search: Tensor-Saturation-for-Even-Spin-Groups-September-24-2026.
Its lower operations must retain the following boundaries:

- 01-introduction.tex: read completely, especially thm:main, triple
  root-lattice scope including spin weights and all ranks n>=2.
- 02-real-schedules.tex: read decoded character positions [0,24500).
  This includes def:schedule, real:signs, real:balance,
  prop:basic-schedule STATEMENT, lem:coefficient and its proof,
  lem:flag-composition and proof, lem:invariant-moment and proof,
  lem:schedule-moment and proof, strict approximation and initial
  decreasing-path construction. The later area/basis proof was not read
  completely. The basic-schedule theorem is stipulated input, not an
  inference from reading only its statement.
- 03-lattice-continuation.tex: read in full. thm:integral-schedule needs
  all three integral root-pairing labels and root congruence, and in type
  D the moving weight has at most one zero coordinate. Read the signed
  graph exceptional case, half-kernel bounds, local-link conditions and
  full continuation proof. It is a ONE-shape theorem.
- 04-moment-knots.tex: read decoded character positions [0,9500).
  Includes prop:strict-count statement, profile-rigidity statement/proof,
  and the orbit dimension/norm argument through its joint-kernel discussion.
  The rest of the strictness/knot-count proof was not read. No omitted
  argument is claimed to have been generalized to four factors.
- 05-columns.tex: read [0,9000) and the final 7000 decoded characters.
  This includes prop:columns, col:folding and proof, minuscule columns,
  common-wall functional setup, and the concluding coefficient/Cartan
  composition proof. The small intervening gap was not relied upon.
  A column list sums to ONE moving highest weight; it is not an arbitrary
  tensor factor list.
- 06-zero-tail-completion.tex: read the final 9500 decoded characters,
  including the zero-tail construction's ending, the COMPLETE final proof
  of thm:main and tail:fractional remark. Earlier preprojective and filtered
  intersection proofs were not freshly read or generalized. The complete
  triple theorem is stipulated.
- references.bib: relevant source locators (Sam, Hong--Shen,
  Berenstein--Sjamaar, KM, Kiers, Littelmann, FH) read. No claim of full
  bibliography verification or auditing those proofs.

## Screen-only source families

177 Bounded-degree-coboundary-expanders-in-every-dimension: introduction,
construction and expansion sections read completely. They state F2
coefficients, the q-group congruence tower, distance to cocycles, separate
vanishing and weight comparison. Geometry/homology bodies were retrieved
but not read. No coefficient extension theorem is claimed.

314 Cyclic-Length-and-Chromatic-Fixed-Point-Loss: introduction [0,5700)
read, including thm:main and the established abelian/extraspecial comparison.
Other proof bodies were retrieved only. No cyclic-length theorem or
poly-Zp consequence is pursued.

313 Finite-generation-for-the-Kn-local-sphere: complete introduction and
01-history.tex [0,4500) read. Its main theorem is for localizations of
FINITE spectra; it explicitly excludes arbitrary semilinear free modules.
Other retrieved sections were not read. The all-dualizable possibility
was rejected against Li's actual counterexample criterion before freezing.

## Primary literature actually read

Original PDFs and pdftotext -layout representations are retained privately.
literature-records.json gives their retrieval URLs and original byte hashes.
Versioned arXiv URLs fix versions; unversioned author PDF bytes are fixed
by their recorded SHA256, with no invented publication-version identity.

- Sam, https://arxiv.org/pdf/1009.3040v2 : title/abstract and introduction
  through its end (first 14000 extracted characters), including Theorem
  1.1, Corollary 1.2 WITH PROOF, arbitrary-factor scope, factor-one contrast,
  and symmetric-quiver/Pfaffian method overview. No full quiver proof read.
- Hong--Shen, https://arxiv.org/pdf/1404.4098v2 : extracted text lines
  1--175, introduction through the tropical/Satake-method overview,
  including Theorems 1.1/1.2, Corollary 1.3 and its proof. Later folding
  proof not read; no claim to extend it to the Q4 junction.
- Berenstein--Sjamaar, https://pages.uoregon.edu/arkadiy/bs.pdf : extracted
  lines 730--840, complete Theorems 3.2.1--3.2.5 and the exact branching/
  moment interpretation preceding them. The two equivalent descriptions
  supply rational moment/occurrence, not an integral point theorem. No
  fresh complete proof audit; it is an established primary interface.
- Kapovich--Millson, https://arxiv.org/pdf/math/0508186v1 : first 14000
  extracted characters, introduction with Theorems 1.1--1.3 and Conjecture
  1.4, and initial path conventions. No polygon-extension theorem claimed.
  Attempted v2 returned HTTP 404 and is not treated as a read source.
- Kiers, https://arxiv.org/pdf/1804.09229v3 : first 14000 extracted
  characters plus focused extracted lines 44--100; Definitions 1.1,
  Conjecture 1.2, Theorem 1.3 and Section 2.1 tensor-cone interface.
  No finite-rank calculation or full proof audited.
- Li, https://arxiv.org/pdf/2110.08397v1 : first 14000 extracted characters,
  especially introduction/Theorem 4.22 criterion and Theorem 1.4 as a
  SCREEN against all-dualizable finite generation. The underlying original
  Hovey--Strickland proof was not read. This counterexample is established
  antecedent, not an r12 result.

## Historical reading and limits

Read applicable AGENTS.md; no additional applicable ancestor/nested rule
file was found. Read the owned ledger snapshot and complete mandatory
119315-character brief in windows, including the U/H/T2/B/EPnI/FK/CI and
other scope objections. Read full r8, structural-r10 and relative-CI-r2
candidates, specified C/F/G parent dispositions, and supplied full Artin
r11/r2/review history. Also read actual r11 original scope, contracts,
literature screen and notes. The Artin proof/contribution verdict is
history, not an r12 mathematical dependency or new audit.

I104 report Section 1/S104 and I226 selection Section were read after
project-local searches. Their all-arity triangulation screen is expressly
credited; these reports were snapshotted, not bound to future mutable
parents. They are not sources proving Q4's novelty. No historical program
was executed. No claim is made to have reread every cited historical
primary body, reauthenticated every older full package, or performed an
Artin proof review. No old theorem is reused as a new mathematical premise.

Hashes authenticate retained bytes, not semantic reading, truth or novelty.
All final dependencies are owned inputs. The final verifier does not bind
the future live ledger or mutable parent directories.
