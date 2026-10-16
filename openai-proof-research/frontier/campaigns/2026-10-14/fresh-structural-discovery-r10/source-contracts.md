# Source contracts and reading boundaries

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
Retained third-party materials remain private under their original rights.

## Immutable upstream

Repository: https://github.com/openai/math

Revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
The copied sources/upstream.json identifies this revision. The copied
sources/preprints-tree.json is the complete tree; sources/tree.json was
not used. inputs/upstream-pins.json gives each of 25 retained text blobs'
full immutable raw URL, path, Git blob SHA1, SHA256 and byte size.
source-readings.json adds exact read-line ranges and total line counts.
The final manifests authenticate these maps and all bytes. Retrieval,
hash verification, lexical search and semantic reading are distinct.

The source root is inputs/private/upstream/preprints/. Abbreviations:

* B = The-Artinian-Lex-Plus-Powers-Betti-Theorem-September-23-2026.
* D = Commuting-Division-Coefficient-Forms-and-the-Artinian-Eisenbud-Green-Harris-Conjecture-September-23-2026.

Read in full in B/build/sections/: 01-introduction.tex, 01-forms.tex,
02-filtered.tex, 03-monomial.tex, 06-tor.tex, 07-assembly.tex,
08-characteristic-zero.tex. Used labels: thm:main,
cor:characteristic-zero, thm:forms, filt:comparison/filt:initial,
mono:transfer, mono:bound, tor:deficit, tor:stable. In particular R in
06-tor.tex is explicitly a polynomial ring in earlier variables; its
Tor notation is not a theorem about an arbitrary CI base ring.

Read D/build/sections/01-introduction.tex lines 1--195, including the full
thm:construction, Artinian Hilbert-function theorem, characteristic-zero
corollary and initial strategy; read 09-consequences.tex in full, including
cor:local-cohomology and cor:quadratic-cayley-bacharach. These companion
corollaries were screened as already paid, not nominated. The deep
division-algebra construction proof was not re-read or audited. Other
retained source section bodies were lexically searched for Tor, relative,
Poincare, Shamash, Tate, quotient ring, local cohomology and consecutive;
they were not fully semantically read. Main wrappers, bibliographies,
figures and README blobs are authenticated retention, not a full-read
claim. Source theorem truth is stipulated throughout.

## Primary antecedents

inputs/literature-provenance.json gives original URLs, PDF hashes and
sizes; inputs-manifest.json also binds the extracted text bytes. All text
line numbers below mean LF-delimited physical extraction lines, including
form-feed page boundaries as characters within the line. No PDF page
layout/visual review is claimed or needed for these theorem interfaces.

1. Murai--Peeva, *Hilbert schemes and Betti numbers over
   Clements--Lindstrom rings*, Compositio Math. 148 (2012), 1337--1364.
   [Primary PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/7843F9C098A8425C10B52739B87CED88/S0010437X1100741Xa.pdf/hilbert-schemes-and-betti-numbers-over-clementslindstrom-rings.pdf).
   murai-peeva-2012.txt: read lines 25--150, 665--715 and 1500--1655.
   Read Theorems 1.3/1.5, relative Betti definitions, Lemmas
   4.6.1--4.6.4 and Theorem 4.6.5 with proof. The relative initial-pair
   theorem in Lemma 4.6.2 is credited there to Gasharov--Horwitz--Peeva
   (2008), Proposition 2.6. That earlier paper was not independently
   retrieved; its stated interface is used through MP, not claimed as an
   independently read proof. MP's long polarization/route construction
   earlier in Section 4 was not read in full or independently audited.
   Hypotheses in this retained version include algebraically closed
   characteristic-zero k; arbitrary characteristic-zero fields in a
   proposed C proof would be handled by field extension/descent.

2. Mermin--Murai, *The Lex-Plus-Powers Conjecture holds for pure powers*,
   Adv. Math. 226 (2011), 3511--3539.
   [Author PDF](https://math.okstate.edu/people/mermin/papers/the_lex_plus_powers_conjecture_holds_for_pure_powers.pdf).
   mermin-murai-2011.txt: read lines 1--130, 225--245, 1110--1135,
   1190--1225, 1260--1295. These include Theorems 3.1 and 8.1,
   Theorem 9.2 with its reduction paragraph, Conjecture 10.2 and the
   introductory operation discussion. Long shifting/compression proofs
   were not read in full. The paper is an ambient-S antecedent, not the
   arbitrary-R relative transfer. Historical open-problem language in
   this 2011 paper is not treated as current status after the stipulated
   pinned theorem.

3. Caviglia--Sammartano, *Syzygies in Hilbert schemes of complete
   intersections*, retained author version.
   [Author PDF](https://www.math.purdue.edu/~gcavigli/Articles-PDF/%5BS6%5D.pdf).
   caviglia-sammartano-syzygies.txt: read lines 945--1090, including
   Section 5, Conjecture 5.1, Lemma 5.2 and full Theorem 5.3 proof.
   The introductory statement was also read in primary web excerpts;
   no full paper read is claimed. Version-specific theorem numbering
   is 5.3 here (published-version metadata search snippets use other
   numbering). Its expansive-ideal/fixed-polynomial/pure-power scope
   is kept separate from C's entire-Hilbert-function/arbitrary-base scope.

4. Eisenbud--Peeva, *Minimal Free Resolutions over Complete Intersections*,
   retained author book draft.
   [Author PDF](https://pi.math.cornell.edu/~irena/papers/ci.pdf).
   eisenbud-peeva-ci.txt: read lines 1490--1565 and 1672--1758.
   Used Definition 3.4.1, Proposition 3.4.2 with displayed construction
   argument, Construction 4.1.3, Proposition 4.1.4 and Remark 4.1.5.
   The Tate/Shamash exactness theorem is credited, not reproved in full;
   the explicit wedge homotopies used in the finite checker are verified
   in candidate.md. No claim to read the entire book or Tate's original
   1957 paper is made.

Primary-site searches located these authors' documents; secondary snippets
were discovery aids only and are not mathematical evidence. Literature
screening is bounded. No all-literature novelty or priority certificate
is asserted.

## Continuity and project context

Read AGENTS.md and upstream.json; searched the full catalogue title list
and read selected family entries. Read current NEW-TEN-2026-10-14.md and
TWENTY-FINDINGS.md, with accepted-finding scope records R023--R026.
Frozen snapshots identify the consulted ledger state; later live edits
are not dependencies. The new analytic r9 output was not consulted.

Read full r8 and elementary-unimodality-r2 candidate reports, locally and
in the user-supplied continuity brief. Authenticated all 47/50 files of
those original packages to supplied external seals before using copied
content. No prior checker/verifier was run. Copied reports, scopes,
source contracts and manifests are in inputs/private/continuity/.
The read-only verifier also checks both original inventories offline.

Read full frontier/iterations/i226-new-algebraic-bridge.md after the exact
family search found it. Its deeper linked source/proof documents were not
read or executed in r10. Its ambient cancellation, scalar-degeneration
and Clifford findings are retained as prior technical lanes; no theorem
of this report depends on an unaudited detailed I226 proof.

## Rights

Original r10 prose: CC BY 4.0; original code: MIT. Author Myeongjin Kang,
no affiliation. These licenses do not relicense private third-party PDFs,
TeX, extracted text, or historical input snapshots. No distribution of
those inputs is authorized or performed here.
