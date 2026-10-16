# Source contracts and actual reading extents

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Third-party files
remain private under their original rights. Authentication is not semantic
reading or independent verification of a historical proof.

## Frozen continuity and stipulated source

The complete r13 candidate, radical/torsion-tower/proof-attempt checkpoints,
source-contracts.md, source-records.json, original-scope.md and the parent
r13-disposition.json were read. The last was snapshotted as
inputs/context/parent-response.json. Current AGENTS.md and the parent r2
brief were snapshotted. The supplied historical findings/responses in the
current assignment were also read. Older recursive histories were not
recopied or rerun. Their exclusions remain effective as reproduced in that
assignment; their historical work assignments are superseded.

The r13 seal was checked first, its two manifest hashes checked, and every
manifested payload checked. The entire verifier was then read and its
authenticated bytes executed. Its ACCEPT_INTEGRITY_ONLY result is retained
in r13-authentication-receipt.json. This is separate from reading mathematics.

The openai/math revision is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
sources/upstream.json was read. The complete 13223-entry preprints-tree.json
was parsed with truncated=false, including exhaustive filtering for both
selected manuscript paths. sources/CONTENTS.md was parsed completely (9142
lines, 638727 bytes), and its family 256 entry and the two selected manuscript
links were read semantically. This does not mean all manuscript abstracts or
all papers were studied. No truncated tree.json was used.

Actual pinned PDF/text interfaces reread this round:

* Nonsingular systems, extracted lines 1–170: full introduction, Theorem 1,
  historical comparison and full Theorem 2 statement. Lines 514–846: entire
  Proposition 4.1 setup/proof and Section 5 proof construction through Remark
  5.1. No fresh audit of the incidence or phase proof bodies in the omitted
  middle interval. Theorem 1's truth remains stipulated. Its conclusion is
  G↪U only; 4.1 pairs all variable slots and has coefficient-only boundary;
  5.1 already pays arbitrary independent families.
* Companion Kervaire paper, extracted lines 1–135: Theorem 1.1, Corollary 1.2
  and its proof, context and proof overview. No full proof audit. These
  interfaces concern unrestricted groups, with no torsion-free solution claim.

Git blob identities, sizes, SHA256 and immutable raw URLs for both PDFs are
in source-records.json. The bytes are referenced in the frozen r13 package,
not copied as redundant PDFs. They are rechecked against its complete pinned
catalogue. The two actual blob identities are
48694a86b0e54c20faa0dcd29686039740e5f674 and
b1363f19fb03b27e5615f3fe6d00f4b4555789f6, respectively.

## Newly recovered primary body

Brodsky–Howie, *The universal torsion-free image of a group*, Israel J. Math.
98 (1997), 209–228, DOI 10.1007/BF02937335. Publisher PDF retrieved by
urllib from https://link.springer.com/content/pdf/10.1007/BF02937335.pdf.
Read all 803 extracted lines, covering every printed page 209–228 and
references. Visually inspected rendered p. 210 to authenticate the hatted
image notation in Lemma 1.1/Theorems 1.2–1.4/Corollary 1.5. The complete
small-presentation and picture-application interfaces and operational limits
are in primary-operation-checkpoint.md. The paper's final small-case coset
enumeration claims are historical inputs read in context, not computations
independently reproduced here. No historical code was acquired or executed.

The electronic mirror timed out once in this round. The publisher web reader
returned Internal Error, whereas the independent publisher terminal download
succeeded with a PDF. One exploratory author-path URL returned 404. None of
those failed retrievals is used as a theorem source. No further mirror retries
were made after obtaining the full publisher copy.

## Additional mathematical interfaces actually read

Chiodo, arXiv:1107.1489v3, *A universal finitely presented torsion-free group*.
Read extracted lines 1–170, 165–350, 345–480, thus all text through the start
of the discussion following Theorem 4.10 (some overlap). In particular:

* 2.2: countably generated recursive presentations embed effectively into
  finite presentations with EXACTLY the same torsion orders. This theorem's
  cited underlying Higman proof was not independently audited.
* 3.9–3.10: iterative radical and universal torsion-free quotient; surrounding
  credited example and limitation of one-step removal.
* 3.12–3.14: effective enumeration and recursive universal torsion-free
  quotients, with proofs. The quotient's coefficient preservation is NOT a
  conclusion. The recursive construction is independently explained in our
  universal-coefficient checkpoint.
* 4.8–4.9 and their full displayed proofs: a single finitely presented
  torsion-free group containing all recursively presented torsion-free groups.
  Universal ordinary-subgroup embeddability for arbitrary ineffective groups
  is not asserted. The finite-diagram ultrapower argument is proved here.

Klyachko–Mikheenko–Roman'kov, arXiv:2303.13240v1, *Equations over solvable
groups*. Read extracted lines 1–285: introduction, examples, Section 2,
complete Proposition 2 proof, and split-extension setup of Section 3. Main
theorem requires an ALREADY Howie quasivariety. Proposition 2 says H_fin(Q)
=H(Q) is a quasivariety. We apply its actual closure operation to Q=TF,
not the Main theorem with an unproved Howie premise. The proof of the
specific ultrapower/subgroup reduction is also given directly here. Later
ring-independence proof not audited or used for a new deduction.

Forester–Rourke, author PDF multi.pdf: all four extracted pages read, including
Theorem 1 and Proposition 1 proofs and finite-subgroup remark. Exact layered
relative-complex and invertibility-over-Z assumptions are retained. This
primary source is used to delimit the known operation, not to claim that
matrix diagonalization layers arbitrary words.

Ramirez-Côté–Wise, DOI 10.1007/s00209-025-03753-3: reread extracted lines
243–365, including Theorem 9 contraction proof and Theorem 10 statement/first
proof continuation. The embedding setup and Definitions/Theorem 5 hypotheses
are inherited explicitly from the authenticated r13 source contract, not
relabeled a new full reading. No statement that B=E/[N,N] embeds in these
power-series groups is made. The embedding assumptions remain necessary in
every invocation of their theorem.

Evans, *Relation modules of infinite groups*, Bull. London Math. Soc. 31
(1999), 154–162. Read primary web PDF text lines 0–164: introduction and
Section 2 through the opening of Lemma 2.4. In particular equations (1)–(2)
define the standard free abelianized extension F/R' and relation module.
PDF download through urllib returned HTTP 403; the primary web PDF text was
available. No theorem in this paper is used as a torsion-free relative
presentation theorem. Our relative-cover argument is proved from tree normal
form. Source URL:
https://static.cambridge.org/content/id/urn:cambridge.org:id:article:S0024609398005165/resource/name/S002460939800516Xa.pdf

An exploratory primary paper, Fournier-Facio–Löh–Moraschini, *Bounded
cohomology and binate groups*, was downloaded from the authors' preprint
site. Only extracted lines 448–475, Definition 3.16 (mitosis) and adjoining
remarks through the start of Lemma 3.18, were read. It is UNUSED as a
mathematical dependency: no mitotic/acyclic envelope theorem or conclusion is
claimed. The retained PDF/text have their original private rights.

The four-generator Higman example is attributed to Higman's 1951 work,
DOI 10.1112/jlms/s1-26.1.61. Its primary body was not retrieved. We do not
rely on an unread assertion of simplicity, finiteness properties, or an
embedding theorem from it. All properties actually used (infinitude,
torsion-freeness, perfectness, finite presentation) are proved from the
displayed HNN/amalgam normal forms. This familiar example is not a novelty
claim.

## Operation comparison and novelty limits

Universal radical removal, the free abelianized extension, recursive universal
quotients, universal finitely presented torsion-free groups, quasivariety
closure and the Higman four-cycle are all credited operations. The new report's
relative normal-form checks and exact examples are research support. The
cover route fails because a solution over the same canonical base splits it;
the universal-coefficient reduction does not solve its remaining test; the
small-presentation theorem does not provide relative coefficient preservation.
No complete proof, genuine full TFS counterexample, new-to-literature theorem,
priority certificate or substantial-contribution nomination is claimed.
