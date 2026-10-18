# Manuscript reading, provenance, and limits

This is an author-side manuscript preparation record, not a new proof or contribution verdict. Myeongjin Kang; no affiliation. Prose CC BY4, code MIT. The frozen r36 candidate and every earlier packet were left unchanged. r38 was checkpointed with no target frozen before this priority change.

## Project inputs

Read in full in this manuscript task: AGENTS.md; sources/upstream.json; frozen r36 scope027o.md, candidate027o.md, source-and-credit.md; completed proof review review.md (all E1–E6), completed contribution review review.md and reading-limits.md (all R1–R4); formal author's README; completed formal review review.md (all F1–F4). Formal T027O.lean opening and parent formal-adoption receipt opening were inspected, not the entire Lean source/builder/cache. Parent reports adopted scoped PASS after independently rebuilding54 declarations and matching receipt/logs; this author did not rerun Lean.

The complete canonical preprints-tree.json is parsed and SHA256-checked for the full source-family inventory. It has13223 entries, truncated=false. This is an identity/completeness check, not a read of every manuscript in the corpus. Source truths at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. No upstream truth audit was performed.

## Pinned source027

All13 non-PDF blobs of Integral-points-on-character-varieties-of-curves-September-25-2026 are retained privately and checked against complete-tree Git blob identities and byte lengths. The one canonical paper.pdf was not retrieved. Manuscript-task rereads: introduction.tex1–120; dynamics.tex1–155 (the complete operative closed-density proof); surfaces.tex125–265 (complete determinant-one irreducibility proof and scalar-extension distinction); model.tex50–90 (quotient closed-orbit passage); main.tex title/author metadata. Source027's other operations and earlier r36 reads are described in the copied frozen reading-limits/source-credit records; they were not all reread now. No other companion body was newly searched in this manuscript task. The frozen candidate's complete-tree companion screen remains the declared bounded screen.

## Actual primary passages read for this manuscript

- Coccia–Litt, arXiv2507.00167v1, retained HTML and text: text680–725 (Prop3.1.10 statement and opening proof),1310–1410 (Prop5.0.1 full case proof, Thm5.0.2 statement and nearby context). Full §4 constructions were not re-proved or reread. This is the cited rank2 input, not a manuscript-derived new theorem. Author metadata verified from actual HTML.
- Goldman1986: retained PDF/text; text1–95 (orthogonal structure, smooth D/G, tangent/form contract),380–475 (including Lemma1.11 and proof),1160–1335 (4.2–4.7 statements and proofs, HNN twist formula and separating comparison). Other sections were not read in full in this task. No claim that the full classical geometry is reproved here.
- Pickrell–Xia I: text410–635, full Prop2.1.24/Lemma2.1.34 operative spanning argument, including (2.1.29)–(2.1.47). Section3 sewing attribution relies on the earlier r36 operative reading/parent receipt and independent contribution comparison; it was not fully reread now. Full paper not read in this task.
- Mantelos2302.02471v4: text620–690 and915–965, plus theorem/section search hits and actual author metadata. These give the oriented-cycle identity and Lemma6.2. Earlier r36 reads include Thm1.1 and §§3–4. No global classification theorem imported as an axiom.
- Loewy1986: body remains unread; previous publisher request returned403. Bibliographic/global-rigidity antecedent only. The exact infinitesimal lemma is proved independently in manuscript.
- Golsefidy–Tamam PNAS2025: actual retained PMC text270–305 and515–590 (definition context, §2.4 higher-rank remark, exceptions G/H and I/J, PX caveat); bibliographic metadata70–100 and references. The detailed orbit-closure preprint abstract/contents/first page and rank-term searches only. Its140-page body was not read in full; neither GT_MCG-all nor IMRN exceptional-orbits paper was newly read. Higher-rank extension is explicitly unproved in the inspected publication.
- Litt2409.02234v1: actual text2035–2105, including §5.4.10–5.4.14, full Thm5.4.13 proof sketch, and title/version metadata. PX02b body not read. Its theorem is discussed solely as Litt's antecedent with GT caveat, not used uncaveated.
- **New actual primary retrieval:** BKMS, NYJM24(2018)241–250, https://nyjm.albany.edu/j/2018/24-13p.pdf, retrieved2026-10-18. Read actual pp241–242,248–249 (Prop1.2 statement, Thm5.1 and full proof of Prop1.2); retained PDF and pdftotext extraction. Theorem is GL_n fixed characters with infinite image. TQFT theorem KS Cor4.3 is cited there; its original body was not read by this author.
- MO332994: web tool returned actual question, comments and answers (lines32–156), including Kapovich comment and Lawton BKMS pointer; no local raw page retained. Treated only as discussion pointers. The comment's stronger high-rank dense-image observation was not independently verified. No claim it is supplied by BKMS Prop1.2.

Primary receipts identify every retained body/extraction with SHA256 and byte length. Copying or hashing a complete body is not a claim of complete reading. Private bodies are ignored and are not included in the public source deliverable.

## Validation limits

The full manuscript is a mathematical exposition of the unchanged independently reviewed candidate, with E1–E6 and R1–R4 editorial/credit implementation. No new orbit computation or finite-rank diagnostic was run, and none is needed as a substitute for the proof. Scoped Lean support is described in proof-scope.md and AppendixA.1; independent reviewer derivative additions are distinct from the author support. Neither proves the full geometric theorem.

PDF builds use Tectonic0.17.0 with cached dependencies and fixed SOURCE_DATE_EPOCH. A fresh copied-source rebuild must match the final PDF bytes. All final pages are rendered with Poppler and visually inspected; the receipt identifies their hashes. Exact file/directory inventory controls certify packet identity only. Worldwide literature completeness, full-source novelty, full formalization, publication, acceptance and campaign counting are not claimed.
