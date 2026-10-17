# AGM063 contribution review r1: exact reading limits

Downloading, hashing or searching is not reading. Line numbers refer to the frozen author copies under fresh-arithmetic-discovery-r18/private/ unless stated otherwise. No third-party body is reproduced in this directory.

## Governing files (read completely)
- openai-proof-research/AGENTS.md
- sources/upstream.json (pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb)
- agm063-parent/contribution-review-brief.txt and author-entry.json
- The first ~600 bytes of agm063-parent/proof-review-brief.txt, enough only to confirm that it is a separate proof gate with its own output directory. The rest was not read.

## Frozen author packet (read completely)
fixed-scope.md, proof.md, contribution-map.md, adversarial-checks.md, reading.md, formal-interface.md, checkpoint.md, normal058-checkpoint.md, primary-receipts.json, verify.py.

- manifest.json was inspected for its schema and its counts.
- receipts.json was checked by the author verifier only.
- private/context snapshots r5–r17 were grep-screened for Mukai or 063 (the only hit was r16 line 63, a Mukai pairing in an unrelated context). They were not reread in full.

## Pinned source family063 (author copies, Git-blob verified by the replayed verifier)
- **Read completely:** introduction.tex 1–137, equality.tex 1–157, setup.tex 1–136.
- **trace.tex:** only prop:independent-correspondences and its proof (lines 155–204) were read. The rest was not read.
- **Not read:** spectral.tex and descendants.tex (stipulated lower inputs, per the brief), main.tex, references.bib, README.md.
- **Not retrieved:** the article.pdf blob listed in the tree.
- **Inventory:** the complete repository sources/preprints-tree.json (truncated=false; it equals the author context copy byte for byte) was enumerated for family063 and for Fano, Mukai, rational-curve, quantum and chain titles. sources/CONTENTS.md was grep-screened, and the 052/062/063/066/067 entries were read at catalogue level. No companion asserts AGM.

## Primary bodies
1. **Fujita, Around the Mukai conjecture for Fano manifolds** (Eur. J. Math. 2 (2016); the author's pdftotext copy).
   - Lines 1–520 were read in sequence. This covers the abstract, Conj. 1.1–1.4, Rem. 1.5, Thm. 1.6/1.7, Prop. 1.8, Rem. 1.9, the organization paragraph, notation, all of §2 (Defs. 2.1–2.4, Prop. 2.5/2.6, Lemmas 2.7–2.9), all of §3 (Def. 3.1, Thm. 3.2, Prop. 3.3, Thm. 3.4 with proof, Constr. 3.5, Lemmas 3.6/3.7), and the start of §4 (Def. 4.1, Lemma 4.2, Prop. 4.3 with proof, Def. 4.4 and formula (1), and the statement of Lemma 4.5).
   - Lines 521–539 (the rest of Lemma 4.5 and its proof) were NOT read.
   - Lines 540–1010 were read: Cors. 4.6/4.7 with the proof of 4.7, all of §5 (Thm. 5.1/5.2, Prop. 5.3 with proof), all of §6 (Thm. 6.1 with Claims 6.2/6.3, Cor. 6.4 with proof), all of §7 (Props. 7.1–7.3 with proofs), and the start of §8.
   - §8 beyond line 1010 and the references were not read.
   - The text extraction loses some glyphs. No visual PDF inspection was done.
2. **Dedieu–Höring, Numerical characterisation of quadrics** (version of December 15, 2016). Only text lines ~29–90 were read: Thms. 1.2/1.3, the Miyaoka-gap remark, the n≤3 remark, Cor. 1.4 and the outline. The proof was not read.
3. Kollár IV.4.16, BCDD, Occhetta, Höring–Novelli and the other lower references are known only through the statements quoted by Fujita or the source. Their originals were not retrieved.

**Fresh retrieval.** Both primary URLs in the author's primary-receipts.json were downloaded on 2026-10-17 into a new, empty temporary directory. Only their SHA-256 hashes were taken: Fujita d97b566d2dc6ac2173dc8e722c6835d70f3884982f554b908b65ec995b21bf92 and Dedieu–Höring d1e8594d45db3e1cde3890be58b25f0f5a51bf8783c849017ce56a165263d55b. Both match the receipts. The downloads were then deleted.

## History screen (bounded)
history-search.json records the queries and the hits. The grep covered *.md, *.json and *.txt under frontier/, findings/, proposals/, reviews/ and notes/, excluding private/, inputs/, context/, corpus/ and tree/CONTENTS copies. The terms were mukai, pseudoindex, unsplit, 063 and Generalized-Mukai. These were read at the hit lines:
- the geometry scout line 62
- NEW-TEN line 961–963
- tasks.json lines 2939–2984
- r16 checkpoint line 63
- i19 line 5 and i21 line 18
- i136 lines 169–178 (family066 only)

No developed family063 chain was found. This was not a semantic reading of every old task note or proof. The prior contribution reviews o217, cm275, ab194 and complex-projector-borsuk-r3 were consulted only for their verdict format and calibration lines.

## Literature (search only)
Two standard web searches were run (see history-search.json). The results (arXiv 1409.8433, math/0309473, 1206.1990, 0905.4388, 2403.14065, 2411.00379 and others) were titles and snippets only. None was read. They are neither premises nor novelty certificates.

There is no claim of exhaustive history clearance, literature clearance or worldwide priority.
