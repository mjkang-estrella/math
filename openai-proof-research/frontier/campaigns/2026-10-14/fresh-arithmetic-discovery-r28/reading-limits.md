# Reading, identity and validation limits

This round used AGENTS.md, sources/upstream.json, sources/CONTENTS.md, complete sources/preprints-tree.json, the arithmetic-r23 brief with the parent's r28 ownership/count overrides, current NEW-TEN ledger ending at R035, and actual history items described in source-and-credit.md. Broad catalogue/headings and r39 history searches were selection aids, not complete manuscript reads. Some early combined tool outputs were truncated; no complete-reading claim is based on their omitted parts.

## Pinned source bodies

All 39 non-PDF source blobs for the three named manuscripts were downloaded and authenticated: 25 across family200's two companions, and14 for family008. Receipts record canonical path, immutable URL, complete-tree Git blob identity, SHA256 and byte count. source-family-inventory.json records the exact corresponding canonical entries including PDFs, which were not downloaded or read. Authentication is distinct from reading.

Family008: complete introduction (including equations, thm:main, noncanonical generators, context and organization); 02-algebra lines1–95 (including complete lem:lie-lattice and proof) fully read, with additional later portions only partially read in a truncated initial combined output; complete04-deletion and references fully read. All source files were searched for faithful/matrix/representation/enveloping terminology, but matching lines are not full reads. Sections03,05–08, preamble, figures and the rest of02 were not read as complete proofs. The source theorem is used as stipulated, with no attempt to audit its truth. The full04 operation comparison was added after the scope freeze; the theorem/PBW interface and closest CR/BEG operations had been read before freeze.

Family200: complete Betti-paper build/main.tex and sections01-introduction,01-forms,02-filtered,06-tor,07-assembly, plus the EGH-companion complete01-introduction, read in the earlier screen. Other acquired source sections are not claimed read. I226's complete report and parent disposition were read. CHH was used only to test applicability of the pre-freeze rigidity idea, which was rejected.

## External primary bodies

Private versioned HTML receipts: CHH2003 math/0306236v1; CR2020 2006.04676v1; BEG2008 0807.2345v1; MS2012 1107.1413v3. All four full downloaded HTML bodies are SHA256-authenticated; the PDF counterparts were not read or rendered.

* CHH: web lines22–315, including §§1–2 and Corollary2.7's lex argument; later lines315–396 partially incidental. Not a full paper reading.
* CR: introduction and §1.1, then §4's complete construction/Theorems4.2–4.4 and proofs via overlapping reads through line732. Lower-bound §§2–3 were not read completely. The body of the final displayed block matrix was missing from the web text rendering; its surrounding three-block structure and proof were read. No claim to have visually inspected that formula is made.
* BEG: introduction, §§2–3 completely; §4 through its cohomological construction/limitations; §6.2's full finite-example comparison. §5 was incidentally returned in a later tool call but not used; no exhaustive primary proof audit is claimed.
* MS: introduction and §2's effective-versus-faithful distinction/tensor-power transfer, and complete §7.1/Theorem24 proof. §§4–6 and remaining applications not read. This comparison occurred after freeze and strengthens attribution without changing target or proof.

Lo–Ostheimer publisher page failed to open. The source references Reutenauer, Hirose–Sato, Hirose and other antecedents, whose original primary bodies were not opened in this round; claims about their role are attributed to the pinned source, not represented as first-hand primary reads. Burde–Moens and general truncated-algebra minimal-module literature remain unchecked leads. Search results alone are not relied on for mathematical theorems. No worldwide novelty claim follows from this bounded search.

## Exact finite diagnostics

`python diagnostic-008.py` uses Python standard library only. It checks all top-word extracting entries for caps1–24; all words of weights cap+1 through cap+6 vanish; independent recurrence counts match actual state lists; exact rational rank equals the full truncated associative dimension for N3–18; and1,029 pair products agree with free-word concatenation/cutoff. Three deliberate construction mutations are detected: no crossing, only unit prefix gaps, and reversed suffix creation. Independent Lyndon-word enumeration agrees with the weighted Witt formula through weight24. The report is diagnostic-008-result.json. This is finite verification, not the all-N proof.

`python diagnostic.py` retains the family200 finite search and exact rational Koszul calculation. The first attempt to use SymPy failed because it was not installed; the completed script uses standard-library Fraction elimination and passes. A later attempt to parse primary HTML using BeautifulSoup failed because that package was absent; no output from it is used. Actual primary reads proceeded through the web tool.

No formal verification, independent proof/contribution review, manuscript PDF, release, upload, stage or commit occurred in this author task. Count remains13/20. Original prose CC BY4.0; original diagnostic/verifier code MIT; third-party bodies remain private and excluded from public inventory. The author's full proof is ready for separate review, not accepted.
