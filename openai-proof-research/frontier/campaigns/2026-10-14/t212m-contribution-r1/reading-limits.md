# Exact reading limits for the T212M contribution review, round 1

Every interval below is one I actually displayed in this review. Unless a
truncation is noted, the output was complete. Line numbers refer to the
author packet's `private/*.txt` extractions (pdftotext -layout) or to the
pinned source `.tex` files. They are not page numbers.

## Frozen author packet (`fresh-analytic-discovery-r74/`)

Read in full:
- candidate-proof.md
- dependency-map.md
- comparison-and-dependencies.md
- reading-limits.md
- dh-limiting-coupling.md
- cubic-wall.md
- label-stability-interface.md
- same-status-lowering.md
- parent-author-halfplane-transfer.md
- parent-author-status-preserving-perturbations.md
- ah-6-8-integration.md
- ah-9-10-integration.md
- structural-author-bridges.md
- stationary-extension-cocycle.md
- scope-status.json
- author-completion.json
- checkpoint.json
- verify.py

Not read (contribution role; the proof gate owns them):
- cap-author-cap-core.md, cap-author-shape-and-length.md, cap-shape-interface.md and cap-author-checkpoint.md. Their content enters only through candidate §§3–4.
- tail-and-modification.md and mechanism.md
- parent-author-extension-cocycle-linearity.md
- README.md, controls.py, interface-checker.py and interface-checks.json
- canonical-membership-check.json, source-receipts.json, primary-receipts.json, parent-author-provenance.json and source-universe.json. These were read by the author verifier only, as bytes.

## Pinned source212 (fd4aeeb2…; author's authenticated copies)

- 01-introduction.tex: lines 1–193, complete.
- 02-preliminaries.tex: lines 1–30 and 125–160.
- 05-budget.tex: lines 280–295.
- 07-tilts.tex: lines 220–232.
- 08-conclusion.tex: lines 125–140.
- Keyword navigation over all sections for moment, integrability, finite energy, AhlbergHoffman and DamronHanson. Navigation is not reading.
- Strict-convexity companion: keyword lines only (`consequences.tex` 25, 60, 88, 120–126, 164, 174, 214, 278; `introduction.tex` 168–169, 208). This is enough to confirm that the companion covers only Gamma and exponential, fixed-direction material that already satisfies the source moment. It is not a full read.

## Primary papers

- **ADH arXiv:1302.5413v2.** Appendix C, extracted lines 1225–1524 in full (all of Appendix C and the start of the references). Lines 29–30, 111–113, 237 and 551 were seen only through keyword lines. The rest of the body is unread.
- **Cerf–Théret arXiv:1404.4539v2.**
  - Extracted lines 1–140: abstract, definitions, Theorems 1–3 and the opening of the next paragraph.
  - Lines 230–280: Kesten's moment necessity at line 245 and the Cox–Durrett/Kesten contour regularization at lines 247–262.
  - Line 225 seen only through a keyword line.
  - Proofs are unread.
- **AH arXiv:1609.02447v2.**
  - Extracted lines 300–389: assumptions A1/A2, Remarks 3.1–3.3 and the start of §3.1.
  - Lines 378–392 (the shape statement), 1940–1962 (Section 9 outline), 2120–2180 (the 9.2 averaging tail, the P0 coupling and the 9.5 statement), 2470–2500 (the 9.10 Case 1 upward raise) and 3886–3940 (open problems).
  - Lines 1682, 1691–1692 and 1713 seen only through keyword lines.
  - **I did not re-read** AH Sections 6–8, 9.6–9.9 or 10 bodies. My statement that every explicit energy use matches the packet's maps comes from a keyword search for "finite energy", "(vii)", "P0" and "local modification" together with the intervals above. It is not a proof-body audit.
- **DH arXiv:1209.3036v1.**
  - Extracted lines 20–40, 140–185 (A1, A2 and the shape remark) and 1336–1505 in full: the Theorem 6.1 statement, the standing hypothesis at line 1350, the full Lemma 6.2 proof, the triple extraction, Lemma 6.3 and Lemma 6.4. This interval supports my claim that the 6.2 and triple steps do not use UFE.
  - Lines 1505–1580: Lemma 6.5, and Lemma 6.6, the UFE pushforward.
  - Keyword lines 275–277 (A1′/A2′), 325–329 (Definition 1.9) and the theorem-label list.
  - Sections 3–5 bodies are unread by me. The packet's reads are recorded in its own reading-limits.md.
- **Jacquet arXiv:2310.04091v1.** Extracted lines 1–80, plus keyword lines 304–354 on penalized paths. The proofs are unread.
- **Damron–Hanson arXiv:1512.00804v2.** I retrieved this myself from https://arxiv.org/pdf/1512.00804v2. Hashes are in `private-receipts.json`, and the copy is kept in ignored `private/`. I read extracted lines 1–75 (abstract, Conjecture 1 at lines 54–55, Theorem 1.1) and keyword lines 240–250 and 355–361. The rest is unread.
- **Not read by me:** Boivin 1990, Cox–Durrett 1981, Kesten 1986, Wehr–Woo 1998, Licea–Newman and Brito–Damron–Hanson. Each is credited only through the statements quoted in the papers above.

## History and other campaign material

- `t212m-parent/intake.json` and `dispatch-r1.json`: read. I did not read `proof-r1-brief.txt`. I did not read the brief text in `contribution-r1-brief.txt` either; I only took its SHA256.
- `agm063-contribution-r1/verify.py` and the head of its `review.md`: read, as the template.
- Keyword search with rg over tracked non-private files, excluding any `t212m-*` review directory. Commands are in `history-search.json`.
- No parallel proof-review directory existed, and none was read.

## Scratch

`/var/tmp/t212m-contrib-r1/` holds the downloaded PDF and text, plus control copies. This directory is not part of the sealed packet.
