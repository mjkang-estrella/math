# MathDB 356756: draft manuscript and reproducible dossier

**Ready for root review; zero accepted credit.** The six-page AI-assisted draft proves exact admissibility of the conjectured digit family using the parity-corrected potential. It states the full source objects, classifies every wrap orientation, proves both gap formulas and the summation, and explains the uniform dual certificate. It makes no record or priority claim and records the EHPS comparison and source computations honestly.

Deliverables:

- `paper/digits-parity-draft.pdf` and editable `paper/build_paper.py`.
- `PROOF.md` and `STATEMENT-CORRESPONDENCE.md`.
- Byte-identical `formal/Digits.lean` and `formal/Audit.lean`; new full-body `formal/AuditFull.lean`.
- `digits-source-only.zip`, portable `replay.py`, `REPRODUCE.md` and negative controls.
- `digits-full-dossier.zip`, source copies, HTTP/search receipts and exact hashed raw MathDB line.
- Input/copy/module/source/dossier manifests, archive hashes, `results.json`, QA images and receipts.

Final safe extracted replay: **PASS**. Three strict builds and three per-module leanchecker runs passed. AuditFull printed and checked all **45 declarations, 45 full types and 45 bodies**, including generated declarations; only propext, Classical.choice and Quot.sound occur. Both false Lean variants failed for the intended mathematical reason. Existing-olean refusal was exercised. Peak sampled RSS was 3,872,192 KiB; the longest subprocess was 28.97 s. Every final subprocess respected the two-CPU, sampled 6 GiB, 120 CPU-second and 140 wall-second caps. Receipts: `fresh-replay/receipts/replay.json` and adjacent per-call receipts; full audit: `fresh-replay/logs/build-AuditFull.log`.

All six PDF pages were rendered and visually inspected; `receipts/pdf-visual-qa.json` binds the final PDF and images. The misleading cached `sieb-thesis.pdf` filename was resolved from the title page: it is Jakob Führer’s 2024 thesis. The frozen file was not changed.

All **269 frozen input files** match their before/after SHA-256 bindings. The required Digits and source-packet hashes match exactly. No git, child agents, browser, publication, external messages, shared ledger edits or writes outside this lane were used. No started jobs remain at handback. The first negative control failed initially for a hidden decidability instance; after unfolding its definitions it rejects the false proposition itself. Earlier attempts are retained transparently; final fresh-replay is operative.

Trust limits: cached upstream oleans are trusted, not source-attested. The general histogram strengthening, Stirling consequence and literature comparison are ordinary mathematics beyond the exact frozen SourceSet endpoint. Prior-art clearance is the inherited bounded review/root record, not exhaustive coverage or a new live refresh. Root alone accepts, refreshes registries and performs its final independent replay and paper review.

`DOSSIER-MANIFEST.json` binds the files inside the full ZIP (excluding itself); the full ZIP also carries that manifest. `archive-hashes.json` and `receipts/archive-integrity.json` are external post-archive bindings to avoid self-reference. Temporary Python dependencies are not part of the delivered dossier archive.
