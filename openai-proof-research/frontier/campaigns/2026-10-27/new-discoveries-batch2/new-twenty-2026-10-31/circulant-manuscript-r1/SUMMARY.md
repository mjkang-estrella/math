# MathDB 350979: draft manuscript and dossier

Complete within circulant-manuscript-r1. Zero accepted credit; root alone accepts.

The five-page draft proves that every order-15 circulant with diameter 2 has mp-number at least 3, refuting the exact universal existential quantifier in Conjecture 4.5. The proof includes the triangle and open-twin lemmas, the 128-mask classification and a table of all 19 triangle-free masks. The residual graphs are familiar C5[3K1] blow-ups, with exact mp-number 6; the known product formula gets no separate credit. Verified positive witnesses cover every order 11 through 40 except 15. The corrected question excluding 15 remains open beyond that range.

- paper/circulant-draft.pdf: five-page AI-assisted DRAFT, with explicit trust and access limits.
- paper/manuscript.json and paper/build_paper.py: editable text and PDF builder.
- PROOF.md and STATEMENT-CORRESPONDENCE.md: ordinary proof and correspondence.
- circulant-source-only.zip: clean portable proof sources, AuditFull, controls, drivers and certificates.
- circulant-full-dossier.zip: source materials, receipts, paper, rendered QA and complete dossier (no local oleans).
- REPRODUCE.md, pins.json and SOURCE-MANIFEST.json: replay instructions and pins.
- fresh-replay/receipts/replay.json: PASS after safe fresh extraction of the source-only ZIP.
- fresh-replay/logs/build-AuditFull.log: full types, bodies and axiom data for all 52 local declarations, including generated ones.
- receipts/frozen-integrity.json: all 372 frozen original input files unchanged.
- INPUT-COPY-MANIFEST.json, MODULE-HASHES.json, DOSSIER-MANIFEST.json and archive-hashes.json: SHA-256 bindings.

Validation: fresh sequential strict builds and one-module-per-process leanchecker runs passed for all seven modules; both false controls failed for the intended false-decision reason. Independent certificates verified all 128 masks and all triple-path witnesses at the 29 positive orders. Only propext, Classical.choice and Quot.sound occur transitively. All five PDF pages were rendered and visually inspected. No child agents, git, shared-ledger edits, browser, publication, uploads or external messages were used. No launched job remains running.

The journal body remains unread (403); worldwide priority and a complete citing-literature census are not established. Cached mathlib oleans are trusted and not rebuilt. The exact mp=6 and coverage computations supplement rather than extend the literal Lean source_refutation endpoint. Root must still perform its final replay, paper review and acceptance decision.
