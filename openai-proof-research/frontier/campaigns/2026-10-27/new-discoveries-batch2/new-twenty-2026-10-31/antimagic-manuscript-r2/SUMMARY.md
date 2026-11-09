# Round 2 correction dossier — MathDB 354228

DRAFT; zero accepted credit. Root alone accepts. Campaign count remains 35/40 beyond 39, per the round-2 brief.

Corrected paper.md and PROOF.md directly from a fresh Python transcription of the frozen Lean formula. For t=2,n=3 the leaf row is (10,12,8,11,9,14,7,13), every final parent weighs 24, and the spectrum is [7,14] union {24}, nine colours. A negative control confirms that the old row gives (26,26,22,22).

The complete numerical audit found one further formula error: Section 3 must read H=4t+tq+1, not H=4t+(t-1)q+1. Both manuscript sources are corrected. D and C retain their definitions in terms of H. No other error was found. The t=4,n=3 example passed unchanged.

All 20 requested parameter cases passed, covering 27 statement groups and 6,836 evaluations, with full edge bijections, independently aggregated incident weights, properness, exact spectra, and every applicable specialized identity and inequality. AUDIT.md lists the checks and limitations; receipts/numerical-audit.json records case data. Finite diagnostics are not a proof.

The rebuilt eight-page paper.pdf includes a visible errata note. Every page was rendered and visually inspected; receipts/visual-qa.json binds the observations and page images to the new PDF hash. scripts/build_pdf.py is unchanged from round 1.

The Lean packet is byte-identical: 987233b0343fb9855f659eefedaf28bc2a91576cf5c6c3a50342671895d3d175. No Lean, lake or leanchecker ran. All bound external inputs were rehashed at sealing. The dossier ZIP was safely extracted afresh and checked against its manifest; the detached verification receipt and archive-sha256.json avoid a circular archive hash. See REPRODUCE.md for commands and boundaries.

All writes stayed in this lane. No network, git, publication, uploads, messages, browser tabs, shared ledger edits or child agents. No jobs remain running at handback. Inherited receipts under receipts/inherited-r1 describe round 1 only. Required task/reference files were read before initial hashing as expressly instructed; input bytes were bound before copying or substantive manuscript/source review. The inherited supplemental hash-timing disclosure remains inherited evidence, not a new round-2 read.
