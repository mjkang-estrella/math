# Hermite envelope conjecture — full source theorem

This packet proves Guo--Liu Conjecture1 (published Eq29, arXiv Eq30), MathDB346243,
for every integer n>=1 and real x>0. It uses the literal physicists Rodrigues
Hermite function, Gamma coefficient, square-root cutoff and clamped envelope.
The closed Lean endpoint is HermiteEnvelope.source_conjecture_346243. No
odd-bulk, ODE-comparison, strict-energy-loss or tail hypothesis remains.

## Read and replay

- paper.pdf / main.tex: three-page release manuscript.
- formal/SourceDefs.lean and OddCompletion.lean: literal definitions and closed endpoint.
- Remaining15 formal modules: actual Hermite ODE/initial data, Wallis bridge,
  positivity-safe comparison, energy loss, real-root moment tail, low degrees.
- verification/verify_candidate.py and pins.json: isolated strict verifier.
- reviews/final/review.md: independent final five-gate review and access limits.
- reviews/parent-final-addendum.md: review reconciliation and release changes.
- NOVELTY-R2.md: bounded additional classical/citer/registry source investigation.

Run with the pinned Lean4.34.1 binary and pinned packages directory:

    python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages

Expected:162 declarations,17 modules, all module logs empty, only propext,
Classical.choice and Quot.sound. The parent and independent receipts are
byte-identical. A separate post-extraction replay is required before acceptance.

## Original reviewed bytes and scope

All105 independently reviewed originals are preserved and hash-bound by
reviewed-parent-hashes.json and reviewed-file-locations.json. Only main.tex,
paper.pdf and paper-qa.json have presentation-only release versions; reviewed
originals are under reviewed-originals/. All formal/verifier and mathematical
source bytes are unchanged. Historical PROOF.md/provenance.json and supporting
checkpoint notes contain older incomplete statuses; FULL162-INTEGRATION.md,
this README and the independent final review supersede those statuses.
The archived candidate keeps credit0 until the parent records a successful
fresh extracted replay in a separate acceptance.json, outside this archive.

This is ONE full explicit source-conjecture outcome. Classical Hermite/Wallis,
ODE/Taylor, real-root/Cauchy and compactness tools, known even/low-degree cases,
helpers and finite numerical checks are not additional discoveries.
The bounded prior-art screen found no resolution/subsumer. The adjacent MDPI2026
fractional-Hermite body remained unread; no exhaustive MathSciNet/zbMATH survey
or worldwide-priority guarantee is claimed. The rejected preliminary false
sine-upper-bound coverage claim is explicitly NOT adopted.
