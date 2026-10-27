# Complete peakon trace-power coefficient formula

This packet resolves Avan--Frappat--Ragoucy published Conjecture5.2, associated
with MathDB372008. One universal partition coefficient function works for every
particle number and positive trace power. The closed Lean endpoint is
PeakonCoefficients.source_conjecture_372008; the separate
nonnegative_source_conjecture_372008 covers literal principal square roots.

Read paper.pdf, PROOF.md, formal/SourceConclusion.lean and
reviews/final/review.md. Reproduce the strict replay with pinned Lean4.34.1 and
the pinned mathlib/packages directory:

    python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages

Expected:121 declarations,19 modules, all module logs empty, only propext,
Classical.choice and Quot.sound. Parent and independent receipts agree.
The archive requires its own fresh extracted replay before acceptance.

All64 reviewed originals are preserved with a location map. Only main.tex,
paper.pdf and paper-qa.json have release versions; all proof/verifier bytes are
unchanged. Historical candidate/checkpoint metadata retain credit0 and pending
statuses; this README and the final review supersede them. A post-extraction
acceptance.json is authoritative and is outside the immutable archive.

ONE source-question outcome only. Classical tools, helpers, the two already
conjectured coefficient families and finite checks are uncredited. Selective
semiseparable/Kostant--Toda and bounded citation/web coverage do not guarantee
worldwide priority. Unreliable MathDB companion metadata are not evidence.
