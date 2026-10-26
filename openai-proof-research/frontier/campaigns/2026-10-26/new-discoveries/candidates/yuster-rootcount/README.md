# Four interior roots: MathDB 357503

This packet disproves Yuster's Conjecture 3.9 in arXiv:2302.12276v1. The literal Corollary 3.7 polynomial at k=48, with its canonical source parameter, has one root in each of (1/100,1/10), (1/10,1/2), (1/2,3/5), and (3/5,4/5). Thus its interior-root count with multiplicity is at least four, contradicting the proposed maximum two.

The seven frozen Lean modules contain 53 declarations. They realize the exact coefficient recurrence and factorial normalization, construct the unique source parameter, check exact rational signs, transfer them to the real polynomial, and certify the roots and final negation. No conditional source/parameter/sign/IVT assumption remains. `paper.pdf` and `main.tex` give the complete three-page manuscript. `reviews/` records independent mathematical, actual-source, arithmetic, formal and final manuscript review. `verification/` contains receipts, pins, declaration types/axioms and visual QA. `certificates/` stores full exact rational data. `scripts/check_signs.py` independently checks signs using a closed coefficient formula with Python's standard library; it regenerates its adjacent independent certificate.

## Replay

With Lean 4.34.1 and the exact compiled mathlib/dependency revisions in verification/pins.json, run from the extracted packet root:

```sh
python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
python3 scripts/check_signs.py
```

The first command checks dependency revisions and tracked cleanliness, builds isolated byte-identical sources with warnings as errors, and inspects all declarations. Only propext, Classical.choice and Quot.sound are allowed; no proof holes, custom axioms, unsafe or native_decide are used. All rational comparisons are checked in the Lean kernel.

This is one counterexample, not a count per root, helper or equivalent formulation. No minimal k, exact total root count or new entropy inequality is asserted. Wakhare's related conjecture is discussed but no separate formal endpoint or discovery is counted. Ho2026 already proves the underlying entropy inequality, which this result does not refute. Source/novelty limits are in NOVELTY.md. No external publication, contact, posting, upload or push occurred.
