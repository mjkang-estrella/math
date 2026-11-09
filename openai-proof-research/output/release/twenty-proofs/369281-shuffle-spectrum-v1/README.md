# Four-card refutation of the printed spectrum endpoint

MathDB369281 / Clay, arXiv:2507.10294v1, Conjecture2, predicts `1/16` as an
eigenvalue at deck size four. It does not occur. This is explicitly a
correction to the displayed ceiling endpoint, not a new general spectral
theory or a disproof of a corrected conjecture.

`formal/ShuffleSpectrum.lean` constructs all sixteen fair top/bottom coin
assignments for the actual four-card shuffle, counts their positions, and
proves that the probability matrix agrees with the source binomial formula.
It then proves that the `1/16` eigenspace is zero over the complex field and
negates the stated universal spectrum claim. The finite enumeration uses
kernel-checked `decide`, not `native_decide`.

The main conjecture is represented using the usual nonzero-eigenvalue
condition and mathlib's `Module.End.HasEigenvalue`. No spectral fact is
assumed. The formula's natural index bound `n/2` equals the printed ceiling
`ceil((n-1)/2)` for integer deck sizes; specifically, both are 2 at n=4.

Status: full proof, independent review, and two-page paper QA passed.
Run from the campaign root: `python3 verify_outcome.py outcomes/shuffle-spectrum`.
Standalone releases use `python3 verify_outcome.py . --lean-bin /path/to/lean
--packages /path/to/.lake/packages`.

The paper is `main.tex`. No worldwide-priority claim is made. Original code
is MIT; original prose CC BY4.0. The code and paper are AI-assisted.


## Reproduce the release

From the campaign root run `python3 verify_outcome.py outcomes/shuffle-spectrum`. From an extracted standalone release run `python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages`. The release includes pinned dependencies in `pins.json`, exact theorem/axiom logs in `receipts/`, and the complete independent review.
