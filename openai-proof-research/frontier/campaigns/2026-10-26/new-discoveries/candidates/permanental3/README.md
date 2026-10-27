# Sharp universal permanental Koteljanskii bounds in dimension three

One combined outcome: for every real totally positive3x3matrix,
2/3 < per(A12,12)per(A23,23)/(per(A)*a22) < 9/8,
and both constants are optimal. The literal full-minor/permanent endpoint,
all normalization bridges, both sharpness families and optimality are proved
by53declarations in six Lean modules. No residual normalized-form premise.

This sharpens Skandera-Soskin EJC32(1)(2025)#P1.14 Proposition11's bounds1/2and2.
It addresses the explicit informal optimal-constant question after that result
and in the author's slides. The related MathDB363360 Sihong conjecture is a
DIFFERENT question and is not resolved. Known9/8boundary examples and failures
of R<=1 are uncounted. Novelty searches are bounded, with no absolute priority
claim. Exact scope, sources and access limits are in the review and addendum.

Reproduce after extraction with the pinned external Lean/packages:

    python3 verification/verify_candidate.py . --lean-bin /absolute/path/to/lean --packages /absolute/path/to/pinned/.lake/packages
    python3 verification/independent-math.py

The independent exact checker uses only the Python standard library. The
optional scripts/check_algebra.py additionally needs SymPy; its numerical
samples do not replace the full Lean proof. verification/pins.json binds Lean
and all dependency revisions. The verifier copies source modules afresh,
uses warningsAsError, checks all53types/axioms, and rejects proof holes.
The allowed axioms are only propext, Classical.choice and Quot.sound.

The original independent review is preserved verbatim; reviews/parent-addendum.md
records the harmless minor-list ordering correction and qualifications.
final-review-hashes.json binds current proof/paper bytes. MANIFEST.json binds
all archived payload bytes. Final acceptance is controlled by the campaign
ledger and external packet receipt after fresh extracted replay.
