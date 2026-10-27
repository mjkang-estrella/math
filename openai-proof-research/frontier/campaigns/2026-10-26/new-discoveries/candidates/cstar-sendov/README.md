# Continuous C*-Sendov counterexample

The concrete algebra is C([0,1],C). A cubic with all roots of norm at most9/10
has a completely split derivative, two distinct critical elements of norm less
than9/10, and continuous strictly positive real convex weights. Nevertheless
every critical element is farther than21/20 from root0 in the supremum norm.

This is ONE proposed combined refutation of MathDB353909 (Krishna2026
Conjecture3, preprint2203.06916v1Conjecture2.5) and the published completely
split derivative variant (Conjecture4). Classical scalar Sendov and the
source353908 density-of-invertibles variant are outside the formal claim.

The complete mathematical argument is in PROOF.md and the3-page main.tex/paper.pdf.
Eight Lean modules contain136 checked declarations. source_counterexample_353909
and source_counterexample_published_conjecture4 are closed negations of literal
cubic source specializations; classification and positive convex weights are
proved, not residual hypotheses. source_complete_counterexample packages the
construction, splitting, norm bounds and obstruction for every critical element.
source_critical_strict_real_weights separately verifies the strict coefficient claim.

The full isolated strict replay uses Lean4.34.1 and the exact revisions in
verification/pins.json. Warnings are errors; every declaration's type and axiom
dependencies was read; only propext, Classical.choice, Quot.sound occur.
With the pinned compiler/dependencies installed, run from this directory:

    python3 verification/verify_candidate.py . --lean-bin "$LEAN_BIN" --packages "$MATHLIB_PACKAGES"

The independent final source/math/formal/bounded-novelty/eligibility/manuscript
review passes. Its unchanged report and parent audit-record qualification are
in reviews/. The exact reviewed theorem and manuscript bytes are unchanged.
Historical provenance/final-provenance/FORMAL-PROGRESS/PROOF-prelude freeze records
retain credit0 at that time. frozen-parent-hashes.json binds those historical
bytes; final-review-hashes.json binds current theorem, manuscript and metadata.
MANIFEST.json binds every archive member. Final acceptance is controlled by the
campaign ledger and external packet receipt after a fresh extracted replay.
Source PDFs remain in research lanes; URLs/hashes identify third-party papers.
No absolute worldwide priority claim is made.
