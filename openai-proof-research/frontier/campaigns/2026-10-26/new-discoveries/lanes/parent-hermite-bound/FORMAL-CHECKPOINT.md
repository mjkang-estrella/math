# Supporting formal checkpoint: 33 declarations, three modules

This supersedes only the initial19-file freeze's statement that there is no
formal code. It does NOT supersede its pending novelty/eligibility review or
credit0. The literal source conjecture has been defined, but NOT proved.

All3 modules compile from source with warningAsError=true, exit0 and empty logs
under the absolute pinned Lean4.34.1 binary and the existing pinned mathlib
d13f23b7 packages. AxiomCheck.lean prints ALL33 actual types and axiom reports;
the parent read the entire output, all standard3 only. Logs, code hashes and
the precise scope are in formal/helper-build.json and formal/axiom-check.log.
This is a supporting compile/axiom check, not an extracted full-candidate replay.

- SourceDefs: physicists' Hermite recurrence; proves its exact equality to the
  source Rodrigues definition using actual repeated Gaussian derivatives;
  derivative recurrence and Hermite ODE; literal Gamma coefficient, cutoff,
  clamped envelope and exact SourceConjecture346243 definitions.
- Energy: actual weighted Hermite and slope derivatives, energy derivative
  -2xy^2 and antitonicity on[0,infinity), bulk bound conditional ONLY on its
  explicit initial-energy bound. That hypothesis has not yet been instantiated
  at the source Gamma coefficient, even for the even-degree branch.
- WallisBounds: actual Mathlib Wallis-product ratio, exact recurrence,
  antitonicity, corrected-ratio strict increase and limit1, strict bound<1,
  and gamma_m<=9pi/28 for m>=1. The identification of this Wallis ratio with
  the source's odd-degree initial energy is NOT formalized yet.

Missing before a full literal endpoint: source Gamma/initial-value identities;
odd-degree ODE sine comparison, small-interval bound and strict energy loss;
n=1 branch; a formal proof of a sufficient global tail bound (the mathematical
argument currently invokes classical Cramer--Indritz, which is absent from
pinned Mathlib); low-degree tail cases; final clamped assembly. No new axiom,
surrogate Hermite, or unproved classical theorem will be silently assumed.

The original19 mathematical review files remain byte-identical. Additional
source files now include actual bodies of all4 indexed citing works (Nature2023,
ResearchSquare preprint of the2023 diatomic paper, arXiv2109.05338 and2603.05886),
but only a keyword/reference-location screen has been performed so far; no claim
that their full theorem bodies have been cleared. The AMS Indritz1961 requests
returned403 HTML, transparently stored as HTML, not PDFs. DLMF18.14.9 actual
official body records the exact classical bound used in PROOF.md.

Adversarial review should explicitly test whether the full source claim is an
immediate combination of older bounds: Foster--Krasikov at middle x, an elementary
linear estimate near0, and Cramer--Indritz near the turning region. A bound
exceeding the target at0 alone does not rule out that combined subsumption.
No priority claim, no independent formal/manuscript review, no paper or packet,
and no discovery credit exists here. Accepted tally remains24/30.
