# Arcsinh parameter-concavity paper and Lean review packet

Status: candidate under independent review; credit0, no acceptance.

Claim: for every x>0 the literal integral A(p,x)=integral_0^x (1+t^p)^(-1/p)dt
is strictly concave on p>log(2)/2. This proves all of Yin–Huang–Wang–Lin2019
Conjecture5.1 (p>1, 0<x<1). It does not claim concavity for all p>0.
The old small-p counterexample, classical entropy, helpers and consequences
are not separate credits. One family at most.

- paper.pdf / main.tex: complete2-page proof and honest pending status.
- formal/:5 Lean modules plus exhaustive19declaration Checks.lean.
- pins.json / verify_candidate.py: pinned Lean4.34.1, mathlibd13f23b7 and
  8installed packages. Run `python3 verify_candidate.py` for a fresh temp-copy
  compilation and type/axiom audit. No precompiled candidate oleans are used.
- PROOF.md: ordinary proof and strongest objections.
- PRIOR-ART-SCREEN.md / sources/: bounded early screen with actual source PDF.
- original-review-hashes.json: historical original freeze atdcef9ead57.

The copied formal sources are byte-identical to that original review freeze.
PROOF.md's status paragraph was updated only in this combined copy; the
original remains unchanged. SUMMARY.md and provenance.json retain historical
pre-manuscript context from that original candidate. Current packaging status
is this README and the parent review-packet receipt.

Dependencies: the verifier pins exact installed binary/package revisions and
uses the absolute package paths recorded in pins.json/run_lean.py. Reproduction
on another machine requires those same versions and corresponding local path
configuration. The archive includes the proof sources, not a vendored mathlib.

The preliminary independent review is of the original frozen math/formal
candidate. This combined paper/proof packet still requires final independent
review and root acceptance. No global-priority claim. In particular, generic
reciprocal-norm subsumption is an open eligibility review question.
