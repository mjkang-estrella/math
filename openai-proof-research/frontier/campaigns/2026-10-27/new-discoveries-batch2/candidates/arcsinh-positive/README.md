# Generalized inverse hyperbolic sine: paper and Lean proof

For every real x>0, A(p,x)=integral_0^x (1+t^p)^(-1/p)dt is strictly
concave on p>log(2)/2. This resolves all of Yin–Huang–Wang–Lin (2019),
Conjecture 5.1 (p>1,0<x<1). No optimality or all-p>0 concavity is claimed.

paper.pdf and main.tex contain the complete ordinary argument. formal/
contains the genuine real-power/interval-integral certificate: 19 declarations
in five modules, standard three axioms only. Run python3 verify_candidate.py
to compile fresh sources, verify exact toolchain/package pins, and inspect
the generated actual types and axiom reports in verification/Checks.log.
No candidate oleans are bundled. The exact pinned installed Mathlib is a
dependency, not vendored here; another machine must configure its local paths.

reviews/ includes independent preliminary/final reports, the final reviewer's
fresh extracted replay receipt, and root corrections. Both reviews PASS with
bounded novelty and elementary-proof caveats. historical/ preserves the
reviewed manuscript and pre-review notes; those pending-status labels are
historical, superseded by this README and the current acceptance receipt.
The current final archive receipt and parent acceptance decision are saved
alongside this candidate in the campaign, bound to the archive SHA256.

One outcome only. The old excluded small-p witness, entropy identity,
derivatives, all-x extension and Turan consequence receive no separate credit.
No external posting or publication was performed by this assembly.
