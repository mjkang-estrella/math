# Full two-branch candidate: increasing ratio to a stable Stolarsky mean

29 October 2026 UTC. Credit 0 pending parent review. Counts remain 3/30 additional, 33/60 total.

The full source Conjecture 4.7 is addressed by `PROOF.md`, a proposed complete exact computer-assisted ordinary proof for all distinct positive inputs and BOTH branches. No analytic premise is intentionally left open. The proof includes finite exact arithmetic and an explicit all-order tail bound; it is not a numerical extrapolation or a local sixth-order argument.

The common comparison mean is S_(alpha,beta), alpha=(5+sqrt17)/2, beta=(5-sqrt17)/2. Both parameter branches stabilize this SAME mean. This classical identity is expressly uncredited: Raissouli's 2011 preprint, actual Theorem 3.1 and its telescoping proof, https://rgmia.org/papers/v14/v14a43.pdf . It was found during the investigation and is also rederived in the proof. The new substantive bridge proposed here is strict increase of log(S/M) as a function of half the logarithmic input ratio. This stronger ratio comparison transfers through the resultant to prove the actual conjecture, even when the outer order is negative.

The derivative comparison reduces to E(t)>0, where E is an explicitly defined even entire exponential polynomial with polynomial prefactors. Its derivatives vanish through degree8, are positive at every even degree10..298 by exact INTEGER convolution, and are positive at all even degrees>=300 by domination of the exponents +/-(7+sqrt17). The complete finite values are provided, along with an independent rational-quadratic-field expansion and exact tail inequalities. `PROOF.md` explains why this gives positivity for every t>0, without a missing interval or endpoint.

## Primary and closest actual bodies

- https://arxiv.org/html/2405.13618v2 , actual Definition1.1, (1.5), Example4.6 and Conjecture4.7 reread live. v2 dated24May2024; saved body SHA256 ca5e87dcd0cc54c69dfeb7f69e58b118bbb4071ab5270d2c06fe55a292a8b193. The local sixth-order coefficient is already in Example4.6 and uncredited.
- https://link.springer.com/article/10.1186/s13660-016-1212-z , actual Theorems4.1/4.2/4.4 and proofs reread. Generic curvature/sandwich criteria do not supply the new ratio derivative inequality. Prior r16's exact conjugation failures retained, not reinvested.
- https://rgmia.org/papers/v14/v14a43.pdf , actual Theorem3.1 and proof. Classical stable Stolarsky identity is directly subsumed and uncredited.
- https://link.springer.com/article/10.1186/1029-242X-2012-55 , actual Theorems3.1/3.2/3.3 and proofs. Generic pointwise resultant monotonicity and refinement statements are classical. Mere M<S gives R(M)<S, which is insufficient to compare R(M) to M. The proposed strict ratio monotonicity supplies the missing bridge.
- Jovanovic–Treml, KJM49(1)(2025)105–110, actual Theorems2.1/2.2 and printed formulas2.5–2.7 read in public PDF (URL in provenance). This concerns reciprocal atan, not the nested mean statement. The web extracted plus sign in2.5 conflicts with g(1)=2/pi<1 while its displayed integral is positive. A screenshot attempt timed out; no claim about typeset sign correctness is needed. That route was abandoned and NO reciprocal-atan theorem or integral from it is used in PROOF.md. No separate credit sought.

## Current public prior coverage and limits

Authorized complete r7 registry trees/head receipts reused with ORIGINAL retrieval dates 29October2026 04:39:40–44UTC, not represented as fresh current-head equality. Checked omega Problems/D5, OpenAI preprints, count root/registry using names, source identifier and stabilizability terms; no matching path/registry proof found. Exact paths, hashes, heads and search matches are in provenance. Registry path absence is not full-text proof absence.

Fresh live public searches on29October2026 during this lane for exact source identifier, author names, Conjecture4.7, Stolarsky/arctan/logarithmic and sqrt17/arctan combinations located the original and classical Stolarsky result, but no located resolution of this target. This is bounded coverage, NOT worldwide novelty clearance. No repeated GitHub API traversal; prior rate limit respected. Prior MathDB403 route not retried; current solution bodies unread. No exact MathDB ID for this conjecture asserted.

Actual2026 journal body remains unread under inherited timeout/certificate limits; no TLS bypass or retry of affected route. Only literal arXivv2 target is certified by source comparison. The journal DOI is https://doi.org/10.2298/AADM240618001M , not evidence of body equality.

## Checks, objection and remaining gates

Run from this lane:

    python expcheck.py
    python integercheck.py
    python check.py

The first two use ONLY exact standard-library arithmetic and 512MiB address-space/40CPU-second limits, BLAS/OMP1. They verify the finite certificate by two distinct formulas and every tail bound. The third is explicitly a high-precision DIAGNOSTIC:242 gap/derivative points from t=10^-5 to10^4 and independent consistency checks of the centered source formula, stable S identity, A/B formula, and J derivative identity. It is not used as proof.

Strongest objection: independently audit/replay the finite arithmetic and all-order exponent bookkeeping, then audit the transfer and sign for the negative outer power. No independent reviewer was authorized in this solo lane; self-checking is not independent review. Also novelty is only bounded and source journal-body coverage is incomplete. No Lean or paper was started and no acceptance authority claimed. The proposed ordinary proof has no identified unresolved analytic gap, but its explicit exact-arithmetic certificate is a proof dependency requiring review.
