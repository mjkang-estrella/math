# Independent review of the parent cosine/Horner bridge

Reviewer: native `new_discovery_screen` agent, author of the separate integer coefficient/sign certificate. This is an independent review of the parent's analytic bridge, not an independent authorship claim for the full counterexample.

Reviewed frozen source: `lanes/parent-trig/formal/TrigBridge.lean`, SHA256 `81324cf9168c3a92051f67574e570a772f622d919af90f8cba5dc45d4d9bec63`.

**Mathematics and semantic scope: PASS.**

1. `cosine_recurrence` is the standard identity cos((n+2)t)+cos(nt)=2cos((n+1)t)cos(t), with all natural-number casts exact. The argument proves this for every real t and every natural n.
2. `witnessAngle=arccos(523/527)` lies at the intended rational cosine; the two hypotheses to `Real.cos_arccos` are discharged numerically. No angle approximation enters the proof.
3. `integer_cosine_bridge` uses exactly C0=1, C1=523, and C(n+2)=1046C(n+1)−277729C(n). Since1046=2·523 and277729=527², induction gives Ck=527^k cos(k·witnessAngle). Its recurrence is required through the last index N, and the conclusion likewise stops at N. The unconditional C1 assumption is harmless when N=0 and is true for the supplied certificate.
4. `horner_trigonometric_identity` has the correct indexing: H0=0 and H(k+1)=2108Hk+BkCk give H(m+1)=2108^m Σ_{k=0}^m b_k cos(kt). In particular N=949 uses H950 and denominator2108^949, not2108^950. The scale2108=4·527 correctly combines the coefficient and cosine denominators.
5. `negative_sum_of_horner` needs only the certified negative integer accumulator and positivity of2108^N. It places no hidden sign hypotheses on coefficients or cosine data. Its conclusion is the actual real cosine sum, not a floating-point or formal-polynomial substitute.

**Independent pinned replay: PASS.** The exact bytes were copied into this lane's fresh `review-trig-bridge/` directory, then compiled with the pinned Lean4.34.1 runner and `-DwarningAsError=true`. No parent `.olean` was imported. The three main endpoints were separately subjected to `#print axioms`; their dependencies are the standard permitted axioms only.

**Boundaries.** This module supplies the analytic cosine and Horner scaling bridge. It does not itself establish that the B data are the source's square-root coefficients; that is the independent matrix/source bridge's responsibility. It does not prove a zero of the Taylor polynomial and makes no claim on the separate zero-free conjecture. It also does not establish novelty or clear the latest published-source comparison.
