# Independent ordinary-proof and eligibility review

Date: 2026-10-29. Solo, assigned lane only. No git, children, browser tools, contact, posting, uploads, Lean or paper work. This is a recommendation to root, not acceptance or a nomination.

## Decision

**Overall HOLD on eligibility clearance; preserve the full ordinary theorem for further consideration.** Mathematical gate: **INVEST / ordinary proof sound**. Source gate: **INVEST / exact full published target answered**. Novelty gate: **HOLD / no exact subsumption located, current registry head blocked**. Substantive gate: **INVEST, provisionally**, with a serious routine-adaptation objection. I do **not** adopt r57's categorical EXCLUDE merely because the proof is classical and short. This recommendation neither establishes literature priority nor authorizes discovery credit.

The evidence now includes an actual published general comparison theorem with its hypotheses checked below. That establishes much more than the worker's bare reference to Sturm comparison. It still stops short of a published theorem whose conclusion is this full parameter-ratio unimodality statement. My provisional substantive judgment is that the target-specific global bridge is enough to investigate at the campaign's demonstrated minimum depth, pending root's judgment. It is not new comparison machinery.

## Exact source and versions

Read the frozen published KVZ body, Results in Mathematics 80:112 (2025), DOI [10.1007/s00025-025-02431-4](https://doi.org/10.1007/s00025-025-02431-4), §§2 and 4, especially PDF pp.6,17–18. A fresh publisher PDF has exactly the frozen PDF's SHA256, `1ba19be497b661f25b6572b0c35afb938974ba8807965ec38be7693691db8115`. The target is the final §4 paragraph: for every real u≥v>−1 and 0<a≤b, I_u(ax)/I_v(bx) is unimodal on (0,∞). Its inherited scale restrictions matter. The published definition explicitly includes monotone and constant functions, and allows either orientation of a single turn. The proof gives the stronger restriction that any genuine turn is a peak.

The preceding proof on p.17 treats even positive integer order differences; Theorem 4.3 is its Q-function integral-transform consequence, with that same order restriction. Neither supplies arbitrary real difference simply by relabeling parameters. Multiplication by x^(u−v) is not in general unimodality preserving, so the common power-series theorem cannot be applied after discarding this factor.

The saved earlier author manuscript has a separate log-concavity clause. That clause is absent from the published ending. The live arXiv history HTML matches the worker's frozen history byte-for-byte; I do not claim to have independently downloaded every arXiv version body. The frozen Omega problem/result bodies explicitly distinguish log-concavity from unimodality and give the former's counterexample. Their path history records the public October 25 result. This is disqualifying prior public work for the log-concavity refutation only; it does not settle this target. No new credit is sought for it.

## Independent mathematical verification

For ν>−1, Γ(k+ν+1)>0. The defining series is positive on the positive axis and converges locally uniformly with differentiated series after factoring x^ν. Thus f=I_u(ax), g=I_v(bx) are positive C² functions there and satisfy

    (x f')'=(a²x+u²/x)f,  (x g')'=(b²x+v²/x)g.

I independently differentiate W=x(f'g−fg'), using these two identities, to obtain

    W'=[(u²−v²)/x−(b²−a²)x]fg,   (f/g)'=W/(xg²).

There is no omitted factor of a or b: those enter the scaled equations through a² and b². No sign of f' or g' is used. Put δ=u−v, s=u+v, A=δs, B=b²−a²≥0. With C=(a/2)^u(b/2)^v/[Γ(u+1)Γ(v+1)]>0,

    δ>0: W=C x^s(δ+O(x²));
    δ=0: W=C x^(2v+2)((a²−b²)/(2(v+1))+O(x²)).

These follow directly by differentiating the convergent factored series. For δ>0 the first expression is positive near zero even if s<0. One must NOT integrate W' from zero with W(0)=0 in that case. For δ=0, 2v+2>0, so W tends to zero.

* δ=0: W'=−Bxfg. For B>0, strict decrease from the zero limit implies W<0; for B=0, f=g and the ratio is 1.
* δ>0 and A≤0: W is strictly decreasing unless A=B=0. Initial positivity gives at most one zero, with positive-to-negative crossing. If A=B=0, W is a positive constant, including u=−v with distinct orders.
* δ>0, A>0, B=0: W'>0 and initial positivity gives W>0 everywhere.
* δ>0, A>0, B>0: W increases up to t=sqrt(A/B), is positive through t, and strictly decreases afterwards. Hence at most one zero, only after t, again a positive-to-negative crossing.

The derivative relation and mean value theorem give exactly the source conclusion. All finite positive x are covered. Neither 0 nor ∞ is in the target domain, and a large-x estimate is unnecessary for at-most-one-turn. A peak's existence is not asserted in every unequal-scale case by this argument. Constancy forces A=B=0 from W'≡0; if δ>0 the endpoint formula excludes W≡0, leaving exactly u=v and a=b. No residual ordinary analytic bridge was found.

The negative-sum case is a real stress test: u=−1/4,v=−3/4,a=b=1 has A<0, initially positive W and eventually negative W. Thus equal scales do not imply that every distinct-order ratio is increasing. Our independent exact series enclosures certify W>0 at x=1/10 and W<0 at x=20 in this case.

## Concrete classical bridge, and its limits

Read actual primary bodies, not just titles:

1. Krüger–Teschl, *Relative oscillation theory for Sturm–Liouville operators extended*, J. Functional Analysis 254 (2008), 1702–1720, DOI [10.1016/j.jfa.2007.10.007](https://doi.org/10.1016/j.jfa.2007.10.007), author-hosted [body](https://www.mat.univie.ac.at/~gerald/ftp/articles/RelOsc2.pdf), §§2–3, equations (2.2)–(2.5) and Theorem 3.1.
2. Eckhardt–Gesztesy–Nichols–Teschl, *Weyl–Titchmarsh theory for Sturm–Liouville operators with distributional potentials*, [author body](https://www.mat.univie.ac.at/~gerald/ftp/articles/DistSL.pdf), Hypothesis 2.1, equations (2.5)–(2.7), Lemma 2.3. This independently verifies the classical identity in a common-operator formulation.

For the first source set p0=p1=x, r=1, q0=b²x+v²/x, q1=a²x+u²/x, u0=g, u1=f, and λ0=λ1=0. Its W(g,f) is precisely our W. On every positive compact interval, p,r>0, 1/p,qj,r are locally integrable, and solutions and their fluxes are locally absolutely continuous. Its equation (2.5) becomes exactly W'=(q1−q0)fg. This verification does not require regularity at the singular endpoint 0, a self-adjoint realization, spectral boundary conditions, or square-integrability of the Bessel functions.

Theorem 3.1 explicitly includes zeros of W, unlike the elementary textbook formulation about solution zeros alone. Where q0−q1=Bx−A/x>0, it implies that two zeros of W would force a zero of f, impossible since f>0. In particular it applies on all (0,∞) for A≤0 except the identical-potential case, and on (t,∞) when A,B>0. On the earlier interval (0,t), q1>q0 and W'>0, so initial positivity excludes a zero there. At t continuity and strict earlier increase give W(t)>0. For A>0,B=0 the derivative is positive throughout. Equal potentials and equal orders require the elementary cases already handled. There is no unverified direct use of a theorem across a potential sign reversal.

This is a fully checked classical-comparison reduction. **It is not an exact published all-parameter unimodality theorem.** Positivity at the singular endpoint and the splice of the two comparison regions remain application-specific. A theorem saying only that W' changes sign once is insufficient: W=1−(x−2)² on (0,4) has W' first positive then negative and two zeros. Taking g=1 and f=10−x³/3+2x²−3x>0 on that interval realizes this W as f'g−fg'. The omitted initial-sign hypothesis changes the conclusion.

## Adjudication of substance

The strongest EXCLUDE case is now concrete: the entire proof follows from the published Wronskian identity/comparison theorem, the leading Bessel series coefficients, and a few sign cases. No difficult new estimate, new special-function identity, or new general comparison theorem occurs. An analyst versed in positive second-order equations could reasonably call it a routine application. The endpoint work is elementary; I do not claim that merely doing it makes a theorem significant.

The opposing case is also concrete. The published paper leaves the full continuous-order question open after a discrete-difference proof. The global comparison requires matching the potential difference, retaining initial positivity despite a possible divergent W, and eliminating the first of two possible crossings. This answers the full four-parameter source assertion, rather than correcting an endpoint or extracting a parameter instance of its own theorem. The checked primary classical bodies do not already state that global criterion for this ratio.

I read frozen ordinary proofs of the accepted arcsinh-positive and gamma-level-convexity families as calibration only. They explicitly identify their central entropy bound and perspective-convexity mechanism as classical; their short source-specific normalization/derivative and strictness bridges carry the application. They show that “standard identity + elementary sign/Jensen argument” is not by itself a consistent exclusion rule here. Gamma has more convergence/level-existence work; arcsinh is closer in depth. These are reasons to retain this result for eligibility consideration, not binding precedents and not evidence of priority.

On balance my recommendation is **provisional INVEST for substance**, rather than categorical EXCLUDE. Root may adopt the stricter routine-adaptation judgment, but should identify that as a depth judgment, not a demonstrated printed duplicate or a gap in the mathematical proof. An exact earlier full-ratio theorem, or a published positive-solution one-crossing criterion that applies with essentially no target-specific argument beyond substitution, would strongly reverse this recommendation. No such item was located in this bounded review.

## Prior-art coverage, failures, reproducibility

Read frozen nearest bodies: KVZ published/earlier author manuscript; Nanthanasub–Novaprateep–Wichailukkana (2019), including its individual-Bessel log-concavity hypotheses; Salazar arXiv:2607.05538v1, its adjacent-order Bernstein result and the individual/K quotient classifications; the Omega problem/result and path history. The latter scopes do not prove this arbitrary-order arbitrary-scale ratio statement. Search combinations included Bessel ratio/unimodality, Karp–Vishnyakova–Zhang/conjecture/proof, and Wronskian/Lagrange/Sturm comparison. Search results directed primary-body reading; secondary snippets were not used as subsumption evidence. No worldwide, full citing-corpus, MathSciNet or zbMATH clearance is claimed.

The frozen r57 Omega D5 and Problems tree objects are complete in those named scopes only: 23,236 and 1,551 entries, truncated=false, anchored at dev 3b4135a35caa0ae817cf5eca51d605b098027fd2 as observed by r57. Own validation records their hashes and flags. My fresh head request at 15:55:55 UTC returned HTTP403 rate-limit exhaustion. No retry or bypass. Consequently I cannot verify an unchanged current head or a complete head delta; those cached trees are **not** current clearance in this review. I make no independent current-clearance claim for the other four registries. Prior r57 coverage is preserved as historical evidence only.

The Nagy lecture-note URL returned just 212 bytes despite HTTP200, not a PDF; it is not source evidence. The web tool's radon-host DistSL request failed; the author's www-host URL succeeded normally. These failures are retained. The earlier r57 d-nb429 was not retried. The fresh canonical publisher PDF succeeded with an automatic cookie-related redirect and matches the frozen version.

`owncheck.py` is a newly written checker, not a rerun of the worker's 2,295 coefficients. It encloses the infinite normalized Bessel and weighted derivative series with exact rational arithmetic and a geometric weighted tail at 100 terms; all eight W-sign stress cases pass, including negative sums, equal scales/orders, A=0 and a peak with positive orders. These are diagnostics, not the universal proof. The generic missing-endpoint counterexample is exact. `ownchecks.json` and `owncheck.log` retain output and limits.

Python computational work and PDF extraction use AS512MiB, CPU210s, wall230s, BLAS1; the reused guard monitors process-group RSS512MiB every40ms. Own checker sampled peak ~10.3MB, wall0.052s; fetch ~25.3MB, wall6.42s. Sampling does not exclude intersample transients. The initial singleton freezer used hard AS/CPU and timeout at the same limits with no child processes. No Lean process ran, and no cap was raised.

All consumed supplied files were frozen with before/copy/after SHA256 equality before substantive reading; work used those copies. `input-freeze.json` and `input-after.json` bind originals to the frozen bytes and recheck them at completion. Downloaded primary artifacts and their derived texts are separately hashed in provenance; no external content was modified. No counts or acceptance files were changed.
