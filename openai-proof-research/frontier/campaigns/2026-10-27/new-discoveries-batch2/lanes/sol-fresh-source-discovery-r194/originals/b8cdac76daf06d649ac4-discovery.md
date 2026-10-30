# r79 — sign-averaged lasso maximum: complete mathematical separation, eligibility HOLD

Research date: 2026-10-29 UTC. Worker credit 0. No acceptance proposed without source, novelty and substantive review. No PROOF.md is issued because the published-body and exact surviving-conjecture gates are incomplete.

## 1. Screening before nomination

All campaign dates were searched, including FINDINGS.md, other Markdown and JSON reports. `all-campaign-report-files.txt` inventories those filenames; `duplicate-report-files.txt` records the initial rg -l conjecture/open-problem hits. The later precise filename-first screens are `target-duplicate-files.txt`, `precise-duplicate-files.txt`, and `lasso-duplicate-files.txt`. The last is empty outside this lane for `2303.16843|Stallrich|lasso sign recovery`. The broader numerical-ID screen returned unrelated hashes; these are not mathematical overlap. Bounded sections of the three old log-concavity listing JSON files (around lines2740–2785) identify the strengthened varentropy question346595; they contain database entries, not a proof attempt. r74's relevant mentions concern its Chernoff bibliography/search material, not this lasso problem. Nothing is described as globally fresh on this evidence.

Three precise questions were screened:

1. Melbourne–Tkocz Conjecture5.1: concavity of log(t sum_i x_i^t), t>0, for finite positive monotone log-concave sequences. EXCLUDE: actual Melbourne–Palafox-Castillo2111.06997v1 Theorem1.1 states the full stronger l1-sequence result. Read its statement, introduction and surrounding applications. The published 2023 AAP33(6A)4322–4340 record identifies DOI10.1214/22-AAP1919. No rediscovery.
2. Orthogonality maximizing the lasso sign-averaged criterion for every fixed tuning parameter. EXCLUDE as already counterexampled in the source itself: 2303.16843v3 Section3.2, PDFp26 and Fig5, explicitly discuss failures. This cannot be nominated by relabeling their numerical phenomenon.
3. Orthogonality maximizing the **maximum over all tuning parameters**, for unknown signs, across completely symmetric positive-definite correlation matrices. INVESTIGATED. Section2.2 PDFp14 defines the max summary over lambda>0; Section3.2 PDFp27 argues its orthogonal global optimality is plausible. Its final sentence instead displays fixed-lambda symbols and says “generally”; the exact intended quantifiers require adjudication. The result below separates entire optimized curves, not a single fixed-lambda comparison. The integral summary is not resolved.

Target source: Jonathan W. Stallrich, Kade Young, Maria L. Weese, Byran J. Smucker, David J. Edwards, *An Optimal Design Framework for Lasso Sign Recovery*, arXiv:2303.16843v3, revised24April2025, JRSSB87(5)(2025)1457–1480, DOI10.1093/jrsssb/qkaf026. Actual latest preprint PDF includes technical supplement; Sections2.1–2.2,3.1–3.2, relevant supplemental formulas read. Actual VoR full body remains inaccessible (see provenance), so this is NOT full source clearance.

## 2. Exact mathematical claim established here

Let p=3,k=2,beta=1. Put C(c)=(1-c)I_3+cJ_3 and let psi_lambda^±(c|2,1) be the source's sign-averaged sign recovery probability, averaging uniformly over four active sign vectors and, if desired, over the three supports. Define M(c)=sup_{lambda>0} psi_lambda^±(c|2,1). Then

    c_*=-49999/100000,
    psi_(1/20)^±(c_*|2,1)>61/250,
    for EVERY lambda>0, psi_lambda^±(0|2,1)<27/125.

Consequently M(c_*)>M(0), with a certified gap exceeding7/250. Numerically the fixed witness probability is about0.30306; that diagnostic is not used in the proof.

All substantive model hypotheses hold: C is strictly positive definite, all diagonals are1, beta=1 is positive and meets the source's practical beta>=1 discussion, lambda is strictly positive, and there is a genuine inactive factor. There is no singular covariance or zero-signal input. Eigenvalues are1-c (twice) and1+2c=1/50000. Each support is equivalent by permutation invariance. This is the source's approximate correlation-matrix optimization, not a claim of a +/-1 supersaturated exact design. Any positive-definite C is realizable as a centered real design: isometrically embed a Gram factor in the 3-dimensional subspace perpendicular to1 in R^4, then rescale according to the source's absorbed sqrt(n) normalization.

## 3. Independent reconstruction of the probability model

Use the source's rescaled Gaussian model, g~N(0,C). For support A and sign vector z, KKT gives

    beta_hat_A=beta*z+C_A^{-1}(g_A-lambda*z).

Sign recovery requires z_i beta_hat_i>0 and the inactive subgradient condition. With Z=diag(z), this is the intersection of

    u<beta*1,  u=lambda*Z*C_A^{-1}z-Z*C_A^{-1}g_A,
    |v|<=lambda, v=g_I-C_IA*C_A^{-1}g_A+lambda*C_IA*C_A^{-1}z.

Their Gaussian random parts have covariance zero, hence are independent. This reproduces source Eq(7)–(8) without assuming its supplemental algebra. For C_A=[[1,c],[c,1]],

    C_A^{-1}=(1-c^2)^{-1}[[1,-c],[-c,1]].

For either mixed sign vector z=(1,-1) or(-1,1), C_A^{-1}z=z/(1-c) and C_IA*C_A^{-1}z=0. Thus the inactive variable has mean0 and variance

    v_c=1-2c^2/(1+c)=(1-c)(1+2c)/(1+c).

The active random coordinates after standardization have unit variance, correlation c, and identical upper threshold

    h=beta*sqrt(1-c^2)-lambda*sqrt((1+c)/(1-c)).

Let S be this bivariate active probability and I the inactive probability. Mixed signs constitute half of the sign average; the other half contributes nonnegatively. Therefore psi_lambda^± >= S*I/2. No assumptions about the other signs are needed.

## 4. Rigorous uniform upper bound for orthogonality

At c=0, active coordinates and the inactive coordinate are independent for every sign vector. Hence, writing Phi for the standard normal CDF,

    psi_lambda^±(0|2,1)=Phi(1-lambda)^2*(2Phi(lambda)-1).

The normal density is everywhere <2/5 (use pi>25/8). Set x=1-Phi(lambda), so0<x<1/2. Integrating the density over an interval of length1 gives

    Phi(1-lambda)<Phi(-lambda)+2/5=x+2/5.

Let y=x+2/5 and A=9/5. Then

    psi_lambda^±(0)<y^2*(A-2y)<=A^3/27=27/125,

because the EXACT identity

    A^3/27-y^2*(A-2y)=(A-3y)^2*(A+6y)/27>=0

holds for y>=0. This bounds every lambda, not merely a sampled grid or a numerically optimized value.

## 5. Rigorous lower bound for the correlated witness

Take c=-49999/100000,beta=1,lambda=1/20. Since -1/2<c<0,

    h>sqrt(3)/2-1/20>17/20-1/20=4/5.

For x=4/5, exp(-t^2/2)>=1-t^2/2 and1/sqrt(2pi)>3/8 imply

    Phi(4/5)-1/2 >= (3/8)*(4/5-(4/5)^3/6)>1/4.

Thus Phi(h)>3/4. The union bound, valid regardless of correlation, gives

    S=P(X<h,Y<h)>=1-P(X>=h)-P(Y>=h)=2Phi(h)-1>1/2.

The elementary pi bounds used above follow, for example, from223/71<pi<22/7; the checker verifies the rational implications.

Exactly,

    v_c=149999/2500050000<3/50000.

Chebyshev therefore gives

    I=P(|v|<=1/20)>=1-v_c/(1/20)^2>1-3/125=122/125.

Multiplying yields

    psi_(1/20)^±(c_*)>=S*I/2>(1/2)*(122/125)/2=61/250.

Finally61/250-27/125=7/250>0. This completes the mathematical separation. Strict positivity of C and v_c ensures no hidden endpoint/equality exception. The source's support average does not change the result since every two-element support is equivalent.

## 6. Sustained attempts and falsifiers

Initial small-signal beta=.01 bounds gave a separation but faced the actual source's practical beta>=1 objection. That initial calculation is preserved in initial-small-signal-*; it is superseded for nomination by beta=1. Diagnostics at beta=.2,.5,1,1.5,2,3 are retained in exploration.jsonl. At beta>=2 this particular near-simplex mixed-sign lower bound fails to beat the optimized orthogonal curve; no all-signal theorem is claimed.

The mechanism is cancellation of the inactive mean for mixed signs near the full three-column simplex boundary. Its Schur variance tends to0 while the active covariance remains nonsingular. This preserves a fixed fraction of the unknown-sign average. The source's small-signal discussion considers a different active-block boundary and does not include this optimized full-criterion inequality in the sections read.

The ordinary proof uses only KKT/Gaussian projection independence, a global density bound, a cubic maximum and Chebyshev. These classical tools are explicitly transported above; there is no assertion that a generic theorem cannot apply. Classical Gaussian correlation inequalities alone do not order these two criteria, because both the mean and Schur variance change and the mixed-sign contributions behave differently. The strongest **substantiveness objection** is nevertheless that this short construction may be judged a routine consequence of the source's own Lemma2 once the near-simplex mixed-sign cancellation is noticed. Independent root adjudication is required; shortness is not being hidden.

Strongest **source falsifier**: the vague word “generally”, restricted intended p/k ranges, a strictly-positive-c restriction, or an unpublished/published beta or conditioning qualification could exclude this example from the intended conjecture. The actual preprint defines the family with negative c and no p>=4 or beta>1 restriction. It explicitly includes full-rank correlation optimization despite the SSD motivation. Still, the VoR must be read and compared, and no literal full-source resolution is certified here.

## 7. Prior art, access, chronology and disposition

No earlier lasso-source report was found by the all-date exact source/name screen. The dated full Omega/OpenAI inventories supplied by root (observed17:20UTC) give no exact lasso/Stallrich/source-ID paths under the refined regex; initial broad 'lasso' matching produced irrelevant ClassOverlap/associativity paths and is preserved rather than treated as relevant evidence. Both current raw main README/CONTENTS fetches returned HTTP200 around18:05UTC; neither mentions the target. They do not identify current head SHAs or provide a new complete tree, so registry freshness remains limited to the dated inventories plus those live index observations.

Live public searches found the source, its 2025 journal record, a 2025 Young thesis and a 2024 author-hosted comparison manuscript. The latter two actual bodies could not be retrieved: thesis endpoint returned bot verification HTML; the comparison endpoint returned HTML instead of a PDF. The publisher returned Cloudflare HTML, and web-reader attempts returned non-retryable redirects/errors. No challenge was solved or bypassed. Search excerpts are not substituted for reading those bodies. The closest followup and VoR gates therefore remain HOLD.

The only complete theorem here is the precise probability separation in Section2. It is NOT yet a cleared new attributed source discovery. No claim of worldwide novelty, no acceptance/count change, no Lean or paper work. Root should first resolve VoR/closest-body access and the intended maximum-summary quantifiers, then independently review the mathematics and the explicit classical-bridge objection before any formal investment.
