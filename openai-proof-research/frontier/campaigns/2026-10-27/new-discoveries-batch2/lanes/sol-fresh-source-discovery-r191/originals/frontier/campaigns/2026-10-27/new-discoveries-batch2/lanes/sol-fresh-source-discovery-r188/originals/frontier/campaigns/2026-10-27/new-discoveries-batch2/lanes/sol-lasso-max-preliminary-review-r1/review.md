# Independent adversarial preliminary review

2026-10-29 UTC. Solo review; no children. **Overall HOLD; candidate credit 0.** Root retains the decision. Existing counts remain 7 additional / 37 total. Do not invest in a full formal certificate or paper on this review alone.

| Gate | Verdict | Exact meaning |
|---|---|---|
| Frozen input integrity | PASS | All 49 root-frozen originals matched before review; own byte copies made and verified. Final verification recorded separately. |
| Ordinary mathematical separation | PASS | The stated normalized Gaussian criterion exceeds 61/250 at the witness, whereas its orthogonal supremum is at most 27/125. |
| Preprint domain | Scoped PASS | Valid for the explicitly relaxed positive-definite correlation domain; no exact two-level SSD assertion. |
| Attributed intended source question | HOLD | Optimized-summary interpretation is plausible, but “generally” is not a universal quantifier. |
| Published VoR comparison | HOLD | No actual published body obtained; metadata and indexed snippets are insufficient. |
| Closest primary-body coverage | PARTIAL / HOLD | Actual graphical-comparison preprint read in relevant sections; thesis and distinct SSD/OA comparison remain unread. |
| Substantiveness / classical subsumption | HOLD | Short source-Lemma-2 specialization is a serious objection; no full published same-object subsumption theorem located. |
| Current registry novelty | HOLD | Bounded lexical screens and inconsistent-age mutable Omega observations do not establish current absence. |
| Formal endpoint | NOT REVIEWED / NOT PRESENT | Exact arithmetic checker is not Lean or a literal probability certificate. |

## Inputs and source adjudication

Read ancestor and batch AGENTS, ledger/prior-campaign-context/NEXT, candidate SUMMARY and complete discovery, source model and target extracts, and the actual frozen arXiv text around model/KKT, sign averaging, Section 2.2, Section 3, Lemma 2 and all Section 3.2 target context. The root freeze is the authority, not the candidate's narrower self-manifest. `candidate-copy/` contains all 49 frozen files, including failed-body HTML. The initial small-beta experiment is superseded; it is not a second outcome.

The [latest preprint](https://arxiv.org/abs/2303.16843) is v3, 24 April 2025. Sections 2.2 and 3 define maximum and integral summaries and absorb sqrt(n) into beta and lambda. The approximate domain permits arbitrary positive-definite correlation matrices, including negative c. Its Cp,k interval is wider than full-matrix positivity, but this witness lies in the positive-definite part. No p>=4, beta>1, or condition-number bound was found in the relevant preprint passages. The practical beta>=1 discussion does not exclude normalized beta=1. Global reflection halves the sign enumeration without changing weights, and permutation symmetry removes support dependence. Section 3.2 already reports fixed-lambda orthogonality failures; those receive no novelty credit. Its subsequent optimized-summary discussion supports investigating a maximum claim, but the final conjectural sentence uses fixed-lambda notation and “generally.” A universal optimized claim therefore remains an interpretation, not a source-certified quantifier. The integral summary is untouched.

That distinction is decisive: a theorem saying that some admissible C beats the orthogonal maximum is mathematically stronger than the source's fixed-lambda examples, but it does not by itself refute an informal claim about typical screening regimes. Nor does it refute the source's local-optimality theorem. At this witness c is far from zero. A missing conditioning qualification is conceivable, but none is stated in the relevant preprint domain; it must not be invented either to accept or reject the result. If the published intended claim is only heuristic, restricted to feasible two-level designs, or qualified away from this regime, exclude this nomination as a wording/domain correction.

The [Henry Ford repository record](https://scholarlycommons.henryford.com/publichealthsciences_articles/612/) supplies publication metadata but no manuscript download in the observed page. Author-site searches did not produce another actual VoR. I did not retry the previously challenged publisher/watermark routes, solve challenges, use institutional proxy hosts, or re-request the blocked thesis/download. Consequently journal-versus-v3 changes are **unknown**, not “identical.” The source's advertised broad ideal-structure claim in metadata is not a substitute for theorem-body review.

## Independent reconstruction of the certificate

Let C=(1-c)I+cJ, c=-49999/100000, p=3, k=2, normalized beta=1 and ell=1/20. In the normalized finite Gaussian model let g have covariance C. For support A and true signs z, define B=C_A^{-1}. Strict convexity of the lasso objective follows from C>0, so KKT is necessary and sufficient for its unique minimizer. A solution with this support and signs must have

    b_A = beta*z + B(g_A - ell*z), b_I=0.

Its active event is z_i b_i>0. Its inactive event is

    |g_I - C_IA B g_A + ell C_IA B z| <= ell.

Thus U=ell ZBz-ZBg_A must be less than beta*1, and the inactive scalar W is the displayed affine expression. Their random parts have cross-covariance zero because Cov(g_A,g_I-C_IA B g_A)=C_AI-C_A B C_AI=0. They are jointly Gaussian, hence independent. This proves the product formula; it is not an unsupported multiplication of correlated events. Strict active inequalities and non-strict inactive inequalities are correct finite-event conventions. All relevant Gaussian marginals are nondegenerate, so boundary choices have probability zero.

For each support, B=(1-c^2)^(-1)[[1,-c],[-c,1]]. For mixed signs, Bz=z/(1-c), and C_IA Bz=0. The inactive variance is

    s = 1-C_IA B C_AI = (1-c)(1+2c)/(1+c)
      = 149999/2500050000 < 3/50000.

The signed active covariance is ZBZ. Its diagonal is 1/(1-c^2), and its correlation for mixed signs is c (negative), not -c. Both standardized upper thresholds equal

    h=sqrt(1-c^2)-ell*sqrt((1+c)/(1-c)) > 4/5.

The active correlation need not be estimated: the union bound gives P(active)>=2 Phi(h)-1. Since exp(-t^2/2)>=1-t^2/2 and 1/sqrt(2 pi)>3/8,

    Phi(4/5)-1/2 > (3/8)(4/5-(4/5)^3/6) > 1/4.

The elementary strict constant uses pi<22/7<32/9. Hence active probability exceeds 1/2. Chebyshev gives P(|W|<=ell)>=1-s/ell^2>122/125. For either mixed sign the product therefore exceeds 61/125. Mixed signs constitute exactly half of all signs, or one of the two equally weighted global-reflection classes. The other class contributes a probability >=0; dropping it is sound even if its inactive mean is large and its probability tiny. Consequently the averaged witness exceeds 61/250. Every support has the same argument.

At C=I, full independence gives exactly

    f(ell)=Phi(1-ell)^2 (2 Phi(ell)-1), ell>0.

The standard density is everywhere <2/5, using pi>223/71>25/8. Put x=1-Phi(ell) in (0,1/2), y=x+2/5, A=9/5. Integrating the density over an interval of length 1 gives Phi(1-ell)<y, while the inactive factor is positive. Thus

    f(ell)<y^2(A-2y)<=A^3/27=27/125.

The final inequality follows either from derivative 2Ay-6y^2, or from (A-3y)^2(A+6y)/27 as the difference. This is uniform in ell. Pointwise strictness proves sup f<=27/125, **not** sup f<27/125. The weak supremum bound already yields

    sup_ell psi^±_ell(c) >= psi^±_(1/20)(c) > 61/250
       =27/125+7/250 >= sup_ell psi^±_ell(0)+7/250.

No numerical optimum is needed. For completeness, in this SPD q=1 model the probability curve is continuous, tends to zero as ell decreases to zero (the inactive event shrinks to a null set), and tends to zero as ell tends to infinity (ell z^T Bz eventually overwhelms the active signed sum). A positive value therefore implies an attained interior maximum. This supplies the max-versus-sup bridge without inferring it from pointwise strictness.

The complete matrix has eigenvalues 1-c,1-c,1+2c with 1+2c=1/50000. It is genuinely SPD, albeit ill conditioned. The checker independently obtains positive rational LDL pivots, rather than merely testing floating eigenvalues.

## Realizability and scope restriction

An explicit centered real design exists. Let Q be the 4x3 matrix whose rows are (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1), divided by 2. Then Q^TQ=I and 1^TQ=0. Put P=J/3 and

    R=sqrt(1-c)(I-P)+sqrt(1+2c)P, F=2 Q R.

Then F is centered and F^TF/4=C, with each column having empirical variance 1. For e~N(0,I_4), g=F^T e/2 has covariance C. Choosing physical coefficients beta_phys=beta/2 and penalty lambda_phys=ell/2 reproduces the source's absorbed sqrt(n) model exactly. This is a legitimate centered continuous Gaussian regression design.

It is **not** a balanced +/-1 design with V=I. For any row of three +/-1 entries, (x1+x2+x3)^2>=1; averaging would give 3+6c>=1, hence c>=-1/3. Our c<-1/3 violates that condition. Centering/scaling unbalanced two-level columns cannot rescue V=I. This does not invalidate the explicitly arbitrary-correlation relaxation, but it forbids promoting the result to an actual two-level experiment or SSD optimality counterexample. The manuscript must keep this distinction explicit. No assumption about all magnitudes or all signals is proved: beta=1 is fixed.

## Closest bodies and strongest substantive objection

Obtained the actual [graphical-comparison preprint, arXiv:2311.12685v1](https://arxiv.org/pdf/2311.12685v1), and read its introductory scope, Section 3.2, relevant maximum-comparison discussion in Section 4.2, and conclusion. It uses sign-recovery curves to compare named finite screening designs; its displayed OA comparisons involve expanded models and selected interaction scenarios. Those are not the present completely symmetric three-variable Gaussian optimization. No same-object optimized separation or universal theorem was identified in the sections inspected. This is a partial primary-body improvement, not clearance of its 2024 published version.

The distinct Akubire–Smucker SSD/OA comparison (`SSDs_vs__OAs_R1.pdf`) is **not** this graphical-comparison paper. Its frozen HTML failure remains a failure. The Young dissertation's indexed title and the advisor's/department's chronology identify a **2023** dissertation, rather than a 2025 dissertation merely because a search index gives a recent date. Its actual body remains unread. Either unread work might contain the mechanism or an optimized counterexample; this review does not infer otherwise from abstracts.

Strongest objection: specialize the source's own Lemma 2 to p=3,k=2 and z=(1,-1). Then z-sum vanishes, the inactive mean vanishes, and its variance tends to zero as c decreases to -1/2, while the active block stays regular. Gaussian continuity or Chebyshev keeps a positive mixed-sign contribution. A one-variable density bound controls the orthogonal maximum. This is the **full proposed routine bridge**, with its exact quantitative completion proved above. It demonstrates why the discovery might be judged too close to the source's elementary machinery.

The countercase is specific: the source's fixed-lambda failures and its active-block c->-1 small-signal example do not establish a bound on *every orthogonal tuning choice*. That requires both the different full-matrix boundary cancellation and the uniform cubic estimate. The source's own informal argument that small pointwise failures do not affect maxima does not supply this separation. I found no actual published classical theorem whose hypotheses and conclusion already cover the normalized sign-averaged maximum comparison; KKT, Gaussian independence, irrepresentability, and Chebyshev alone do not constitute such a printed same-object theorem. Therefore I do not declare EXCLUDE merely because the proof is short. Substantiveness remains for root adjudication after the source/closest-body holds, with this explicit bridge available for either decision.

## Registry evidence and formal cost

The supplied 17:20 UTC complete path inventories were inspected with a bounded lasso/Stallrich/source-ID screen. Exact-name absence is only lexical evidence; neither Blueprint nor filenames certify absence of an equivalent theorem. Live read-only API observations returned OpenAI head 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, matching that snapshot. Omega returned d7af67136d4478875778ac6e75eb5fbb8b3693a5. Crucially, the comparison from 70af5407 to mutable main is `behind`, behind_by=70673, ahead_by=0, with no forward files. The initial helper summary showing zero commits must **not** be read as “no delta.” It compares against an older history, not the 17:56 observed 75fa71fb advancement. Raw HTTP bodies and headers are retained; no full current Omega delta audit was obtained. No universal priority claim.

`checker.py` uses independent Gauss-Jordan elimination, full 3x3 LDL, all support/sign enumeration, a derivative-based cubic maximum plus a four-point identity test, and the rational Hadamard isometry. It passes. This differs from both the worker's tautological coefficient-vector check and root's explicit factor convolution. The worker failure is preserved in the byte copy; it does not contaminate the independently validated identity. No Monte Carlo or CDF optimizer contributes proof evidence.

A literal Lean certificate would need an actual finite Gaussian probability space, affine Gaussian laws/covariances, projection independence, event measurability, a precise KKT-to-unique-minimizer equivalence (if claiming lasso rather than the defined Gaussian criterion), CDF-density/integral bounds, Chebyshev with strict inequalities, and transport through both finite averages and the tuning supremum. Rational algebra is the inexpensive portion. No residual “Gaussian bridge” axiom or premise is acceptable. Library investigation is required to estimate cost; this is materially more than a cubic/rational formalization. No formal PASS is claimed.

Final recommendation: **HOLD, no count change and no full formal/paper investment.** Needed before reconsideration: actual VoR and journal-change comparison; actual thesis and distinct SSD/OA comparison bodies; defensible source evidence for a universal optimized-domain question rather than a typical-regime heuristic; root's substantive ruling on the explicit Lemma-2 bridge; a coherent bounded current-registry delta/body audit. Even if these clear, the integral criterion, exact SSD feasibility, all-signal behavior, and worldwide novelty remain outside the proved theorem.
