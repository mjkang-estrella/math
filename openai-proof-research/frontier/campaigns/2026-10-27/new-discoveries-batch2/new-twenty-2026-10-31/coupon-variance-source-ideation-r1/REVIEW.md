# MathDB 374426: public full solution, zero discovery credit

Long's arXiv:2604.25108 **already proves the full positive-interior discrete stopping-time statement**, in both v1 and v2, Theorem 7.8. Recommend EXCLUDE_PUBLIC_FULL_RESOLUTION. Campaign count stays 52/60. No original candidate, Lean task, Pi diagnostic or execution authorization is proposed. This replaces r291's metadata-only analytic PARK as a research assessment; no frozen artifact was changed.

## Exact source gate and chronology

The literal raw record is r291/raw/374426.jsonl (SHA256 e9e2da5e57055457151011a2917972b686f51090ededa6a64373908b02f4c7b3). Its statement says the general case remains unresolved in its supplied source. That assertion conflicts with the actual manuscript, not merely with a newer registry label. Its first-stated year 2026 is also not the original conjecture date.

Doumas–Papanicolaou, ESAIM PS 20 (2016), 367–399, DOI 10.1051/ps/2016016, §1.3, Conjecture 2, p.371, asks for the minimum variance for every fixed pair of positive integers m,N. The paper's p.367 definitions require positive coupon probabilities and independent sampling with replacement. Equations (1.5)–(1.16), pp.369–370, distinguish dependent discrete negative-binomial completion counts from independent Poisson-clock Erlang times. Conjecture 1 is the separate asymptotic equal-probability assertion and is not the assigned finite endpoint. The original general-m conjecture and moment identities were read in the journal body.

Yu, J. Applied Probability 54 (2017), 655–656, DOI 10.1017/jpr.2017.23, Theorem 1 and its complete two-page proof were read. Receipt/revision dates are June 7 and October 17, 2016; publication online June 22, 2017. This proves m=1, even with a null coupon of fixed probability p0. It does not itself prove all m. Its cited earlier m=1 conjecture is Doumas–Papanicolaou 2012; that 2012 body was not separately retrieved here, and the full-m original is the inspected 2016 Conjecture 2.

Long v1 was submitted April 28, 2026, 01:31:07 UTC; v2 April 29, 2026, 04:26:45 UTC. Both actual §2 and §7 mathematical bodies were inspected, including Lemmas 7.5, 7.7 and Theorem 7.8. v1 has 22 PDF pages; v2 has 27. v2 clarifies integrability and differentiation assumptions in Lemma 7.5 and checks them explicitly in Theorem 7.8, adds finite rational moment Proposition 2.1, and adds asymptotic material. The full finite result was present already in v1. v2 is the latest version listed on the live abstract page, whose bytes match r291's cached abstract. No journal reference, separate correction, withdrawal or later version was located in the bounded exact-title/arXiv/correction searches. This is a bounded check, not certification that no such document exists anywhere. Unrelated asymptotic proofs in §§3–6 and v2 Appendix A were not fully read; they are not dependencies of the finite theorem. The v1 Appendix A/v2 Appendix B Hessian mechanism was read from the extracted appendix output, but supplies only a local result.

Thus the publicly available full theorem precedes the MathDB record's August 11, 2026 creation and September 20 modification, and this November 5 local-date research. The record's 'open' label and empty solutions array are not clearance. Exclusion rests on an actual matched proof, not shortness, catalogue absence or the recent title.

## All-hypothesis reduction and proof-body verification

Fix arbitrary integers m>=1,N>=2, positive real p_i with sum p_i=1. On iid draws C_k with P(C_k=i)=p_i define
T = inf{n>=0: for all i, #{k<=n:C_k=i}>=m}.
This is precisely the discrete T in Long §2 and the MathDB question on the source's intended interior. Its moments are finite: union-bound the events that a Binomial(n,p_i) count is <m; for fixed m and positive min p_i these tails are polynomial times an exponentially decreasing term. In particular there is no unproved exchange of infinities in the finite endpoint.

Add iid rate-one exponential interarrival times U_k independent of all labels. Put X=sum_{k=1}^T U_k. Independent thinning gives X distributed as max_i Gamma(m,rate p_i); conditioning on label-measurable T gives E[X|T]=T and Var(X|T)=T. Consequently
E X=E T, E X^2=E[T(T+1)], Var(T)=Var(X)-E X.
The discrete waiting times for different types are NOT independent. The Poissonized ones are. Omitting the minus-mean correction would change the objective.

Here is the source proof mechanism, restated to make the comparison auditable. Let F be the Gamma(m,1) CDF, phi=F'/F, D(y)=sum_{n>=m} y^n/n!. Then phi(y)=y^(m-1)/((m-1)!D(y)). Its logarithmic elasticity e(y)=m-1-yD'(y)/D(y) is negative and strictly decreasing: yD'/D is the mean of the law with weights y^n/n!, and its logarithmic derivative is that law's strictly positive variance. This verifies Lemma 7.7 for every integer m>=1, not just m=1.

For a nonuniform p take q_i(theta)=1/N+theta(p_i-1/N), 0<theta<=1. It remains positive on the entire closed segment, with a positive uniform lower bound. Put G(t)=prod_i F(q_i t), g=G sum_i q_i phi(q_i t), w=-partial_theta G. Direct differentiation gives
w/(t g)=(1/theta)(1/(N M(t))-1),
M(t)=(sum_i q_i phi(q_i t))/(sum_i phi(q_i t)).
Opposite ordering of q_i and decreasing phi gives w(t)>0 for t>0. With alpha_i proportional to phi(q_i t),
dM/dlog(t)=Cov_alpha(q_i,e(q_i t))<0.
The covariance sign follows explicitly from the pair sum (1/2)sum_{ij} alpha_i alpha_j(q_i-q_j)(e(q_i t)-e(q_j t)), which is nonpositive and strictly negative for nonconstant q. Therefore w/(t g) increases.

Normalize w(t)dt to a probability law nu, with mass a=int w>0. Its density ratio to the size-biased current X-law, whose density is t g(t)/mu with mu=EX, increases. The elementary independent-copy covariance inequality implies
E_nu[t] >= EX^2/mu = mu+Var(X)/mu >= mu+1.
The final inequality uses the exact identity Var(X)-EX=Var(T)>=0, not a conjectural variance order. Differentiating the corrected objective gives
W'=a(2 E_nu[t]-1-2mu)>=a>0, W=Var(X)-EX.
Gamma tails along the positive compact probability segment dominate the first two moment derivatives. At zero, G(t)=O(t^(mN)) and w(t)=O(t^(mN)) for theta bounded away from zero, so all displayed integrals exist. Continuity at theta=0 follows by the same uniform tail domination (or finite rational moments). Integrating the positive derivative proves Var_p(T)>Var_u(T) for every nonuniform interior p. At p=u equality is immediate. These are exactly Long Lemma 7.5 and Theorem 7.8, with all their hypotheses checked in v2. No independent discovery is asserted.

N=1 has the sole probability vector (1), T=m deterministically, variance zero. This trivial case completes the positive-integer N wording without adding substantive content. At a boundary p_i=0 with m>=1, T=infinity almost surely, so ordinary real-valued variance is undefined; assigning extended variance infinity is an explicit convention under which the interior minimum statement extends. We do not use an infinity-minus-infinity expression or a proof assistant's totalized integral to make a boundary counterexample. m=0 is outside the stated positive-m domain. Such conventions receive zero credit.

## Other concrete mechanisms and why no new lane endpoint survives

1. Exact finite moments. Long v2 Proposition 2.1 expands each nonempty coupon subset A and alpha_i in {0,...,m-1}. If p_A=sum_{i in A}p_i and |alpha|=sum alpha_i, then
E[T^(r)] = r sum_{A nonempty} (-1)^(|A|+1) sum_alpha ((prod p_i^alpha_i)/prod alpha_i!)(|alpha|+r-1)!/p_A^(|alpha|+r).
Here T^(r) is a rising factorial. r=1,2 and E[T^2]=E[T^(2)]-ET recover the actual variance. This follows by inclusion-exclusion in the Poissonized tail and exact Gamma integration; all sums are finite. It is already a public source formula, not a new discovery. No values, enumerations or searches were executed.

2. Smoothing/majorization. A proof of stochastic or mean minimization supplies no variance comparison. Even increasing both raw moments does not control their difference. Long §7.6 says full pairwise variance smoothing fails already at m=1; that assertion is not supplied there with an exact witness, so we have not independently certified a counterexample to Schur convexity. It is unnecessary for Theorem 7.8. The radial covariance proof above supplies the stronger-than-stochastic derivative centroid condition actually needed; it is a public proof of the full target.

3. Exact deficit-state moments. For remaining requirements d_i in {0,...,m}, let A={i:d_i>0}, r=sum_{i in A}p_i. With remaining draw count mean a_d and second raw moment b_d, iid conditioning and removal of the self-loop give
a_d=(1+sum_{i in A} p_i a_{d-e_i})/r,
b_d=(2a_d-1+sum_{i in A}p_i b_{d-e_i})/r,
a_0=b_0=0.
These follow from T_d=1+T_next; the inactive draws keep d unchanged. The variance is b_d-a_d^2 at d=(m,...,m). This is a sound finite reduction, but a statewise comparison to uniform does not automatically propagate after subtracting the squared mean. Long's active-clock identity, Proposition 7.2, similarly adds the variance of the path-dependent conditional mean to expected clock variances. For m=1 the uniform path contribution is deterministic; for m>1 it generally is not. No missing lemma here is being offered as a new endpoint: a complete public solution already makes searching this target ineligible.

There is consequently no credible *new* full route to hand off. No dormant Pi search brief or Lean semantic plan is warranted under the task's qualified-endpoint condition. The above probability semantics identify the genuine object without authorizing formalization of a known theorem.

## Registries, historical scope and limits

history-review.json retains hashes, matched contexts and exact readscope for the current campaign ledger, batch ledger, prior-campaign context, STATUS, and pinned OpenAI contents. The only direct coupon-family matches in those bounded documents are r291's reservation, the pending source-depth review and this assignment. r291 root integration was November 6, 02:04:18 UTC; this focused source task was launched 02:04:43 UTC. No accepted coupon-variance result was found in those documents. Different Doumas binomial monotonicity families are not coupon results. Prior public-proof/source-identity exclusions and routine-bridge exclusions apply, while historical accepted short/classical-ingredient results do not imply that every short proof is disqualified. Here the exact public theorem is decisive.

registry-review.json records current public GitHub page heads and commit dates. OpenAI current contents were fetched pinned to the observed head and scanned for coupon/Dixie/374426/Papanicolaou/2604.25108. No match. LeanPool's cached candidate tree at its still-current head and previously successful projects catalogue were scanned and had no matches. The attempted current pinned projects path returned 404, and leanpool.org DNS failed; neither was retried. Those are not clearance. Omega head changed since r291: only current root/commit metadata and bounded match scans were read, not the complete recursive theorem corpus. No matched registry theorem body was found and none is asserted absent globally. No GitHub API request was made; its inherited 403 denial remains respected. Registry gaps cannot undo the affirmative April public proof.

The actual read inventory distinguishes body reading, machine scans and downloaded/unread material. Journal/corrections/citing coverage is bounded and no worldwide-priority claim is made. No denied endpoint, alternate API, TLS bypass, browser/account action or contact was used. See http-receipts.jsonl and search-receipts.json.

## Integrity and resource receipt

All 99 frozen inputs matched before work; frozen-after.json must confirm the same hashes at handback. Only this assigned lane was written. No children, numerical searches, solvers, Lean, git or shared edits. Fetches and text conversion jobs completed synchronously or were explicitly reaped.

Resource qualification is PARTIAL, not a false PASS: the first two navigation/read commands had no explicit CPU/affinity/AS/wall prelude, and their output was oversized/truncated. Later local commands use CPU120s, AS6GiB and wall140s with at most two CPUs. One initial frozen/context batch used python without -I -B; later research scripts use -I -B. The bounded fetch script records per-request wall, affinity and sampled process maximum RSS; other text/hash batches were bounded but did not individually persist all resource telemetry. Managed search caps and bytes/hashes of its internal results are not exposed. These bootstrap/logging gaps are disclosed even though the mathematical exclusion is decisive. No live worker or child process is left at handback.
