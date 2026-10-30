# Independent preliminary review: reflected Brownian affine crossing

Recommendation to root: **zero discovery credit; do not invest in Lean or a manuscript.** The supplied ordinary proof of the scalar equation (6) passes this review. A complete classical-method bridge supports exclusion as a routine adaptation, independently of the unresolved historical-priority question. This is an eligibility recommendation, not an acceptance, ledger change, or claim that the formula has already appeared in a read earlier source.

## Separate gates

| Gate | Finding |
|---|---|
| SOURCE | PASS for equation (6), arXiv:2603.27602v1 p8, with a>=0, b>0, mu>0 and standard variance-t Brownian motion starting at zero, reflected by the Skorokhod map. |
| MATH | PASS as an ordinary mathematical proof, with analytic details reconstructed below. Exact checker diagnostics support only the algebra. |
| SUBSTANTIVE | EXCLUDE as a routine classical characteristic-root/compensation and stopped-martingale adaptation. Full applicable bridge is given below; shortness is not the reason. |
| NOVELTY | HOLD / not cleared. Grandits same-model body remains unread; current registry heads, bodies, capped intervals and historical merge coverage are not cleared. No claim of worldwide priority or already-published exact subsumption. |

Counts are administrative only: 9 additional / 39 total, next 40. Root alone adjudicates, accepts, counts and stages. No credit for any auxiliary identity, endpoint observation, bibliography correction or checker.

## Actual source and literal limits

I read the frozen actual text bodies: Dumaz–Magaldi introduction through p9, especially the Skorokhod definition on pp3–4 and pp7–8; Mayerhofer published Section 2 including Theorem 1 and its proof; Salminen–Yor Section 2 Theorem 3, Corollary 5, and Section 3 Theorem 9 and its bridge proof; and the relevant reflected-diffusion construction of Magaldi's 2024 predecessor pp5–7. Conclusions below depend on these bodies, not catalogue or search snippets. Frozen PDFs and extracted bodies have exact hashes in provenance.json and freeze-before.json.

The target source is https://arxiv.org/abs/2603.27602 (fresh 200 at 2026-10-30T04:34:24Z); it still lists only v1, submitted 29 March 2026 09:47:24 UTC. The frozen PDF labels itself v1 and dates the document 31 March 2026. Equation (6) is an infinite series, despite the surrounding prose calling it an integral expression. With alpha=a/b it states

    P(exists t>=0: R^(-a)(t)>=mu+bt)
      = sum_{j>=1} (-1)^(j-1)
        [binom(j+alpha,j)+binom(j+alpha-1,j-1)] exp(-2mu*j*(jb+a)).

The source's immediately preceding Conjecture 1.4 asserts equality of the entire joint laws of two point processes for all a>=0. Its scalar byproduct is weaker. Equality of this one marginal crossing probability does not establish independent exponential gaps, any higher joint marginal, or that conjecture. No such implication is used here. The proof handles arbitrary real a/b>=0, not just integer values. The positive intercept and positive slope are the nondegenerate series domain reviewed; there is no claim for mu=0 or b=0. The source develops other statements for a>-1; those do not enlarge this assigned formula's reviewed drift regime. Absolute value of Brownian motion with nonzero drift is not substituted for Skorokhod reflection.

## Analytic attack and reconstruction

For fixed a>=0,b>0 define

    c_j=(-1)^(j-1) product_{k=1}^{j-1}(1+a/(bk)),
    lambda_j=2j(jb+a), r_j=2(a+jb), s_j=-2jb, v_j=1+a/(bj),
    u(h,x)=sum c_j exp(-lambda_j*h)[exp(r_j*x)+v_j exp(s_j*x)].

1. **Coefficient and derivative convergence.** The logarithm bound log(1+alpha/k)<=alpha/k gives |c_j|<=exp(alpha H_(j-1))<=e^alpha*j^alpha. On h>=mu, 0<=x<=h, the positive exponential is at most exp(-2(j-1)(jb+a)mu). For j>=2 its exponent magnitude is at least b*mu*j^2: the difference is mu*[bj(j-2)+2a(j-1)]>=0. The negative exponential is at most exp(-2j(jb+a)mu). Multipliers v_j are bounded by 1+alpha. A derivative of order p in h and q in x adds at most a constant times j^(2p+q). Thus each fixed derivative order has a summable Gaussian-in-j majorant on this entire unbounded wedge. The j=1 term is a separate bounded smooth term. This proves the stated uniform convergence and bounds; no uniformity over all parameters is needed or claimed.

2. **Regularity at the reflecting and moving boundaries.** A neighborhood of any compact part of the wedge with h>0 retains quadratic decay, even allowing x slightly outside [0,h]. The series therefore defines a smooth local extension there. Restricting to time <=T confines the stopped path to 0<=x<=mu+bT; localization supplies the ordinary smooth Itô hypotheses. No invalid derivative rule based merely on pointwise series convergence is used.

3. **Generator and Neumann boundary.** Both roots satisfy z^2/2-a*z-b*lambda_j=0. Therefore b*u_h+u_xx/2-a*u_x=0. At x=0, r_j+v_j*s_j=0 exactly. This is the correct reflected generator boundary condition, independent of the convention that relates L to semimartingale local time; the support property of dL suffices.

4. **Moving absorbing boundary.** At x=h the two exponents are -2(j-1)(jb+a)h and -2j((j+1)b+a)h. Since c_(j+1)=-v_j*c_j, each negative-root term cancels the next positive-root term. More explicitly, the Nth partial sum equals

       u_N(h,h)=1+c_N*v_N*exp(-2N((N+1)b+a)h).

   The remainder tends uniformly to zero for h>=mu by the same quadratic bound, proving u(h,h)=1. This also verifies no extra alternating sign, boundary constant or terminal term is missing.

5. **Stopped Itô identification.** Let tau be the first equality R_t=mu+bt. Continuous adapted paths and positive initial separation make tau a stopping time and {tau<infinity} precisely the requested crossing event. Applying Itô to u(mu+b(t wedge tau),R_(t wedge tau)) gives no drift or reflection term. The stochastic integrand is bounded on the stopped wedge, so its integral on [0,T] is square integrable with zero mean. Hence

       u(mu,0)=P(tau<=T)+E[1_(tau>T)u(mu+bT,R_T)].

   This needs neither an a priori probability interpretation or positivity of u, nor a uniqueness theorem for an unbounded-domain PDE, nor optional stopping at an unbounded stopping time.

6. **Terminal condition at infinity.** Skorokhod reflection gives exactly R_T=sup_(0<=s<=T)[B_T-B_s-a(T-s)], since the driving path starts at zero. Thus 0<=R_T<=2sup_(s<=T)|B_s| for a>=0. Reflection/Gaussian tails give P(sup_(s<=n)|B_s|>epsilon*n)<=4exp(-epsilon^2*n/2), a summable bound. Borel–Cantelli and ceil(T) comparison imply R_T/T->0 a.s. With h_T=mu+bT, both h_T and h_T-R_T tend to infinity. The positive-root exponent is bounded by -2(a+jb)[(j-1)h_T+(h_T-R_T)], and the negative-root exponent tends to minus infinity as well. On {tau=infinity} every fixed term tends to zero. The wedge majorant permits dominated convergence over j; the uniform bound for u permits dominated convergence in expectation. On {tau<infinity} the indicator eventually vanishes. These observations dispose of the terminal expectation, including the potentially delicate j=1 positive-root mode.

7. **Literal coefficients and a=0.** At x=0 the coefficient is c_j(1+v_j). Write P_j=product_(k=1)^(j-1)(1+alpha/k). Then binom(j+alpha-1,j-1)=P_j and binom(j+alpha,j)=(1+alpha/j)P_j. This yields exactly the source coefficients, including a=0 and j=1. For a=0 the result is 2 sum (-1)^(j-1)exp(-2mu*b*j^2), agreeing with Salminen–Yor Corollary 5. This check alone would not prove a>0.

No substantive gap was found in PROOF.md. In particular its bounded derivative claim, unbounded wedge use, local-time cancellation, telescoping rearrangement and tail argument survive adversarial checks. The independent checker.py proves nine symbolic algebra identities and checks 125 exact rational coefficient/truncated-boundary cases; it performs no simulation and is not a proof of convergence or stochastic identification.

## Complete classical bridge and substantive judgment

Mayerhofer's actual 2019 Section 2 starts with the reflected SDE, the Neumann generator domain, exponential test functions, characteristic roots and stopped Itô martingales for a fixed barrier. It does not state the target affine-barrier formula. Salminen–Yor's actual 2010 arXiv body supplies the driftless affine problem: Theorem 3 is Doob's wedge formula, Corollary 5 gives the exact a=0 crossing series and Theorem 9 computes finite-time distributions via Brownian bridges. It also does not state the a>0 target. Directly changing the drift of the absolute-value representation or citing either theorem as literal subsumption would be wrong.

Here is the complete applicable extension, which is the basis for the routine-adaptation decision. Append the deterministic coordinate h'=b to Mayerhofer's reflected generator; it becomes b*d_h+(1/2)*d_xx-a*d_x. An exponential mode exp(-lambda*h+z*x) requires z^2/2-a*z-b*lambda=0, and the two roots must be paired with coefficients in ratio -r/s to satisfy Neumann reflection. Seed the affine Dirichlet value 1 using a mode constant along x=h. This forces lambda=r and hence r=2(a+b), s=-2b, lambda=2(a+b). Its other root leaves one exponential residual on the absorbing line.

Cancel that residual with a new positive-root mode. If the current positive root is r and negative root is s=2a-r, matching the new boundary exponent requires lambda'-r'=lambda-s. Inserting lambda'=r'(r'-2a)/(2b) and lambda=r(r-2a)/(2b) gives roots r'=r+2b and r'=2a-r; choose the new positive root r+2b. Induction gives r_j=2(a+jb), s_j=-2jb and lambda_j=2j(a+jb). Neumann pairing then forces v_j=1+a/(jb), while absorbing-boundary cancellation forces c_(j+1)=-c_j*v_j. There is no unsolved recurrence or new theorem-strength probabilistic bridge left over. Gaussian series domination and the elementary Brownian sublinearity argument above validate the construction and identify its probability through the same stopped generator method.

Thus the actual additional work is a fully explicit compensation of elementary exponential modes in a classical reflected-diffusion boundary problem, with standard convergence/Itô estimates. No new structural coupling or joint-process mechanism occurs. I independently agree with the worker's **routine classical adaptation** classification under this campaign's explicit exclusion. This is a substantive judgment based on the exhibited bridge, not on the number of proof lines or the fact that the tools are old. A source's explicit open question can have a correct formula proof yet still fail this campaign's novelty/substantiveness threshold. Root may adjudicate that threshold differently; the MATH and SOURCE findings would remain separate.

## Bounded chronology and novelty limits

Salminen–Yor v1 was submitted 9 December 2010 (fresh abs lists v1 only); its extracted document has an internal 27 October 2018 date. That latter date is not used as a submission/publication date. Mayerhofer's published body records publication 18 October 2019. Magaldi's predecessor v1 is dated 21 November 2024; its reflected-diffusion construction is context, not a proof of the new scalar identity.

Fresh Crossref metadata for https://api.crossref.org/works/10.1080/03461238.2025.2587653 reports Grandits's online publication 18 November 2025 and print publication 9 August 2026. Online publication therefore predates Dumaz–Magaldi's March 2026 v1. Metadata does not establish a theorem's scope. I did not retry the denied publisher, request full/diff/raw alternatives there, or infer a duplicate proof from excerpts. The worker's reported acceptance date is not independently verified here. **The Grandits body remains a material HOLD.** The successful Crossref metadata request is a distinct legitimate route and is not body access or clearance.

A fresh bounded Crossref query for 'reflected Brownian motion drift affine boundary' returned five records; the exact JSON body, URL, UTC and hash are retained. It did not supply a verified same-formula body. Metadata-only leads (including an SSRN item and a ScienceDirect item) were not followed through denied routes and are not treated as exclusions. Query ranking and five records cannot establish absence of prior work. Existing cached registry path screens were read as limited inventories; denied GitHub routes were not retried and no parked merge-tree/capped interval was reopened. No current complete registry-history clearance is asserted. There is no significant new discovery investment or acceptance in this review.

The original publisher 403 and inherited access gaps remain preserved in frozen/http receipts and failures.json. No failed experiment was deleted. UTC retrieval time is from the actual runtime (30 October UTC, still 29 October in Los Angeles). Originals and private copies are checked before and after; administrative NEXT/ledger are snapshots only. Final manifest explicitly omits itself and its verification receipt, with a separately executed guarded verifier after final writes. Guard AS/RSS512MiB CPU210s wall230s caps remain unchanged; sampled RSS does not rule out unsampled transients.

No shared edits, git, browser, external messages/posts/uploads, MathDB edits, children, Lean or manuscript work were performed. Root alone owns any final disposition.
