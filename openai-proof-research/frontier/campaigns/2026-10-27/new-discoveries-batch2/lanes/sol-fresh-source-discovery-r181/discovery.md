# Scope, source comparison and mathematical disposition

## Selection and historical screen

Read ancestor/batch AGENTS, ledger, prior context and NEXT; archived full bytes. The live ledger reports 9/39, next40. The r170/175/176/177/178 union was refreshed by SHA256 against actual present bytes, with new SUMMARY/discovery/PROOF/review/DECISION files added conservatively. There are 2,512 retained records, 11 additions/changes and no missing paths. Exact title, author, arXiv, DOI and statement aliases were searched before primary fetching, in early-screen.json, source-lead-screen.json, companion-screen.json, statement-screen.json and exact-alias-screen.json. Some broad matches are unrelated; none is erased. r111–113 originals remain in the union. No path/date exclusions or unproven echo deductions were used.

Initial entropy reconnaissance found the low-signal symmetric entropy question already investigated in r94 and explicitly recognized in r103/r111. No decisive new universal route was available, so it was not reopened and its October partial-family paper was not fetched. This is not one of the three exact statements selected below.

## 1. Poisson modified log-Sobolev mean constant

Original: Pablo López-Rivera and Yair Shenfeld, *The Poisson transport map*, JFA 288(10) (2025) 110864, DOI 10.1016/j.jfa.2025.110864. Actual latest arXiv:2407.02359v2 (6 February 2025), Definition 1.1, Theorem 1.5, Remark 1.6, printed pp2–4. Definition requires a positive log-concave density relative to a Poisson law, hence full support. For every such mu and every positive g in L2(mu), the question asks whether

    Ent_mu(g) <= E_mu[N] E_mu[Psi(g,Dg)],
    Dg(n)=g(n+1)-g(n),
    Psi(u,v)=(u+v)log(u+v)-u log u-(log u+1)v.

Chen and Wang's actual arXiv:2609.23994v1, Example 4.24, printed p40, already says this is false and shows the delta-at-zero obstruction: any constant C must satisfy C >= -log mu(0). Latest landing page lists only v1; printed cover date September22 and arXiv margin September21 are recorded as distinct source dates, not silently reconciled. Their Theorem 4.22 and proof, and Example4.24, were read. Original latest paper Theorem1.5 already supplies the matching upper bound. Combined, these publicly determine the constant exactly, so a new sharp-constant theorem would also be rediscovery.

**Complete admissibility bridge, not a new claim.** Let N=P+B with independent P~Poisson(1) and B~Bernoulli(1/2). Then mu(n)=e^-1(n+1)/(2 n!), n>=0. Summation gives mass1 and mean3/2. It has full support, and its density relative to Poisson(1) is (n+1)/2. The log-concavity identity (n+1)^2-n(n+2)=1 proves ULC for every n>=1. Here p=mu(0)=1/(2e), and -log p=1+log2>3/2 since log2=integral_1^2 dt/t>1/2.

For epsilon>0 choose g_epsilon(0)=1, g_epsilon(n)=epsilon for n>=1. It is strictly positive and bounded, hence L2(mu). Put m=p+(1-p)epsilon. Direct summation, including every n, gives

    Ent_mu(g_epsilon)=(1-p)epsilon log epsilon-m log m,
    E_mu[Psi(g_epsilon,Dg_epsilon)]=p(1-epsilon+epsilon log epsilon).

All n>=1 summands in the second line vanish. As epsilon decreases to0, the difference between the two sides with C=3/2 tends to p(log2-1/2)>0. Therefore some strictly positive epsilon violates the exact source assertion. This closes both the full-support-law and positive-test scope objections to the public delta test. It is a routine limit bridge to an already explicit public refutation, and earns zero credit.

checks.py additionally verifies epsilon=1/1024 by exact rational enclosures for e and logarithms, obtaining a gap greater than0.03269. It uses the atanh logarithm series with an explicit geometric remainder, factorial-tail bounds for e, and outward rational rounding only for reporting. The universal mathematics is the preceding ordinary argument; the one explicit check is a diagnostic, not a universality proof.

## 2. Poincaré interpolation question and existing universal route

Question attributed to Gautam Aishwarya–Liran Rotem, *New Brunn–Minkowski and functional inequalities via convexity of entropy*, Adv.Math.490(2026)110841, DOI10.1016/j.aim.2026.110841, Question1.6. Two actual primary companion bodies state its scope: for every dimension, even 1-strongly log-concave mu0,mu1, their quadratic optimal interpolation mu_t should obey integral f^2 dmu_t <= integral |grad f|^2 dmu_t for odd f. Original journal body was not obtained; do not upgrade this attribution to a source-certified literal quotation. Crossref is metadata only. One purported author URL redirects to a generic Technion page; another fails TLS verification. Neither is paper evidence; no TLS bypass was used.

Actual Han–Zhu arXiv:2607.10769v2, Theorem1.1, pp3–4, proves for all kappa_i>0 strongly log-concave endpoints, extended-valued potentials allowed, every t in[0,1], every smooth compactly supported f,

    Var_mu_t(f) <= ((1-t)/sqrt(kappa0)+t/sqrt(kappa1))^2 integral |grad f|^2 dmu_t.

Their introductory comparison pp4–5 explicitly identifies Question1.6 and parity. Body sections on coupled Bochner methods and the conclusion were inspected in the actual PDF; no independent audit of every elliptic regularity detail is claimed. Gozlan–Malamut–Waldspurger arXiv:2609.39252v1 supplies a second, stronger Talagrand route in Theorem2.1, with actual proof pp4–6 read early, not just its abstract.

The latter route uses the classical two-map Talagrand inequality: for convex gradients A,B on a common absolutely continuous source eta, if A#eta=mu is kappa-strongly log-concave, then integral|A-B|^2 deta <=2 H(B#eta|mu)/kappa. The paper recalls its proof from generalized-geodesic entropy convexity: 0<=H(nu_s|mu)<=sH(nu|mu)-(kappa/2)s(1-s)integral|A-B|^2; divide by s and send s to0. It handles non-smooth potentials in its stated framework.

Write T as Brenier map mu0 to mu1, Ft=(1-t)Id+tT. For finite-entropy nu relative to mu_t, pull it back to nu0=Ft^-1#nu and nu1=T#nu0. Their relative entropies both equal H=H(nu|mu_t). Let B be Brenier map mu0 to nu1; on X0~mu0 set X1=T(X0), Y1=B(X0), Y0=T^-1(Y1). Apply the two-map bound on source nu1 to B^-1,T^-1 and on source mu0 to T,B. This gives E|Xi-Yi|^2<=2H/kappa_i for i=0,1. Minkowski yields W2(mu_t,nu)<=sqrt(2H)((1-t)/sqrt(kappa0)+t/sqrt(kappa1)). Endpoints follow by usual Talagrand. The source proof explicitly treats finite moments, inverses, finite-entropy competitors and sharp Gaussian equality. Infinite entropy makes the inequality automatic.

Standard Talagrand linearization now yields the displayed Poincaré inequality; equivalently this Poincaré endpoint is already Han–Zhu Theorem1.1, so no new classical deduction is proposed. Setting both kappa_i=1 gives bound1. Reflection invariance of the endpoints and uniqueness of the optimal coupling imply reflection invariance of mu_t. An integrable odd test has zero mean. Thus the stronger public theorem covers the attributed question. Its all-function, nonsymmetric extension is also already public, so it cannot be nominated as new. The original-question-body access gap remains explicit but does not make the stronger actual public theorem available for rediscovery.

Chronology: Han–Zhu v1 July12, v2 September1 2026; Gozlan et al. v1 September30 2026; all precede this October30 UTC research. These are genuinely earlier public bodies, not later independent counterparts to our work. Crossref records the original journal issue April2026. No worldwide priority claim.

## 3. Stronger optimal endpoint-constant interpolation

Exact statement: for every pair of strongly log-concave endpoints in every dimension and t in[0,1], sqrt(CP(mu_t)) <= (1-t)sqrt(CP(mu0))+t sqrt(CP(mu1)). This must not be confused with the curvature constants in target2. Actual Han–Zhu Remark1.3 explicitly rejects this strengthening and PropositionA.1, pp32–34, gives a two-dimensional strongly log-concave counterexample. All three pages of its proof were read in text extraction.

It begins with uniform measure on (-pi/2,pi/2)^2, applies symmetric positive definite B_s=I+s[[0,1],[1,0]], and computes the split first Neumann eigenvalue lambda(s)=1-16s/pi^2+beta s^2+O(s^3), with beta>192/pi^4. The double-series expression for beta is controlled by a convergent positive tail, not a finite numerical spectral test. Consequently the midpoint gap for sqrt(CP) has positive r^2 coefficient beta/8-24/pi^4. A truncated Gaussian weight exp(-delta|x|^2/2) on the square gives uniformly convergent CP under bounded density comparison and makes all pushed-forward endpoints delta/(1+r)^2-strongly log-concave. B_r is their actual Brenier map, so the same midpoint is on the quadratic Wasserstein geodesic. This is an exact public refutation of the whole universal assertion. We do not claim an independently certified new witness or duplicate its perturbation work.

The all-measures one-dimensional result also cannot be rebadged: Gozlan et al. Theorem4.1 already proves convexity of Cp^(1/p) for every finite p>=1 along arbitrary monotone interpolation; its theorem and proof were inspected. Nor can the arbitrary-dimensional disconnected-support example in their Corollary5.2 be a new discovery.

## Strongest objections, gaps and disposition

The strongest tractable universal route in this screen is the two-map transport/entropy route above. Its actual full-scope theorem and proof are public before our work. A complete ordinary reconstruction would confirm prior art, not remove this decisive novelty objection. The Poisson positive/full-support bridge is complete but routine and publicly subsumed. No finite computation or changed terminology rescues either.

Exact gap for any future nomination: identify a different, fresh attributed statement with quantifiers not settled by these bodies and provide an ordinary full-scope proof. There is no remaining mathematical gap advertised here as an almost-complete candidate. Original Aishwarya–Rotem journal body access remains a source-comparison gap only. Current registry heads, capped historical intervals and missing merge trees remain PARKED; cached eleven-snapshot name search is not all-body or current novelty clearance. No denied repository/ScienceDirect/Google/IEEE/OpenReview/d-nb route was used or retried. An arXiv search429 was stopped; subsequent paper abs/pdf URLs were distinct known primary documents, not retries of the search or access-control bypasses.

No PROOF.md: there is no full new candidate. Root alone owns eligibility adjudication, investment and acceptance. No shared or git edits, children, messages, browser tabs, uploads or posts occurred.
