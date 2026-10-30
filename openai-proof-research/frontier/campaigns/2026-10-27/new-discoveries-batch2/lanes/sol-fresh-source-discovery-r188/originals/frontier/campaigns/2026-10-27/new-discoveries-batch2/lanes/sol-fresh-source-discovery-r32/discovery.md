# Fresh target screened; no full resolution (credit 0)

## Precise surviving question

For every n>=2, every alpha in (0,infinity)^n, and every symmetric nonnegative weighted connected graph w, let mu=Dirichlet(alpha) on the closed probability simplex. Define

E(f,f)=sum_{x<y} w_xy integral eta_x eta_y ((partial_x-partial_y)f)^2 dmu.

Let lambda be the infimum of E(f,f)/Var_mu(f) over all nonconstant real polynomials, and lambda_2 the minimum over polynomials of degree at most two. The full question is whether lambda=lambda_2 for ALL these data. Equivalently, the symmetric inclusion process has gap_k=gap_2 for EVERY k>=2, with the same graph and parameters. No restriction to homogeneous parameters, small alpha, fixed graph, bounded degree or numerical tolerance is part of the target.

Sources actually read before the experiment:

* Current AIM608: https://raw.githubusercontent.com/MColbrook/AIM/8729eab98bafe409b66c5e39253bf56569a62327/problems/608-brownian-energy-quadratic-gap.md
* Current clopen OP-00279: https://clopen.solutions/OP-00279/
* Kim–Sau, latest arXiv2412.01489v2, Section1.3 Eq1.10 and Section8.1: https://arxiv.org/html/2412.01489v2 . Live record lists v1 December2 2024 and v2 June22 2026.
* Actual published Kim–Sau, CMP407:225 (September27 2026): https://link.springer.com/article/10.1007/s00220-026-05728-9 . The publisher HTML contains the body, despite a cookies_not_supported URL suffix. Published equation numbering differs: the two-particle identity is Eq1.7, not preprint Eq1.10. Published Theorem2.3 is a directional asymptotic, not the exact identity. Remark5.15 expressly leaves general vanishing directions outside the proof.
* Caputo–Quattropani–Sau, latest arXiv2609.10450v1, Section1.4.6, Eqs1.98–1.99: https://arxiv.org/html/2609.10450v1 . Its explicit Brownian-energy paragraph leaves this full question open. Live record has only v1 September9 2026.

This is a different source family from r30/r31 and the user's other exclusions. It is a retained research target, NOT a completed ordinary candidate, nomination, eligibility PASS, or global novelty claim.

## Early same-object/subsumption screen

The most dangerous apparent subsumer is Caputo–Quattropani–Sau Theorem1.1: arbitrary positive Dirichlet parameters and arbitrary block weights, degree-two spectral-gap reduction. Actual theorem and adjacent update definitions show it concerns KMP conditional redistribution, not the Brownian generator. Theorem1.12 treats a general class of stochastic exchange kernels, but Section1.4.6 explicitly computes the formal Brownian hidden operator and explains why it is not Markovian. This is a concrete same-object bridge failure, not a shortness judgment. Their positive-minimum-principle counterexample is ALREADY PUBLIC and is not our result.

A second concrete bridge test: on one edge with parameters a,b the Brownian Jacobi generator is x(1-x)d²/dx²+(a-(a+b)x)d/dx. Its degree-r diagonal/eigenvalue is -r(r+a+b-1). The conditional-resampling KMP operator has eigenvalue -1 on every nonconstant conditional orthogonal polynomial. Multiplying KMP by a+b matches degree one, but at a=b=1/4 gives degree-two rates 1/2 versus 3. Thus even a single scalar edge/time rescaling cannot identify the two operators on degree<=2, let alone on all degrees. Dirichlet-form comparison supplies inequalities, not the required exact spectral endpoint.

Other actual bodies inspected:

* Kim–Sau2303.16607v2, Theorems1.1/1.3, Corollary1.2 and degree/annihilation/min-max method: https://arxiv.org/html/2303.16607v2 . The sandwich (1 wedge alpha_min)gap_RW <= gap <= gap_RW closes only alpha_min>=1. This known entire parameter region is uncredited and cannot be used as a full solution.
* Kim–Quattropani–Sau2505.02400v1, actual Theorem1.1 and adjacent definitions: https://arxiv.org/html/2505.02400v1 . Its KMP lower comparison constant is not the Brownian degree-two identity; later2609.10450 supersedes its KMP status.
* Sau's current public research list: https://sites.google.com/view/federicosau/research . It lists the September2026 follow-up and published CMP paper, with no further matching proof located. This listing is not exhaustive body coverage of all author work.

AIM catalogue and clopen probability/classical-analysis listings were screened first. Gaussian U-conjecture (OP00287), uniform-convex Radon unimodality (OP00312), Gaussian hull intersection log-concavity (OP00268), and hypergraph shuffle gaps (OP00282) were inspected as alternative statements. Their basic known cases were not recycled. No full attack or proof clearance was performed for those alternatives; they are not claimed mathematically excluded. No source family was selected merely from an empty solution array.

## Exact mechanism attempted and remaining universal gap

For s a nonnegative integer composition of k, set D_s(eta)=eta^s/prod_x(alpha_x)_{s_x}. Direct differentiation gives

L_BEP D_s = sum_{x,y} w_xy s_x(alpha_y+s_y)(D_{s-e_x+e_y}-D_s).

The sum is over ordered distinct vertices; zero s_x terms vanish. These homogeneous monomials form a basis on the simplex for polynomials of degree<=k: homogenize with sum eta_x=1, and use homogeneity to extend any zero identity from the positive simplex to the positive orthant. Hence the finite SIP matrix is an exact source-polynomial representation, not an assumed conditional jet or a sampled approximation to the diffusion. Its reversible weights are

pi_k(s)=k!/(A)_k prod_x (alpha_x)_{s_x}/s_x!, A=sum alpha_x.

This classical finite representation is credited to the sources. The exact checker verifies normalization, detailed balance and coefficient identities for 103 monomials in two rational examples (360 directed balance checks). These are implementation checks, not a proof of the full conjecture.

A strict finite counterexample would suffice: rational n,w,alpha, integer k>=3, rational threshold t with gap_2>=t, and a degree-k nonconstant polynomial with Rayleigh quotient<t. One could certify the first inequality by exact positive semidefiniteness of E_2-t Cov_2 on the independent basis of nonconstant degree<=2 polynomials in eta_1,...,eta_{n-1}; the second uses exact Dirichlet moments prod(alpha_x)_{u_x}/(A)_{|u|}. That would be a full universal refutation, not merely a parameter instance of a positive theorem. No such pair of certificates was found.

For a positive proof the missing step is the uniform comparison gap_k>=gap_2 for every k>=3, every graph and every positive alpha. Finite-dimensional intertwining only gives the opposite ordering after enlarging polynomial spaces. A directional alpha->0 limit cannot supply equality at positive alpha. No new coupling, operator comparison, or induction closing that step was obtained. In particular, there is no hidden claim that checking k<=5 settles the question.

## Executable checks and candid limits

`bash run-checks.sh` runs exact and floating checks under hard512MiB AS, bounded CPU/wall, BLAS1. No enumeration beyond the explicit composition/state caps occurs.

* `check.py`: exact rational algebra/detailed-balance checks above. It also verifies a KNOWN-type degree-one failure on Q4, alpha=1/1000. For two particles the Hamming-distance chain has birth2alpha(4-r), death2alpha*r except death at r1 is2(alpha+1). Its stationary probabilities are (1+alpha)/(1+16alpha) at0 and alpha*binom(4,r)/(1+16alpha) otherwise. Trial h=(0,0,1,2,3) has Rayleigh quotient7112/3900875 < gap_1=1/500, strict gap2759/15603500. This is consistent with the already-public phenomenon that degree one can fail; it DOES NOT refute degree two and earns no credit. Pullback to polynomials is through the source duality/basis, not a new theorem being nominated.
* `probe.py`:240 seeded connected weighted graphs n3..6, k2..5, at most252 states. No putative gap_k<gap_2 by the diagnostic1e-6 relative threshold. All240 also had gap_2=gap_1 within tolerance: this probe missed the specifically two-particle regime.
* `targeted.py`:six rows for torus C4xC4 and hypercube Q4 at alpha .001,.03,.3, k1..3, at most816 states. **C4xC4 is isomorphic to Q4**; these are two implementation presentations of ONE geometry, not six independent geometric tests. At .001, gap_2 approx .00168893928253 < gap_1=.002 and gap_3 agrees with gap_2 numerically. Still no violation or proof. Roundoff-scale discrepancies, including ratios below1 by6.6e-9 in the small probe, are not mathematical counterexamples.

No large search is justified by these results; missing all-degree mechanism is the obstacle. No PROOF.md, Lean code/certificate, paper, acceptance or credit is produced. A literal full Lean plan would be premature. If an exact witness is later found, the source endpoint must use actual Dirichlet moments, generator/form and quadratic PSD certificate, not just an uninterpreted matrix comparison. Independent root ordinary review must precede large Lean.

## Current registry/chronology evidence and access limits

All HTTP UTC dates, exact final URLs, SHA256 and failures are in http.json. Registry-screen.json records inherited complete scoped trees plus economical live-head refreshes.

* Omega dev advanced from f9745e6af0bfa02fc8c61013f48003ce3e4f9606 to953086aaf8dbba50658ea758d655753a486ce219, observed10:50:05UTC. The compare response has4 commits/5 added paths, all dyadic solenoid time separation; latest merge10:45:48UTC. D5 adds one Lean path; Problems subtree hash remains3e88018474e7f9e35654ca9061b7aaa9993e3088. Main remains d7af67136d4478875778ac6e75eb5fbb8b3693a5,69-entry complete tree inherited. Cached D5(12497)/Problems(1544) were complete at the old head. The complete scoped inventories plus exact small delta give current scoped path coverage; the truncated whole-dev root is NOT full repository coverage.
* OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, AIM8729eab98bafe409b66c5e39253bf56569a62327 and Countdbf673741a54c7dc9d88a6aec0e8148a538f4a3a match inherited complete scoped inventories. Pinned OpenAI theorem truth is accepted; no upstream audit attempted.
* No matching public resolution found in bounded path/title searches or the primary/follow-up bodies read. Absence of a path hit is NOT semantic novelty clearance. No exhaustive registry body audit, thesis corpus, MathSciNet/zbMATH, or worldwide priority claim.
* Several mistakenly guessed nonexistent HTML versions returned404, including Kimv3 and KS2024v3. Actual current versions were then obtained from live source records; these were not403/challenge bypasses. An incorrect Sau URL redirected to a login page; no sign-in attempted. The correct public research page was discovered through search. Caputo author URL failed TLS certificate verification; verification was not disabled and that route was not retried. An initial read-only extraction attempted unavailable bs4; replaced with standard-library HTMLParser. No403/429 retry loop or browser tab was used.

Strongest objection/falsifier: this lane has NO all-degree inequality and NO strict degree>=3 source counterexample. All retained explicit calculations are classical implementation checks or already-known phenomena. No result should be accepted or counted from this packet. The full target remains unresolved here. Root owns acceptance; count0, campaign5/30 additional and35/60 total unchanged.
