# r67: generalized plane-partition polynomial root monotonicity — unresolved

Solo research; discovery credit **0**. Root alone accepts. Campaign remains 7 additional / 37 total. No new full ordinary theorem, Lean development, paper, or acceptance nomination. No PROOF.md is supplied.

## Source selection and exclusions

Read ancestor and batch AGENTS.md, ledger.json, prior-campaign-context.json, NEXT.md, recent r60–r66 summaries and the polyomino acceptance prior limits before selecting. Read accepted-outcome scopes and relevant exclusions. No same target was located in the bounded previous-summary/source-label search. This is a polynomial family defined by the arithmetic function sigma_2, distinct from r66 Macdonald specialization ratios and from r68 finite-structure work. The prior Wright lanes concern Wright *functions*, not every work citing E. M. Wright; the route here is finite polynomial coefficient algebra, not a retry of that family.

Two source-paper leads received actual body screening, only ONE new full question selected:

1. **Heim–Neuhauser, Polynomization of Sun's conjecture**, Ramanujan Journal 70 (2026), article 58, published 15 July 2026, DOI 10.1007/s11139-026-01435-0. **Conjecture 1, printed p5**, with Definition (1.1)/(1.2). Latest arXiv record inspected: 2601.11226v1, 16 January 2026. Both actual v1 and published PDF read. Selected the published, surviving full scope below.
2. **Zhi-Wei Sun, A family of polynomials and related congruences and series**, FCNT2(2026)1–22, arXiv2505.02767v4 dated10 February2026, journal online11 February2026. Actual v4 definitions, Theorem1.1/proof, Conjecture1.1 and Section4 read. Rising-binomial q-log-convexity has previous-campaign/public overlap; no fresh claim or retry. Separate Section4 prime-square/prime-power congruences were deferred, not silently counted as fresh solved outcomes. The source's published web HTML exposes abstract/references, not a full journal proof body; exact v4–journal PDF identity is NOT asserted.

Search-only Ramanujan/group/irreducibility leads were reconnaissance, not adopted targets. No attempt to repurpose known endpoint corrections or old families.

## Literal selected scope

Let g(k)=sigma_2(k)=sum_{d|k}d^2. Define P_0(x)=1 and

    P_n(x) = (x/n) sum_{k=1}^n g(k) P_{n-k}(x),  n>=1.
    Delta_n(x) = P_n(x)^(n+1) - P_{n+1}(x)^n.

Published Conjecture1 asks BOTH:

* for every positive integer n and every real x>5, Delta_n(x)>0;
* for every integer n>=6 and every real x>=1, Delta_n(x)>0.

The v1 first clause prints x>=5; at n1 equality holds at5. The published source already uses x>5. That already corrected endpoint is not the research target or a discovery. Do not exploit n0 conventions: the target concerns the positive indices used in the source's definition of largest zeros.

## Nearest proof bodies read EARLY

* The same published paper Proposition2.1, Theorem1.3 and Section5.1: root monotonicity at x=1 is already proved using plane-partition log-concavity from index12 and finite initial inequalities. It is not a new result. The source explicitly says the all-real-x result would follow from the older polynomial Turan conjecture.
* Heim–Neuhauser–Tröger, Ann.Comb.27(2023)87–108, DOI10.1007/s00026-022-00604-4, actual publisher PDF. Read Conjecture2, Theorems1.3/1.4 and their Section4 induction proofs, Section7 discussion. Theorems give P_a P_b>P_{a+b} for x>5, and for x>=2 when a+b>=12. These are multiplicative inequalities, not adjacent nth-root inequalities. Conjecture2 is the still stronger all-x>=1, all-n>=12 polynomial Turan claim; it is not a proved bridge.
* Ono–Pujahari–Rolen, Adv.Math.409(2022)108692: actual NSF-hosted manuscript, Theorems1.1–1.3 and full Section3.1 proof. Its explicit major/minor-arc error comparison proves scalar PL(n) log-concavity from8820 with the remaining finite range checked. It concerns P_n(1), not a uniform error bound in arbitrary real x>=1. No uniform extension is inferred.
* Actual immutable Omega Problems dossier AND actual Lean certificate DawseyPartitionPolynomialDerivativeQuestionRefutation at observed6c27b0a… read before substantial algebraic investment. It refutes derivative separation of individual partition frequency polynomials using (1,1) versus (2). Its definitions and endpoint do not concern P_n above. No external Lean compilation claimed.

Registry path screens use saved Problems and actual Lean D5 trees, with their precise historical limits in provenance. The r57 D5 file is Blueprint markdown, not an actual Lean tree. No current-head clearance follows from these screens.

## Route A: logarithmic derivative and an exact Abel cone

Set A_n=n! P_n, so A_n has positive integer coefficients and

    A_n = x sum_{k=1}^n g(k) (n-1)!/(n-k)! A_{n-k}.

Define

    H_n(x)=(n+1)log P_n(x)-n log P_{n+1}(x),
    D_n(x)=(n+1)A_n'(x) A_{n+1}(x)-n A_n(x) A_{n+1}'(x).

For x>0, H_n'=D_n/(A_n A_{n+1}). Therefore an all-n>=6 proof that D_n(x)>=0 on x>=1, combined with the ALREADY PUBLIC H_n(1)>0, proves the entire second clause; it also proves the first clause for n>=6. The n1–5 remainder is finite polynomial algebra at x=5. This reduction has no missing analytic endpoint or interchange issue.

Write D_n=sum_j d_nj x^j. It has zero constant, degree2n-1 and leading coefficient5n(n+1)/2 (from the top two coefficients of A_n). Let S_nj=sum_{k>=j}d_nk. Finite Abel summation gives the literal identity

    D_n(x) = D_n(1) + (x-1) sum_{j>=1} S_nj x^(j-1).

The suffix cone is stronger than shifted-coefficient nonnegativity: its Abel representation becomes a polynomial with nonnegative coefficients after x=1+y. Its possible advantage is an unweighted tail-sum comparison, not a weaker hypothesis.
Hence the invariant S_nj>=0 for every n>=6 and every j>=1 is sufficient. Since d_n0=0, D_n(1)=S_n1; the nonzero positive highest coefficient ensures strict positivity for x>1. This sufficient invariant is NOT proved for arbitrary n.

All100 rows n1..100 satisfy the suffix invariant exactly. All100 also have nonnegative coefficients after x=1+y. Raw coefficient positivity is false: n4 has a negative x^2 coefficient; at n100 coefficients x^2 through x^5 are negative. Thus simply applying a positive-coefficient closure theorem to raw D_n is invalid.

Equivalent shifted formulation: B_nj=[y^j]A_n(1+y). Then

    [y^j]D_n(1+y)
      = sum_{a+b=j+1} ((n+1)a-nb) B_na B_{n+1,b}.

The remaining problem is a uniform signed convolution comparison for these particular arithmetic arrays. Positivity of B itself does not establish it. The exact expression

    [x^k]A_n = n!/k! sum_{s_1+...+s_k=n, s_i>=1} product_i g(s_i)/s_i

explains the divisor-sum input that an injection or domination proof must actually control. No injection, positive recurrence for S, or arbitrary-n domination has been found.

## Route B: antisymmetric bivariate kernel

Let h(t)=sum_{k>=1}g(k)t^k/k. The formal identity sum_n P_n(x)t^n=exp(xh(t)) follows directly from the source recursion. Coefficient extraction and Euler differentiation give

    W_n=(n+1)P_n' P_{n+1}-n P_n P_{n+1}'
       =x [u^n v^(n+1)]
          (h(u)v h'(v)-h(v)u h'(u)) exp(x(h(u)+h(v))).

Pairing i<j yields, with P_r=0 for r<0,

    W_n/x = sum_{1<=i<j<=n+1} (j-i)g(i)g(j)/(ij)
               * (P_{n-i}P_{n+1-j}-P_{n-j}P_{n+1-i}).

Full log-concavity would make these minors nonnegative. It is false at some early source indices for x=1, and the all-x tail version is precisely the older unresolved stronger conjecture. Exact checks of80 kernel identities retain both positive and negative contributions; ignoring the negative minor terms is not justified. A weighted aggregate cancellation bound, uniform in n and x>=1, is missing.

## Rigorous obstructions to overstrong routes

1. **Actual-source all-positive-x derivative monotonicity is false.** D_12(1/10) is exactly

       -3251339865240515317941865832544888033836631 / 10000000000000000000000.

   This lies outside the source x>=1 domain, so it is not a source refutation. The threshold cannot be discarded in a derivative proof.
2. **Positive arithmetic input alone is insufficient.** Take g1=1,g2=10,g3=1 (all later g positive arbitrarily). P2(1)=P3(1)=11/2, so H2(1)>0, but the unscaled derivative numerator W2(1)=-121/6. This blocks a generic positivity-only proof of the missing derivative invariant; it does not refute the sigma_2 source.
3. **The published Bessenrodt–Ono theorem does not by itself imply the target.** A sequence a_n in {2,3}, equal3 only at n7, satisfies a_i a_j>=4>3>=a_{i+j} at every positive pair. Yet a6^7=128<729=a7^6. Thus a full adjacent-root bridge needs additional structure. This countermodel is not a source counterexample or a new theorem claim.

## Exact validation and runnable bounds

Run `bash run.sh`. Every Python process is launched by the reused capped runner: AS512MiB, sampled process-groupRSS512MiB, group CPU210s, wall230s, sampling40ms, BLAS1. Caps were not raised. Sampled bounds do not exclude unsampled RSS transients.

* Integer A recurrence: derivative/shift signs for100 rows; Turan shifted-row diagnostics for99 rows. These are diagnostics, not all-index conclusions.
* Direct high-degree Delta coefficients: n1–5 at shift5 and n6–12 at shift1;12 finite polynomial certificates. No credit for finite cases, several already within the source's computations.
* Independent Euler-product construction product_k(1-t^k)^(-kx):17 coefficient rows through16 exactly match the integer recurrence.
* Independent scalar source recursion:1000 rational-value row comparisons and970 exact source inequalities over ten rational/integer parameters through n100.
* Independent binomial shift construction:19 derivative rows.
* Abel identity:300 exact evaluations;100 nonnegative suffix-cone checks (overlap with the same100 derivative rows, not new independent source instances).
* Kernel identity:80 exact rational cases with negative summands retained.
*300 exact derivative probes below1 expose out-of-domain negative signs, retained in independent.json.

No numerical roots/floating values are used in the assertions above. No mathematical run failed or exceeded caps; pdftotext emitted ICC/Lab profile warnings for the older publisher PDF, with readable extracted text retained. No cap-increase or hidden discarded witness.

## Eligibility, strongest objection, falsifier, precise gap

**Strongest objection:** no full ordinary proof/refutation exists here. The work isolates a plausible sufficient cone but has not proved its preservation. The x=1 theorem and generic log-concavity/root implication are public; reusing them, formalizing finite rows, or solving only x>5 would not be the requested full-source outcome. If a published uniform polynomial log-concavity theorem already covers these P_n, the entire endpoint may be routine; no novelty PASS is asserted.

**Source falsifier:** an exact n>=6 and real x>=1 with Delta_n(x)<=0, or any positive n and x>5 with Delta_n(x)<=0. A negative D_n, negative coefficient, or negative minor alone is NOT a source falsifier.

**Route falsifier:** a negative suffix sum S_nj would refute the proposed Abel cone, but could leave D_n and the source inequality positive. A negative D_n on x>=1 would refute derivative monotonicity, still not necessarily the source inequality.

**Precise gap:** prove S_nj>=0 for every n>=6,j>=1, or prove another uniform D_n>=0 / direct H_n>0 theorem on the whole x>=1 domain; alternatively construct a genuine in-domain source counterexample. No finite bound or asymptotic-with-uniform-tail theorem currently closes this gap.

Freshness HOLD persists. Shared GitHubAPI403 respected, no retry/bypass; no usable reset evidence in inspected inherited records. The15:49-observed6c27b0a… is NOT currentHEAD. Fetching current raw README provides no head SHA or complete-tree clearance. URLs, UTC, versions, hashes and inherited access limits are in provenance.json. No exhaustive literature or worldwide priority claim.
