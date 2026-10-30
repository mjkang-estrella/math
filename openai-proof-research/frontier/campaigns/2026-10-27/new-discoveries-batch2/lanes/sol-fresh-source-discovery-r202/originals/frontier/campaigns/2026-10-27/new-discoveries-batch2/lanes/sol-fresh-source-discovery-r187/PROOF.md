# Full ordinary proof of Dumaz–Magaldi's displayed formula (6)

Research derivation, not an acceptance or a proof of Conjecture 1.4. Proposed classification: routine classical exponential-martingale adaptation, zero discovery credit. Root owns adjudication. The mathematical argument below has no remaining source-formula premise.

Source: Laure Dumaz and Hugo Magaldi, *The spectrum of the stochastic Bessel operator at high temperature*, arXiv:2603.27602v1 (submitted 29 March 2026; document dated 31 March), p8, equation (6). The latest live abs page lists v1 only. Its conjectural byproduct is the formula below. Their Conjecture 1.4 asserts equality of two entire point-process laws; this proof does not establish that stronger statement. Ordinary standard Brownian motion has variance t. The source defines reflection by the Skorokhod map, not absolute value of Brownian motion with drift.

For every a>=0, b>0, mu>0, let R start at zero and satisfy

    dR_t=dB_t-a dt+dL_t, R_t>=0,

where L is continuous, nondecreasing, starts at zero, and increases only on {R=0}. Then

    P(exists t>=0: R_t>=mu+bt)
      = sum_{j>=1} (-1)^(j-1)
          [ binom(j+a/b,j)+binom(j+a/b-1,j-1) ]
          exp(-2mu j(jb+a)).                         (S)

For real upper argument the binomials here are the finite falling products divided by factorials; all displayed products are well-defined, including a=0. This closes every meaningful quantifier in the displayed source formula. The source's beta-Laguerre parameter restriction a>=0 corresponds to this drift regime; neither b=0 nor mu=0 is a convergence endpoint of its series as printed. At mu=0 the event is certain at time zero, but the unregularized series is not asserted.

## Construction and convergence

Put alpha=a/b and, for j>=1,

    c_j=(-1)^(j-1) product_{k=1}^{j-1}(1+alpha/k),
    lambda_j=2j(jb+a), r_j=2(a+jb), s_j=-2jb,
    u(h,x)=sum_{j>=1} c_j exp(-lambda_j h)
                       [exp(r_j x)+(1+alpha/j) exp(s_j x)].

Empty product c_1=1. For alpha>=0,

    |c_j| <= exp(alpha H_{j-1}) <= e^alpha j^alpha.

For h>=mu>0 and 0<=x<=h the positive-root exponential is bounded by

    exp[-2(j-1)(jb+a)h],

and the negative-root exponential by exp[-2j(jb+a)h]. For j>=2 these decay quadratically in j, uniformly on that entire unbounded wedge. The j=1 positive-root exponential is at most one. Each fixed number of derivatives in h and x adds only a polynomial in j (with constants depending on a,b). The series and its derivatives therefore converge absolutely and uniformly on the wedge h>=mu, 0<=x<=h. Smoothness locally across its boundary follows by the same quadratic domination on a small neighborhood of each point. In particular u and u_x are bounded on the whole wedge, and termwise differentiation, boundary summation, Itô's formula, and the expectations below are justified. No sign assumption about u is needed.

## PDE and both boundary conditions

Both r_j and s_j solve z^2/2-a z-b lambda_j=0. Consequently

    b u_h + u_xx/2 - a u_x=0.

At x=0, r_j+(1+alpha/j)s_j=0 term by term, so u_x(h,0)=0.

At x=h the first exponential in the jth term is

    c_j exp[-2(j-1)(jb+a)h],

and the second is

    c_j(1+alpha/j) exp[-2j((j+1)b+a)h].

The recurrence c_{j+1}=-c_j(1+alpha/j) cancels each second term with the next first term. Absolute convergence licenses this cancellation. The only uncancelled term is j=1's first term, equal to one. Hence u(h,h)=1 for every h>0.

## Identification with the crossing probability

Let tau=inf{t>=0:R_t=mu+bt}, with inf(empty)=infinity. By path continuity and mu>0, the event in (S) is {tau<infinity}. Apply Itô's formula to u(mu+b(t wedge tau),R_{t wedge tau}). Its dt term vanishes by the PDE. Its finite-variation reflection term vanishes because dL is supported on R=0 and u_x(h,0)=0. The stochastic integrand u_x is bounded, so on each finite time interval its stochastic integral is square-integrable with expectation zero. Therefore

    u(mu,0)=P(tau<=T)
        + E[1_{tau>T} u(mu+bT,R_T)]               (1)

for every finite T. This can equivalently be obtained by compact localization and bounded convergence, avoiding any global extension of u outside the wedge.

The Skorokhod formula at zero gives

    R_T=sup_{0<=s<=T} [B_T-B_s-a(T-s)]
         <=2 sup_{0<=s<=T}|B_s|.

Brownian sublinear growth implies sup_{s<=T}|B_s|/T ->0 almost surely. For completeness, reflection and Gaussian tail bounds make
P(sup_{s<=n}|B_s|>epsilon n) summable over positive integers n; Borel–Cantelli and comparison with ceil(T) give the asserted limit. Thus R_T/T ->0 a.s. On {tau=infinity}, h_T=mu+bT and h_T-R_T both tend to infinity. Each fixed-j term of u(h_T,R_T) tends to zero. The uniform absolutely summable wedge majorant above permits dominated convergence in j, and the resulting uniform bound for u permits dominated convergence in expectation. On {tau<infinity}, the indicator 1_{tau>T} eventually vanishes. The expectation in (1) tends to zero. Letting T tend to infinity proves u(mu,0)=P(tau<infinity).

Finally,

    c_j(2+alpha/j)
      =(-1)^(j-1)[binom(j+alpha,j)+binom(j+alpha-1,j-1)]

by their finite products. Substitution gives exactly (S). At a=0 it reduces to 2 sum_{j>=1}(-1)^(j-1)exp(-2mu b j^2), the classical driftless crossing formula. This reduction is an identity, not evidence for the nonzero-drift proof.

## Complete classical bridge and objection

Mayerhofer, *Three Essays on Stopping*, Risks7(4)(2019)105, DOI10.3390/risks7040105, actual published body §2/Theorem1/proof uses exponential test functions, the reflected Neumann condition, and stopped Itô martingales for a fixed upper barrier. Salminen–Yor, *On hitting times of affine boundaries by reflecting Brownian motion and Bessel processes*, arXiv:1012.2038v1, actual §§2–3/Theorem3/Corollary5/Theorem9 and proof, gives the driftless affine-boundary formula via Doob wedge reflection and diffusion bridges. Their published citation is Periodica Math.Hungar.62(1)(2011)75–101, DOI10.1007/s10998-011-5075-2; the 2026 source's bibliography lists different pages/issue. This bibliographic correction receives no credit.

The explicit bridge is: add the boundary height as a deterministic coordinate h'=b to Mayerhofer's generator; choose its two exponential characteristic roots with zero derivative at the reflecting boundary; start with the exponent that is constant at x=h; successively cancel each remaining boundary exponential. The cancellation forces lambda_j=2j(jb+a) and c_{j+1}/c_j=-(1+a/(jb)), exactly as proved above. The standard stopped-martingale argument then identifies the sum. This is a complete, elementary classical-method adaptation, not a missing theorem-strength lemma or a claim that either cited theorem literally states (S).

Strongest objection to discovery eligibility: this supplies only the explicitly conjectured scalar byproduct of the joint-law claim, using standard characteristic-root compensation and optional stopping. Under the user's exclusion of routine classical adaptations it should not be counted. No new process-law consequence, independent exponential gaps, higher-order joint matching, or separate helper credit is claimed. Grandits2025/2026 same-model affine-boundary material remains unread in full because the publisher returned403; a search excerpt is not sufficient to retire the formula as already publicly proved. Current registry body coverage is also incomplete. These are prior-art/eligibility limitations, not gaps in the displayed ordinary argument.
