# I260 correctness review of authenticated I262

**Verdict: PASS.** This is a correctness verdict only. No contribution, priority, acceptance, or count-increment verdict is given. I250, I259 and I262 form one prospective finding. No author response or repair round was assumed.

The complete target is `frontier/iterations/i262-global-channel-stability.md`, 205 lines, SHA256 `1899a85fadb07ed0dd34b1396c31033c80d7a8b88b45455cdcb4f5116931cbfb`. Its identity matches the assignment and I262 authentication record. The stipulated revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; upstream results are assumed true. This review independently validates the deductions from them.

## Exact conclusion validated

For each fixed a>0 and 1/2<gamma<3/2, with r=(gamma-1/2)^(-1), w=(r+1)a² sech²(ra x), and normalized phi=c sech^(1/r)(ra x), the explicit eta,c_-,c_+ in I262 work simultaneously for every finite real channel number m>=2 and every measurable unit vector field v with ess sup |v-e0|<=eta for some constant unit e0. For W=w vv^T, the full moment deficit D is bounded between c_- J and c_+ J, where J is the stated weighted distance to constant rank-one channels. There is no spatial support or derivative assumption. The constants are independent of m, translations of the orientation perturbation, and its variation or oscillation.

The theorem remains local in orientation amplitude and uses the fixed scalar profile. It does not establish stability for arbitrary matrix potentials, complex orientations, multiple initially occupied solitons, or variable profiles. It asserts neither endpoint nor uniformity as gamma approaches an endpoint.

## Source contracts

The fully read pinned equality introduction, Theorem `thm:main`, supplies the precise measurable finite-matrix class, ordinary unnormalized trace, full negative moment sum, constant C_gamma, the displayed soliton equality class, and its sole scalar eigenvalue -a². The fully read matrix companion introduction, also Theorem `thm:main`, confirms the full-moment inequality with the same constant and measurable matrix hypotheses. Neither theorem is re-proved or audited here.

The external input is Hundertmark–Laptev–Weidl, *New bounds on the Lieb–Thirring constants*, author-hosted primary PDF, https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf . Independently retrieved full-PDF SHA256: `1e8aac1f8d388ae8e53dfeffd04736a0e00da6b26db6b618023a25d1ffb7f2c1`, matching I259. Pages 3–6 were fully read visually, including the complete presented proof of Theorem 3.1 and its supporting majorization and monotonicity lemmas. Its exact hypothesis is a nonpositive operator-valued V, trace class almost everywhere, with tr V_- in L¹(R). Applied with V=-B_w w ff^T on G=C^(m-1), this gives the claimed factor 1/2 and exponent 1/2. All of these hypotheses hold: the potential is measurable, bounded, nonnegative after changing sign, finite rank, and its trace integral is at most B_w M² integral w<infinity. No compact-support hypothesis is required.

Carlen–Frank–Lieb's scalar lowest-eigenvalue stability, arXiv:1301.5032v2, introduction and Section 2.1 through Theorem 2.2, was read as prior art, not used as a proof premise. No conclusion about matrix/vector overlap or worldwide novelty follows from this correctness review. MathDB is only a relevance lead; no score is asserted.

## Principal-direction centering

Write mu=w rho dx and Z=mu(R). The covariance S=Z^-1 integral vv^T dmu is positive semidefinite with trace one. The original amplitude condition implies |proj_(e0-perp)v|<=eta and v.e0>=1-eta²/2. Thus its top eigenvalue lambda satisfies lambda>=1-eta². In particular it is simple for this eta. For its unit eigenvector e with e.e0>=0,

    lambda |proj_(e0-perp)e| = |proj_(e0-perp) S e| <= eta.

The elementary relation |e-e0|<=sqrt(2)|proj_(e0-perp)e| proves the stated bound <=3eta. Consequently |v-e|<=4eta, v.e>0, and the global chart v=(sqrt(1-|f|²),f) exists measurably with the Euclidean essential supremum M<=4eta<=M_*.

Rayleigh maximization gives J=Z(1-lambda)=integral |f|² dmu=T. The off-diagonal covariance equation gives integral sqrt(1-|f|²)f dmu=0. Since 0<=1-sqrt(1-|f|²)<=|f|²<=M², vector Cauchy–Schwarz proves

    |integral f dmu|²/Z <= M⁴ T,
    V(f)=T-|integral f dmu|²/Z >=(1-M⁴)T>=T/2.

These are Hilbert-space norm estimates, not sums of absolute component sizes. They introduce no dimension factor. If T=0, positivity of mu and the positive chart give v=e almost everywhere; the stipulated equality case gives D=0.

## Global weighted coercivity and form domains

With A=d/dx+a tanh(ra x), direct factorization gives A*A=h+a² and AA*=a²+L_+, where L_+=-d²+[(r-1)/(r+1)]w>=0. The kernel of A is span(phi); polar decomposition, or the inverse of AA* on the range of A, shows h>=0 on phi-perp. This is nonnegativity at threshold, not a positive unweighted gap for h.

For u in H¹ perpendicular to phi, y=(AA*)^-1 Au belongs to H² and A*y=u. The form identity is

    q_h[u]=a² <y,L_+y>+||L_+y||².

It holds first on smooth vectors and then by the closed forms. Since u=-y'+a tanh(ra x)y,

    integral w|u|² <=2w0||y'||²+2a² integral w|y|²
        <=[2(r+1)+2(r+1)/(r-1)] q_h[u].

The inverse coefficient is exactly c_w=(r-1)/[2r(r+1)]. The estimate is global; no lower bound for w on a compact interval appears.

For the quadratic form Q, completion of squares with the free positive resolvent and the substitution F=phi g give

    Q(f)=min_g {integral rho|g'|²+integral w rho|g-f|²}.

The admissible g are the ground-state transformed form domain: phi g in H¹, equivalently the appropriate weighted H¹ closure. Constants are admissible. This specification makes the displayed minimum precise; it does not change the proof. Bounded measurable f gives w f phi in L² and a free-resolvent minimizer. The transformation and Poincare estimate extend by form closure, so f needs no derivatives or compact support. The spectral gap a² of h+a² on phi-perp gives Var_rho(g)<=a^-2 integral rho|g'|². Triangle inequality in L²(w rho), followed by the two-term Cauchy–Schwarz inequality, yields

    V(f)<=(1+w0/a²)Q(f)=(r+2)Q(f),   Q(f)<=V(f).

Hence Q(f)>=T/[2(r+2)]. Each identity and estimate sums Euclidean component norms without changing its constant.

All real physical operators here are self-adjoint on H² with form domain H¹: their potentials are bounded measurable multipliers. They decay in operator norm since they are dominated by a constant times w. Their essential spectrum is [0,infinity), and negative eigenvalues are discrete. The compressed form lives on the closed first-channel phi-perp subspace. These assertions require no spatial regularity of v.

## Analytic branch and explicit remainder

For M>0, b=f/M has Euclidean essential supremum one. For |z|<=rho0=1/[48(r+1)], the square-root branch is uniformly analytic, and H_z is a bounded analytic perturbation of H_0 on the common H² domain. The transpose continuation is essential and is used correctly.

At each x the perturbation acts in the span of the first coordinate and b(x), so its block estimates have no channel factor. The displayed estimates ||U_z||<=6w0|z|<=a²/8 and ||U_z psi||,||U_z* psi||<=6 sqrt(w0 T(b))|z| are conservative valid bounds. In fact <psi,U_z psi>=z² T(b) exactly, so the proposed factor 4 is harmless.

On the circle |lambda+a²|=a²/4, the unperturbed resolvent norm is at most 4/a² and the Neumann product is at most 1/2. Homotopy gives a rank-one Riesz projection and one analytic eigenvalue in that disk. On psi-perp, the distance of lambda to the unperturbed nonnegative spectrum is at least 3a²/4. The perturbed compressed inverse therefore has norm at most 8/(5a²)<2/a². Its Feshbach formula gives

    |lambda(z)+a²| <=[4+72(r+1)]|z|² T(b)
                     <=B |z|² T(b),  B=80(r+1).

The eigenvector has nonzero psi component, since otherwise the invertible compressed eigenvalue equation would force it to vanish. Thus this use of the scalar Feshbach identity is justified also for complex z.

Conjugation by diag(1,-I) makes the branch even. The order-two perturbation formula uses only the free transverse resolvent and gives F(0)=Q(b), where F(z)=(lambda(z)+a²)/z². Cauchy estimates on the even coefficients give, for |z|<=rho0/2,

    |F(z)-F(0)| <= B T(b) (|z|²/rho0²)/(1-|z|²/rho0²)
                 <=(2B/rho0²)|z|² T(b).

Consequently A0=2B/rho0² proves the claimed remainder |delta-Q(f)|<=A0 M² T. The estimate is relative to T, including when T is extremely small because the orientation perturbation lies far out in the tails.

For real z=M the spectral inclusion under a self-adjoint perturbation of norm <=a²/8 identifies this branch as the ground eigenvalue and gives |delta|<=a²/8. The order W<=w I independently gives delta>=0. Testing the normalized psi gives delta<=T. Thus the interval used in the moment derivative estimate is valid.

## Compression, HLW and the critical exponents

For a form vector (u,t) with u perpendicular to phi, discard the positive first diagonal correction. Since sqrt(1-|f|²)<=1, the cross term is bounded by 2 integral w |u||f^T t|. Set X²=integral w|u|² and Y²=integral w|f^T t|². Weighted coercivity and 2XY<=(c_w/2)X²+(2/c_w)Y² give

    q_H[u,t]>=(1/2)q_h[u]+||t'||²-B_w integral w|f^T t|²,
    B_w=1+2/c_w.

This also holds for complex test vectors by absolute values. The lower comparison is the direct sum of a nonnegative scalar compressed form and K_f=-d² I-B_w w ff^T. If mu_j are compressed eigenvalues, codimension-one min-max gives lambda_(j+1)(H)>=mu_j; form order then gives mu_j>=lambda_j(K_f) for negative variational levels, with zero padding when needed. Both directions are correct. Therefore the negative moments after the first are bounded by the full negative moments of K_f.

HLW gives sum sqrt(E_j(K_f))<=(B_w/2) integral w|f|². Since q=2gamma>1, sum t_j^q<=(sum t_j)^q. This is valid for each finite partial sum and extends by monotone limits. The proof avoids multiplying by the number of channels or eigenvalues.

Here p=gamma+1/2=1+1/r and w rho=c² w0^(-1/r) w^p exactly. With theta=1/(2gamma), both theta and 1-theta lie strictly between zero and one. Pointwise,

    w|f|²=(w^p |f|²)^theta (sqrt(w)|f|²)^(1-theta),
    theta p+(1-theta)/2=1.

Holder with conjugate exponents 2gamma and 2gamma/(2gamma-1) gives precisely the inequality in I262. Since integral sqrt(w)|f|²<=M² I_w and I_w=pi sqrt(r+1)/r, it follows that

    sum_(j>=2) |lambda_j(H)|_-^gamma
        <=(B_w/2)^(2gamma) [w0^(1/r)/c²] I_w^(2gamma-1)
                        M^(4gamma-2) T
        =N0 M^(4gamma-2)T.

Every factor of N0 and the exponent 4gamma-2 is correct. The a scaling also checks: N0 has units a^(2gamma-2), matching the conversion of T (units a²) to a moment (units a^(2gamma)).

## Final constants and stress cases

Since tr W^p=w^p, the stipulated scalar equality gives the fixed cost a^(2gamma). For 0<=delta<=a²/8, the derivative gamma t^(gamma-1) on t in [7a²/8,a²] has exactly the stated lower and upper bounds m_gamma and M_gamma, including gamma<1, gamma=1, and gamma>1.

Combining the ground remainder and threshold bound gives the proposed lower coefficient. The two smallness conditions in M_* respectively bound m_gamma A0 M² and N0 M^(4gamma-2) by m_gamma/[8(r+2)]. Together with Q>=T/[2(r+2)] this leaves c_-=m_gamma/[4(r+2)]. The upper bound D<=M_gamma delta<=M_gamma T gives c_+=M_gamma. The other conditions ensure the analytic disk and chart bounds. All constants are finite and strictly positive for fixed a and the stated open range.

The following adversarial regimes do not expose a defect:

- A constant rotation: centering gives f=0 and D=J=0, rather than treating a removable channel change as a positive defect.
- A small perturbation translated arbitrarily far into a soliton tail: T and J can be arbitrarily small, but both errors are bounded by a fixed small power of M times T. Neither coercivity nor interpolation contains a compact-interval minimum. The threshold term is controlled by w^p proportional to w rho, which is the necessary tail weight.
- Arbitrarily large finite m, changing transverse directions on many disjoint sets, or arbitrarily rapid measurable oscillation: only Euclidean norms, trace-one covariance, rank-two perturbation bounds, and the dimension-free HLW constant enter. No derivative of f is taken.
- An arbitrarily long or noncompact orientation perturbation: integral sqrt(w) is finite, and principal centering replaces the previous support-dependent variance lower bound.

At gamma down to 1/2, 4gamma-2 tends to zero and the smallness radius need not remain useful. At gamma up to 3/2, r-1 tends to zero and c_w degenerates. These are limitations already built into the statement, not endpoint deductions.

## Issues, repairs, and read limits

No mathematical repair is required for the authenticated theorem and constants. For expanded exposition, one may explicitly specify the transformed g form domain and spell out the compressed inverse, min-max directions, and Holder factorization as above; these are routine justifications of the stated argument, not changes to the conclusion or constants.

The complete reasoning is also recorded in `frontier/experiments/i260_uniform_channel_stability_proof/analysis.md`. Exact reads, retrieval failures, scope exclusions, and retained primary excerpts are recorded in the corresponding `reading-and-failures.md` and `input-authentication.json`, and `frontier/sources/i260_uniform_channel_stability_proof/literature.md`.

No other review, live I256–I258 output, live sibling output, giant history, numerical experiment, test, or research code was read or produced. No shared index, proposal, staging area, commit, or publishing state was changed. Review artifacts and primary excerpts are the only writes. Detached SHA256 identities accompany the handoff; the authentication JSON does not self-hash.
