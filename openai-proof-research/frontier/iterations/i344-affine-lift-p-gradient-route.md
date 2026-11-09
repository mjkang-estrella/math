# I344 — a revised affine-lift route for actual p-harmonic gradients

2026-10-13. **Parent research route, not a completed theorem or acceptance.** The earlier I230/I241 work left uniform qualitative flatness and nonzero selected slopes unpaid. This note proposes addressing both by using the affine lift with its correct modified PDE, rather than falsely asserting it remains p-harmonic. The complete route and every cited interface need fresh independent validation.

## Target

For each n>=2, seek alpha_n>0 and C_n such that all p>=3 and every bounded weakly p-harmonic u on B1 satisfy

    ||Du||_(B1/2)+[Du]_(C^{0,alpha_n}(B1/2)) <= C_n osc_(B1)u.

A weaker initial target is the same bound for large p, since compact p intervals have classical estimates. Together with the stipulated infinity regularity, such a result would give actual gradient convergence at a power of ||u_p-v||_infinity, without quasiconcavity or assumed equicontinuity. Do not promote this route to either claim before closing its details.

## A. A uniform Lipschitz input and expanding-domain compactness

The primary Kotschwar–Ni paper, arXiv:0711.2291v1, equations (1.1)–(1.5) and Theorem 1.1, gives a local bound for w=-(p-1)log v for positive p-harmonic v. In Euclidean space, fix its auxiliary epsilon=1/2. Its displayed b_(p,n)=O_n(p), c_(p,n)=O_n(p^2), and C(n,0,p,R,epsilon)=O_n(p/R^2), so

    |D log v| <= C_n/R, p>=3.

For a bounded signed u, apply this to v=u-inf u+osc u (the constant case is separate). Then osc u<=v<=2osc u and the resulting local bound is |Du|<=C_n osc u/R. This is a reading of an older gradient estimate, not a new theorem or source stipulation. Check weak-solution regularity and the parameter normalization before using it.

Proposed compactness consequence: for the family of normalized p-harmonic functions (all p>=3), failure of a common Euclidean o(r) affine-fit modulus at radii r_i/dist(boundary)->0 produces expanding-domain globally Lipschitz limits. Pass to p_i->p_*<infinity or p_i->infinity. In the first case the limit is an entire p_*-harmonic Lipschitz function, hence affine by the usual fixed-p C1 estimate and scaling. In the second case it is an entire infinity-harmonic Lipschitz function, affine by the stipulated uniform C1,alpha theorem and scaling. Both contradict the bad unit-scale affine fit. This avoids asserting uniform gradient continuity from value convergence. A common flatness modulus is weaker and does not itself give a power rate.

Apply this to U(y,b)=u(y)+b. The lifts have a common Lipschitz bound and exact b increment. Euclidean o(r) approximation implies the source's cylinder goodness at any fixed positive parameter, hence b(s)->0. Every good cylinder slope P obeys |P.e_b-1|<=sqrt(lambda) and |P|<=L+sqrt(lambda). Thus selected slopes are uniformly nonzero without assuming Du itself nonzero. The source's geometric running maxima and inherited-fit compactness can now be tested on this family.

## B. Correct lifted viscosity equation

Write xi=e_b, Pi=I-xi tensor xi and epsilon=1/(p-2). The proposed exact lifted equation is

    H[DU,DU]+epsilon |Pi DU|^2 tr(Pi H)=0, H=D²U.       (L)

U is NOT claimed p-harmonic. To prove (L) at an upper test phi, phi_b=1. Add a small positive quadratic in b, minimize phi(y,b)-b in b, and obtain an upper test psi of u with Hessian K=H_yy-H_yb H_by/H_bb. The block difference H-diag(K,0) is positive semidefinite. The coefficient matrix DU tensor DU+epsilon|D_y phi|² Pi is positive semidefinite and its yy block is Dpsi tensor Dpsi+epsilon|Dpsi|²I. The original p-viscosity inequality for psi therefore implies (L). Let the regularizing quadratic tend to zero. At Dpsi=0 only H_bb>=0 is required. Lower tests use the reversed semidefinite comparison. This Schur-complement proof must be made precise, not replaced by restriction to a tilted hyperplane, which would introduce extra Laplacian terms.

## C. The exact selected-scale identity

Use the source cylinder normalization in N=n+1 dimensions, with P_i=c_i e_N, c_i in [1/2,L+1], lambda_i->0 and r_i>0:

    U_i(z_i+r_i(sqrt(lambda_i)x,t))
       =U_i(z_i)+r_i c_i[t+lambda_i V_i(x,t)].

The physical xi in these rotated coordinates is (a_i,b_i), |a_i|²+b_i²=1. Put beta_i=1/c_i, A_i=1-beta_i², S_lambda=diag(I,sqrt(lambda)), and q=(sqrt(lambda)D_xV,1+lambda V_t). Every test gradient satisfies q.xi=beta_i, because U_i has exact derivative 1 in direction xi. Therefore, on these tests,

    |Pi q|²=A_i+lambda(2V_t+|D_xV|²)+lambda²V_t².

After dividing (L) by its positive infinity normalization, the equation becomes

    D²V[(D_xV,1+lambda V_t)]
      +[nu_i+epsilon_i(2V_t+|D_xV|²)+epsilon_i lambda_i V_t²]
         tr(S_lambda Pi_i S_lambda D²V)=0,
    nu_i=epsilon_i A_i/lambda_i.                         (E)

The coefficient formula is an on-constraint identity, not a claim that all arbitrary jets satisfy q.xi=beta_i. The original (L) is globally elliptic. This distinction matters when applying general PDE compactness or extension arguments.

## D. Finite effective viscosity, including near-critical original slopes

For p_i->infinity, epsilon_i->0. The inherited local boundedness of V_i supplies bounded-gradient quadratic test contacts. Positivity of |Pi q|² at those tests should imply A_i>=-C lambda_i, so negative nu_i have liminf>=0. Thus a bounded subsequence nu_i has limit nu>=0.

The exact gradient constraint can also be written

    a_i.D_xV_i+b_i sqrt(lambda_i)V_(i,t)
       =(beta_i-b_i)/sqrt(lambda_i)=delta_i.

Since V_i is affine along the corresponding physical added-coordinate direction and is bounded on fixed boxes, delta_i stays bounded, with any limit delta=0 if a_i->0. If a_i->a, b_i->b and nu_i->nu<infinity, (E) tends to

    G[V]+nu tr[(I-a tensor a)D²_xV]=0,
    a.D_xV=delta.                                       (F)

If a=0 this is exactly the homogeneous/finite-viscosity equation already treated by the source or I236. If a!=0, write V=(delta/|a|²)a.x+W(x_perp,t). The Hessian annihilates a, so (F) reduces to the SAME isotropic equation G[W]+nu Delta_perp W=0, not a new anisotropic divergence equation. Inherited sheared fits for W need to be checked: the fitted slope along a is uniformly within C0 of delta/|a|, so enlarging original radius by a fixed factor and projecting should give the requisite all-center/all-radius fit with a finite new constant. The nu=0 source Liouville theorem or nu>0 I236 theorem would then make W, hence V, affine. The zero transverse-dimensional case reduces directly to W_tt=0.

This would close the finite-effective-viscosity branch even if the original gradient is near zero. Do not simply apply I236 to an arbitrary positive-definite anisotropic trace: the exact derivative constraint is essential to the proposed reduction.

## E. Large effective viscosity: a compact small-solution family

When A=1-c^(-2)>0 set e=epsilon A. Normalize at an e-ellipsoid about a fitted slope P=c e_N:

    U(z+L(sqrt(e)x,t))=U(z)+c L[t+e W(x,t)].

On the exact added-coordinate gradient constraint, (L) becomes

    D²W[(D_xW,1+eW_t)]
       +B(DW) tr(S_e Pi S_e D²W)=0,
    B(DW)=1+epsilon(2W_t+|D_xW|²)+epsilon² A W_t².       (S)

For arbitrary jets use max(B,0) to define a globally elliptic extension. It agrees with all physical test jets, since B=|Pi q|²/A>=0 there, and is polynomial near zero. At zero the coefficient is

    e_N tensor e_N + S_e Pi S_e.

Its spatial block is I-a tensor a; its time Schur complement is exactly 1. If |b|>=b0>0 it has uniform upper/lower bounds for 0<=e<=1. Here b=P.xi/c is bounded below by cylinder fitting and the common Lipschitz bound. All local jet derivatives are uniformly bounded for epsilon in [0,1], A in [0,1], and xi in this compact subset. Introducing an amplitude parameter as in I241 should give proportional C² estimates from Savin's small-solution theorem with one common threshold. Verify the extension, all parameter endpoints and quantitative derivative estimate.

If a lambda-bad scale has nu=e/lambda->infinity, use the strengthened running maximum at radius H=nu²r and coarse fit parameter eta=kappa lambda, kappa=O(nu^(2gamma)), gamma->0. To transfer A from the base fit to this coarse fit, use the source's QUADRATIC NORM comparison, not merely its O(sqrt(eta)) vector estimate:

    |c_coarse-c_base|<=C eta(1+log nu),
    |A_coarse-A_base|<=C eta(1+log nu)=o(A_base),

because A_base=nu lambda/epsilon and epsilon<=1. Thus e_coarse is positive and comparable to e, eta/e_coarse->0, and the ellipsoid lemma applies. Its fine-cylinder error is C e_coarse r²/H, whose ratio to lambda r tends to zero. The available domain, growing fit error and slope-norm comparison must all be verified. No wider-box compactness or uniform gradient bound is being assumed here.

## F. Remaining validation obligations

This route suggests that source power-decay and derivative extraction might extend to the entire actual-p family through the lifted equation. It is not yet a complete proof. Critical obligations are the expanding-domain flatness argument, exact viscosity lift, compactness with on-constraint jet identities, the projected fit contract, the max(B,0) small-solution family and its uniformity, and coarse A comparison. The source's geometric nonaffine-limit extraction is not assumed to apply until its hypotheses are explicitly met. Bounded p subsequences require classical uniformity on compact p intervals. If any step fails, retain the exact gap and do not claim the target.

Earlier credits: I230's quasiconcave result is a technical restriction; I236 finite-viscosity rigidity is independently proved but contribution-technical; I241 selected high-viscosity result is not independently gated. The present proposed new operation is the correct lifted, constrained effective-viscosity treatment that could remove the earlier nonzero-original-gradient selection gap. Existing partials are not additional findings.
