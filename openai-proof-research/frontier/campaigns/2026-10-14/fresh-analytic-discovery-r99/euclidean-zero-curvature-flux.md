# The free z=0 specialization: an actual local Euclidean flux

Live author derivation, conditional only on the stipulated source367 universal tensor certificate, not an independent certificate audit. This local lemma is supporting research, not the full nonhomogeneous rigidity target.

Let u be harmonic on an open set D in R5, smooth to a regular one-phase boundary portion, with u=0, inward normal derivative1 there. Suppose |grad u|<=1. On {w=|D²u|>0}, put T=D²u, B=D³u, A=T/w, X=B/w, p=grad u. Use the source's rational polynomials f,U,K,M,P with the algebraic arguments g=0 and homogenizing parameter z=0. The certificate explicitly quantifies over these values. Write C_lijk=K_lijk-K_iljk, G_lijk=delta_li U_jk+C_lijk, a=29/50, and define

 h=w^a sqrt(f(A,p,0)),
 Z_l=w^(2a)[G_lijk X_ijk+w M_l].

The source's D rules are now EXACT Euclidean derivatives of coefficient polynomials: partial_l A_ij=X_lij-q_l A_ij, partial_l p_i=w A_li, partial_l g=0. Since u is harmonic, T and B have the required trace-free symmetry. Both the Laplacian contraction ΔT and the skew fourth-derivative contraction vanish. Thus the displayed source divergence identity specializes with all z terms deleted, without any spherical curvature or radial-null-vector assumption.

For every free vector ell the universal inequality reads

 w^(-2a) div Z + f|ell|² - (partial_l f+2a q_l f)ell_l >= epsilon_* |ell|².

Take ell=grad h/h. Since partial_l f+2a q_l f=2 f partial_l h/h, this proves

 div Z >= (1+epsilon_*/f)|grad h|².

The normalized coefficient domain {|A|=1,tr A=0,|p|<=1,g=0} is compact and f is polynomial. If F=max f on this domain, then F is finite and positive, and the coefficient is at least1+epsilon_*/F. This is a strict bulk gradient gain. No positive w^(2a) mass term survives z=0.

On a smooth boundary portion with H=-D²u(N,N)>0, the local Euclidean boundary-jet identities give exactly the same normalized odd-normal tensor V as in the source. The even-in-p symmetry removes the uncontrolled even-normal contribution in the contraction with N. Consequently the source boundary inequality gives

 N·Z+H h² >= delta_* w^(2a+1).

This is the Euclidean boundary remainder; its sign uses the INWARD normal. The derivation does not assert H>0 for all unnormalized global solutions without the separate gradient-bound and maximum-principle hypotheses. Nor does it handle w=0 by simply ignoring that set: any integrated application must supply admissible regularization/cutoff estimates there.

The local flux is not yet a global rigidity estimate. Integrating eta² div Z introduces -2 eta Z·grad eta. Z contains w^(2a-1)D³u, which is not controlled pointwise by grad h alone. The source compact-spherical cutoff proof does not dispose of the outer cutoff on R5. A scale-r curvature neck has boundary mass of order r^(n-2-2a), here r^(46/25), while ordinary stability measures r^(n-2). Turning the new boundary charge into a useful excess estimate therefore requires an actual bound on the outer flux and Hessian-zero errors, not just this favorable dimensional exponent.

For a full dimension6 target, an additional tensor or reduction mechanism remains necessary: the algebraic certificate is explicitly over R5. Extending matrices by deleting a direction is not valid for a generic R6 harmonic Hessian. No dimension5-only nomination is made.

## Stronger paid coercivity and a compact-cutoff estimate

The preceding obstruction based only on the proposition headline is superseded by an actual lower proof operation. Reading certificate-proof.tex450–563 shows that I is bounded below by

 c_w w²+c_z z²+c_l |ell|²+c_X |X|²,
 (c_w,c_z,c_l,c_X)=(673/18400,438907/12000000,2844869/24900000,3479389/7600000).

These are the source's exact weighted diagonal slacks, not new numerical tests. The z=0 geometric substitution therefore gives

 div Z >= |grad h|²+c_w w^(2a+2)+c_X w^(2a-2)|B|²+c_l w^(2a)|grad h/h|².

On the compact normalized coefficient domain, polynomial coefficients and their derivatives are bounded. Hence |Z|+|h grad h| <= C[w^(2a-1)|B|+w^(2a+1)]. This now controls ALL third-derivative directions, which the weaker displayed proposition did not do.

Suppose additionally that the classical solution satisfies Euclidean stability, integral_D |grad phi|² >= integral_boundary H phi², for compactly supported tests smooth from the positive side. For a smooth compact cutoff eta initially vanishing near {w=0}, apply stability to eta h. With inward normal N, the divergence identity is

 integral_D eta² divZ + integral_boundary eta² N·Z = -2 integral_D eta Z·grad eta.

Insert the interior and boundary inequalities, and subtract the stability expression for eta h. The result bounds the positive bulk and boundary remainders by

 2 integral_D eta (h grad h-Z)·grad eta + integral_D h²|grad eta|².

Young's inequality absorbs the full B and w remainders, using their strictly positive slacks. Thus

 integral_D eta²[w^(2a+2)+w^(2a-2)|B|²]
 + integral_boundary eta² w^(2a+1)
 <= C integral_D w^(2a)|grad eta|².                 (C)

Constants depend only on the fixed certificate. No outer boundary term has been thrown away: eta is compactly supported.

### Removing Hessian zeros

On a nonaffine connected positive component, |grad u|<=1 and Δ|grad u|²=2w² imply strict interior inequality |grad u|<1. The Hopf lemma at every smooth boundary point gives H>0, hence w>0 there. Thus in any fixed compact support, the Hessian zeros needing removal lie away from its free-boundary portion. Affine positive components contribute zero to every displayed curvature term and can be omitted.

The source's weighted Bochner proof applies locally without spherical curvature. For W_delta=w²+delta, ΔW_delta=2|B|² and |grad W_delta|²<=4W_delta|B|². Testing against a nonnegative smooth interior cutoff chi gives

 (4a-2) integral chi W_delta^(a-1)|B|²
 <= a^(-1) integral (Δchi)W_delta^a.

The right side is bounded in absolute value on a fixed compact set by smoothness. Since 4a-2=8/25>0, monotone convergence gives local integrability of w^(2a-2)|B|² on {w>0}. Smoothness and positivity of w near each compact boundary patch handle the remaining portion.

Apply (C) to eta vartheta(w/epsilon), with vartheta zero below1 and one above2. The extra RHS is bounded by a constant times integral_{epsilon<w<2epsilon} w^(2a-2)|B|² eta², which tends to zero by the established integrability. Dominated convergence handles the unchanged RHS and Fatou handles the nonnegative LHS. Thus (C) holds for every smooth compact eta, with the weighted B integrand defined as zero on {w=0}. This argument does not assign a geometric dimension to the zero set.

A standard power cutoff and Hölder now yield integral_{B_R∩D} w^q <= C R^(5-q), q=2a+2=79/25, provided the required solution and stability hold on B_(2R). Namely choose eta=zeta^(q/2), estimate the RHS by (integral w^q zeta^q)^((q-2)/q) times (integral |grad zeta|^q)^(2/q), and absorb. Smooth approximations to the power cutoff suffice. This is a scale-correct curvature estimate, not rigidity in dimension5: 5-q=46/25 is positive.

The full nonhomogeneous and dimension6 obligations remain. In particular a boundary neck-mass lower bound and a sharp excess-dependent RHS have not been established by (C).
