# Compatible reduction at the entire K369R134 scope

This is an operation-level contribution comparison, conditional on correctness of the submitted candidate. It is not a separate correctness verdict, repaired author proof, weaker replacement, or downstream manuscript. The unchanged scope has SHA256 `690e3b4b2314ac7009a8cf60b24c89961b2e6e01dd21543904156b851e304a88`; the actual submitted proof has SHA256 `cab6bb9b3fdb27a126cb6a214f52b83936526449c823ac345fe3010aa2dd6700`.

The conclusion of this comparison is that an existing nonlinear moment theorem supplies the important smoothing operation, at the actual bounded measurable signed-potential scope. The remaining reciprocal and Fourier calculations compose with it uniformly. This is positive evidence for TECHNICAL, rather than an inference from unsuccessful novelty searches.

## 1. Paid source operations and the precise remaining question

At the stipulated pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, family369 Section04 constructs the Green-chain kernels, proves Poisson-section smoothing, sums the tails by a contraction, and controls their integrals. Section05 proves the reciprocal result for every nonnegative bounded subcritical disk potential, every interior normalization point, and also interior reciprocal inertia. Its proof includes the bounded regularization, positive node elimination, quadrature refinement, removal of regularization, boundary passage at compact support, and increasing support limit. All of those operations are paid.

For signed potentials, replacing every factor by its absolute upper bound Q retains the analytic estimates and existence. It does not, by itself, retain reciprocal inertia. Conversely, the alternating coefficients produced by a negative node update do not prove that some different compatible source or classical composition is unavailable. The question is whether a whole quantitatively positive radial moment class can be handled after the strongest such composition.

At the center, rotation invariance makes K_e(0,s)=k_e a scalar. The problem is therefore the sign of the nonzero Fourier coefficients of f_e=1/N_e. This is a useful reduction with a real loss of scope: no off-center signed conclusion follows by multiplying by a nonconstant positive boundary function. The reduction does not itself settle the infinite-mode problem.

## 2. A primary nonlinear moment theorem that applies to arbitrary bounded v

The decisive antecedent is Barry Simon, *A new approach to inverse spectral theory, I. Fundamental formalism*, Annals of Mathematics150 (1999),1029–1057, Theorem2.1 and its proof through Lemma2.2, pp1036–1040. The published primary body was acquired and read. For a real half-line potential U in L1(0,infinity), it supplies a Laplace amplitude A and, writing H(t)=integral_0^t |U(s)|ds, the estimate

    |A(t)-U(t)| <= H(t)^2 exp(t H(t)),
    m_U(-z^2) = -z - integral_0^infinity A(t) exp(-2zt)dt,

for real z>||U||1/2. The proof expands the resolvent and writes each free Green factor as a positive integral over a path length; its region estimate gives the quadratic error. No smoothness of U is required in the theorem. The printed difference estimate(2.4) has a known typographical issue, explicitly noted in Daudé–Macià–Meroño–Nicoleau, arXiv:2402.06321v3, Section4.1 footnote4. The estimate used here is Simon's(2.1), proved by(2.7); the difference estimate is unnecessary.

For the frozen potential, set a=eQ and use the d=2 radial Liouville change r=exp(-t):

    U(t) = -e exp(-2t) v(exp(-t)).

Then U is real, bounded, measurable, integrable, and

    ||U||1 <= a/2,
    H(t) <= a min(t,1/2).

Thus, with F=A-U,

    |F(t)| <= a^2 t^2 exp(a t/2).                         (R1)

Taking a below a fixed absolute constant makes Simon's representation valid at EVERY integer n>=1. There is no potential-dependent high-frequency cutoff.

For clarity, the radial solution y_n(r), normalized by y_n(1)=1 and regular at0, becomes u_n(t)=y_n(exp(-t)). It satisfies

    -u_n'' + U u_n = -n^2 u_n.

For n>=1 this is the square-integrable half-line solution and the Dirichlet-to-Neumann eigenvalue is lambda_n=-m_U(-n^2). Hence

    h_n := n-lambda_n = -integral A(t) exp(-2nt)dt,
    h_n = e integral_0^1 v(r) r^(2n+1)dr + b_n,
    b_n = -integral F(t) exp(-2nt)dt.                       (R2)

The radial transformation and the DtN/Weyl relation also appear explicitly, with their proofs, in Daudé–Macià–Meroño–Nicoleau, *Stable factorization of the Calderón problem via the Born approximation*, arXiv:2402.06321v3 (22June2026), Sections2.3 and3.1–3.3, equations(2.13)–(2.15),(3.1)–(3.8). Their Theorem3.2 states the same quadratic amplitude estimate. The fixed-energy continuation of Macià–Meroño–Sánchez-Mendoza, arXiv:2501.05889v2 (17January2026), Sections4.2–4.3 and the proof of Theorem4.4 in Section6, points directly back to these estimates. Its less precise general fixed-energy bound is not substituted for the sharper zero-energy estimate.

The half-line representation is NOT invoked at n=0: the regular zero mode need not be square-integrable at infinity. This limitation is harmless but must be kept explicit.

## 3. Uniform differences and the low modes

With Delta b_n=b_(n+1)-b_n, equations(R1)–(R2) give, for n>=1 and every fixed nonnegative integer j,

    |Delta^j b_n|
      <= a^2 integral_0^infinity t^2 exp(-(2n-a/2)t)
                                      (1-exp(-2t))^j dt
      <= C_j a^2 n^(-3-j).                                (R3)

Indeed 1-exp(-2t)<=2t and the last integral is bounded by a constant times (j+2)!/(2n-a/2)^(j+3). All constants here are absolute for fixed j and a below one absolute threshold. This proves the same all-potential, all-mode difference estimates as the author's longer constant-potential Riccati/Catalan route. It neither differentiates v nor assumes it has boundary values.

The low modes have the same quadratic bound by the source Neumann majorant, or directly as follows. The unperturbed radial Green inverse is

    g_n(r,s)=(rs)^n integral_max(r,s)^1 u^(-2n-1)du.

It is nonnegative and <=g_0. On radial bounded functions the latter has norm1/4. Therefore

    ||y_n||infinity <= (1-a/4)^(-1),
    ||y_n-r^n||infinity <= (a/4)/(1-a/4).

The radial Wronskian identity gives h_n=e integral v(r)r^n y_n(r)r dr, also for n=0 with the usual zero-mode interpretation h_0=-lambda_0. Consequently b_0=O(a^2), and every fixed low b_n is O(a^2), uniformly in v. This uses only ordinary resolvent contraction and an integral identity; there is no unproved analytic-continuation assertion at spectral zero.

In the arclength convention of the frozen statement,

    Rhat_e(n) = h_|n|/(2pi),

because Lambda_0-Lambda_e is convolution by R_e with ordinary angular measure. This also follows directly from angular integration in the source's Green chains.

Let B_e=R_e-eR_1, where R_1 is the first coefficient, not the value at e=1, and w=2-2cos(theta). Multiplication by w^2 takes a fourth centered difference:

    (w^2 B_e)hat(n) = Delta^4 b_(n-2)/(2pi), n>=2.

For n>=3, use(R3) with base n-2>=1 to get O(a^2(1+n)^-7), enlarging the universal constant at n=3. At n=2 and |n|<2 use the finite low-mode bounds above. Evenness handles negative modes. Thus

    ||w^2 B_e||H6 <= C a^2.                                (R4)

The tail check is sum n^12*n^-14<infinity. This is exactly the regularity required in the frozen proof. No first-variation-only or finite-matrix argument has replaced the all-mode estimate.

## 4. The angular singularity and the reciprocal product

Here is a compatible route to the pointwise estimates as well; alternatively the author's elementary Poisson-convolution identity can be retained with full credit to the same resolvent path construction.

Let P_x(theta)=(1-x^2)/(1-2x cos(theta)+x^2). The amplitude yields

    R_e(theta) = Rhat_e(0)
       -(1/(2pi)) integral_0^infinity A(t)
                            [P_exp(-2t)(theta)-1]dt.         (R5)

The subtraction of1 is essential. A need not have finite total absolute mass at infinity. For t<=1, (R1) gives |A(t)|<=Ca. For t>=1, P_exp(-2t)-1 and every positive angular derivative are O_l(exp(-2t)), which compensates the growth in(R1). The formula defines an L1 function, by integrating the absolute angular norm first, and has exactly the Fourier coefficients in(R2). Its constant coefficient is Rhat_e(0)=O(a).

The source R_e is L1 by absolute domination. It is also continuous off the diagonal: for the first chain, separated Poisson poles have uniformly small integrals on sufficiently small neighborhoods of either pole; on the complement ordinary dominated convergence applies. For the higher chains P_s varies continuously in L^(3/2), the Green kernel smooths it to a bounded function, and the source's contraction gives a uniformly summable tail. Thus Fourier uniqueness followed by off-diagonal continuity identifies(R5) with the actual pointwise kernel, rather than merely an unrelated representative.

For small t, 1-exp(-2t) is comparable to t. Using the rational Poisson derivative bound and integrating in t gives, with d the distance to2pi Z,

    |R_e(theta)| <= Ca(1+|log d|),
    |R_e^(l)(theta)| <= C_l a d^(-l), 1<=l<=6.               (R6)

For example, split t<=1 into t<=d and dyadic shells d<t<=1; the first shell and geometric sums give the derivative bounds, and the zeroth derivative has logarithmically many shells. The t>=1 part is smooth and uniformly O(a). This is elementary Poisson integral analysis after the existing amplitude estimate.

Put S=pi wR_e, extending S(0)=0. Then ||S||infinity<=Ca, and

    |S^(l)(theta)| <= C_l a d^(2-l)(1+|log d|), 0<=l<=6.

Take a below an absolute threshold so that ||S||infinity<=1/2. The exact reciprocal identity is

    f_e = pi w - e pi^2 w^2 R_1 + E_e,
    E_e = -pi^2 w^2 B_e + pi w S^2/(1+S).                  (R7)

The first error is handled by(R4). For the second, any l-th derivative, l<=6, is a finite sum of products with a derivative of w, at least two differentiated S factors, and possibly more S factors from differentiating the denominator. With m>=2 S factors, the term has the bound

    C_l a^m d^(2+2m-l)(1+|log d|)^m.

Since a is bounded and d^2(1+|log d|) is bounded, the whole derivative is at most

    C_l a^2 d^(6-l)(1+|log d|)^(l+2).

Derivatives of orders0–5 tend to zero at the puncture. The sixth is square-integrable. Integrating by parts after excising a radius eta, then letting eta tend to0, has vanishing boundary terms through order5, so these are the weak derivatives. It follows that

    ||E_e||H6 <= C e^2 Q^2,
    |Ehat_e(n)| <= C e^2 Q^2 (1+|n|)^(-6).                 (R8)

This is ordinary product/chain differentiation and Fourier Sobolev estimation. The reason six derivatives suffice is visible from the three double zeros in the quadratic reciprocal term w^3 R_e^2. There is no appeal to a pseudodifferential calculus for smooth symbols, which would leave the measurable-v hypothesis unsupported.

## 5. Full simultaneous conclusion, with the frozen constants and quantifiers

The first-order coefficient, including n=2, is exactly

    fhat_e(n)=-(pi/2)e m_(n-2)+Ehat_e(n), n>=2,
    m_k=integral_0^1 v(r)(1-r^2)^4 r^(2k+1)dr.

The weight comes from the fourth difference of the elementary moment c_1(n), rather than from an additional positivity theorem. Its unweighted value is

    beta_n=12/[(n-1)n(n+1)(n+2)(n+3)] >= (1+n)^(-5).

If m_k>=delta beta_(k+2), then(R8) and e<=c delta/Q^2 imply

    |Ehat_e(n)| <= Cc e delta beta_n.

Choose one absolute c so that Cc<=pi/4 and so that every previous a=eQ smallness requirement holds. The latter is possible because delta<=Q implies eQ<=c. This gives the exact frozen n>=2 bound. Mode1 starts at-pi and differs by O(a), so shrinking the same c gives fhat_e(1)<=-pi/2. All modes, including the finitely many low modes, are controlled with one universal c. There is no numerical or optimal-c assertion.

The bound(R8) and the first-order n^-5 bound make the Fourier series absolutely summable. For zero-sum real coefficients at distinct circle points, the Fourier quadratic form is the sum of fhat_e(n) times the squared modulus of the corresponding discrete Fourier moment. Each nonzero frequency coefficient is strictly negative. A nonzero finite atomic measure cannot have all these moments zero: the first m complex powers give an invertible Vandermonde matrix on m distinct points. This proves the frozen finite-set strictness for e>0, without making a strictness claim at e=0.

Kernel positivity does not require a new signed maximum principle. From(R6), N_e=(1+S)/(pi w)>0 off the diagonal. The source majorant gives the solution with boundary value1 within O(a) of1; rotation invariance then gives k_e>0. Equation(R7) gives continuity of f_e at0, and D_e=k_e^2 f_e. Its e=0 value is w/(4pi), as frozen.

For necessity, the same expansion holds without the moment-margin hypothesis. If D_e is CND along positive e tending to0, then so is f_e for small e. Testing against trigonometric mean-zero densities, or their finite equally spaced approximations, gives fhat_e(n)<=0 for n!=0. For each fixed n>=2, divide the expansion by e and let e tend to0; (R8) gives m_(n-2)>=0. No uniform strictly positive margin is inferred, and no sufficiency on a vanishing-moment face follows.

Finally, the normalized moments for r^2-b are (k+1)/(k+6)-b. Their infimum is1/6-b. This gives exactly the sign-changing class0<b<1/6, delta=1/6-b and Q=1-b. If b>1/6, m_0<0 makes mode2 positive for every sufficiently small e. Nothing here treats b=1/6. This example, strictness, positivity and necessity are parts of the joint corollary, not separate grades.

## 6. Relation to the author's construction and contribution judgment

The author's signed Hausdorff measures are not an unexplained new perturbation primitive after comparison with Simon's actual proof. Under r=exp(-x),

    g_n(exp(-x),exp(-y))
      =[exp(-n|x-y|)-exp(-n(x+y))]/(2n),

the free half-line Green kernel used in Simon's Lemma2.2. Its positive length representation ranges from |x-y| to x+y. The composite Hausdorff parameter is exp(-2alpha), where2alpha is the total endpoint-plus-path length. This explicitly identifies the compatible old chain construction at the operative proof level.

The author's F_t power series is the normalized Bessel J_t series; the recurrence producing h_t(b)=b/[2(t+1)-h_(t+1)(b)] follows from the standard neighboring-order Bessel recurrences. Expanding a scalar reciprocal gives the Catalan count, and differentiating its positive rational products gives the displayed fixed-order bounds. Those are valid useful calculations to credit, but Simon's already-proved nonlinear amplitude estimate replaces their critical role here. NIST DLMF10.2.2 and10.6.1–10.6.2 were checked as explicit formula references; the cited Watson/Olver derivations were not newly read and are not represented as such.

The closed joint interface is therefore: existing quadratic Laplace-amplitude remainder -> fourth-difference H6 smoothing, plus an elementary reciprocal product estimate -> all-mode sign dominance with the moment margin. I judge that composition technical at this exact frozen scope. The mathematical theorem can still be useful and may be new as a statement in this project. No read primary paper was found stating this entire boundary reciprocal theorem verbatim, so REDISCOVERY is not justified. No worldwide literature novelty, search exhaustion, correctness gate or acceptance is assigned.

Primary links: [Simon published paper](https://www.maths.tcd.ie/EMIS/journals/Annals/150_3/simon.pdf), [Daudé–Macià–Meroño–Nicoleau v3](https://arxiv.org/pdf/2402.06321v3), [Macià–Meroño–Sánchez-Mendoza v2](https://arxiv.org/pdf/2501.05889v2), [DLMF series](https://dlmf.nist.gov/10.2.E2), [DLMF recurrences](https://dlmf.nist.gov/10.6).
