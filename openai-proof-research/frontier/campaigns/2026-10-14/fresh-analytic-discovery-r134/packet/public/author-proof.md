# Author proof for the unchanged frozen scope K369R134

This is a research proof submitted for separate review, not a manuscript, contribution verdict, acceptance or release. The exact statement is FROZEN-SCOPE.md, SHA256 690e3b4b2314ac7009a8cf60b24c89961b2e6e01dd21543904156b851e304a88. All constants denoted C or C_j below are finite absolute constants, with the subscript indicating dependence on an explicitly fixed derivative order only. They do not depend on the radial potential. The universal constant c in the frozen statement is chosen at the end from these constants. No explicit numerical value is asserted.

## 1. Inputs, conventions, and the operation being added

Use the disk Green and Poisson kernels from family 369 at the stipulated pin. Sections 04 and 05 of that manuscript give the boundary resolvent construction and its reciprocal-kernel theorem for nonnegative bounded subcritical potentials. The latter is already paid; its positivity-preserving finite update is not claimed here as new. We use the kernel construction and absolute majorants for the constant positive potential, with no source truth audit. The source theorem alone does not apply to the signed potentials below.

Agler–McCarthy, *Complete Nevanlinna–Pick Kernels*, Theorem 1.2 and Corollary 1.12, supply the established reciprocal-inertia context. Their finite-valued positive definite kernel hypotheses do not identify our singular Green function as a reproducing kernel. Rozenblum, arXiv:1012.3528v1, Section 2.2.2 and Section 2.3.1, supplies the classical diagonalization of radial Toeplitz forms. The weighted version here follows by the same direct monomial orthogonality. Neither reciprocal-matrix characterization nor Toeplitz diagonalization is the proposed contribution.

The added operation is an infinite-mode nonlinear lifting: uniformly positive weighted radial moments give strict negative type of the reciprocal boundary kernel at small coupling, although the physical potential may change sign. The proof gives a remainder with six square-integrable angular derivatives, whereas the favorable leading coefficients have order n^(-5). It is this uniform separation, not continuity of a finite matrix, that closes the deduction.

Let v be real measurable with ||v||infinity=Q>0, and write a=eQ. Until the final choice of e we require a less than a sufficiently small absolute constant. We always integrate radial variables against r dr and angular variables against ordinary dtheta. Let

 w(theta)=2-2cos(theta),   d(theta)=dist(theta,2pi Z).

For a periodic integrable h, hhat(n)=(2pi)^(-1) integral h(theta)e^(-in theta)dtheta. Write R_e(theta)=N_e(1,e^(i theta))-1/(pi w(theta)) away from zero. Rotation invariance makes K_e(0,s) a constant, denoted k_e.

Absolute convergence of all source series at their stated off-diagonal arguments follows by replacing every v by Q and e by |e| in every Green chain. The source's constant-potential estimates apply for sufficiently small a. To see subcriticality directly, integral_D G(z,x)dx=(1-|z|^2)/4, and the symmetric-kernel Schur bound gives ||G||_(L2 to L2)<=1/4. Thus a<1 gives a strict contraction with a uniform margin. The same identity gives ||T_e||_(Linfinity to Linfinity)<=a/4.

If W_e is the Dirichlet solution with boundary data 1, its Neumann series gives ||W_e-1||infinity <= (a/4)/(1-a/4). By rotational invariance and the Poisson representation, k_e=W_e(0)/(2pi). In particular k_e>0 when a<=1. Hence multiplication by k_e^2 preserves conditional negative definiteness; it suffices to study f_e=1/N_e. The standard Green identities identifying these kernels with -Delta-eq are unchanged for signed q, since all series are absolutely dominated by the constant positive case. No normal differentiation of an undominated singular series is needed.

## 2. A radial Green chain is a Hausdorff moment

For a real parameter t>=0 define

 g_t(r,s)=(rs)^t integral_(max(r,s))^1 u^(-2t-1)du,    0<r,s<1.

For t>0 this is [(min(r,s)/max(r,s))^t-(rs)^t]/(2t); at t=0 it is -log(max(r,s)). This is the radial Dirichlet inverse for -d^2/dr^2-r^(-1)d/dr+t^2/r^2 with integration measure s ds. It follows either by differentiating on the two sides of r=s and checking the jump, or by solving the two homogeneous radial equations. In particular it is positive.

Define c_1(t)=integral_0^1 v(r)r^(2t+1)dr. For j>=2 define

 c_j(t)= integral_((0,1)^j) r_1^t r_j^t [product_(i=1)^j v(r_i)r_i dr_i]
                         [product_(i=1)^(j-1) g_t(r_i,r_(i+1))].          (2.1)

Inserting the integral expression for each g_t shows that c_j(t)=integral_[0,1] x^t dnu_j(x), where nu_j is the pushforward of the signed measure

 [product_i v(r_i)r_i dr_i] [product_i du_i/u_i],
 max(r_i,r_(i+1))<u_i<1,

under x=(product_i r_i/product_i u_i)^2. This x belongs to [0,1]: for example u_i>=r_i for i<j implies the ratio is at most r_j<=1. For j=1 use x=r^2. The total variation of nu_j is bounded by nu_j^Q, the same positive pushforward with every v replaced by Q. Finiteness will follow from the explicit constant-potential coefficient estimate below, including at t=0.

Here is also a pointwise angular derivation, to avoid identifying kernels only through almost-everywhere Fourier uniqueness. Let P_x^circle(theta)=(1-x^2)/(1-2x cos(theta)+x^2), for 0<=x<1. It has Fourier coefficients x^|n| and integral 2pi. The disk Poisson kernel at radius r is (2pi)^(-1)P_r^circle. The angular Green kernel is

 G(re^(i alpha),se^(i beta))
  =(2pi)^(-1) integral_(max(r,s))^1 P_(rs/u^2)^circle(alpha-beta)du/u.     (2.2)

Its Fourier coefficients are g_|n|(r,s)/(2pi), which verifies the displayed identity by the elementary logarithmic Green expansion; it also follows by integrating the geometric series. The parameter can equal 1 only on an integration endpoint of measure zero. The normalized convolution of two circle Poisson kernels is P_x^circle*P_y^circle=P_(xy)^circle. Substituting (2.2) in a boundary-to-boundary Green chain and doing its angular integrals therefore gives exactly

 R_e(theta)=(2pi)^(-1) integral_[0,1] P_x^circle(theta)dmu_e(x),
 mu_e=sum_(j>=1) e^j nu_j.                                             (2.3)

All interchanges are first valid for the positive majorant by Tonelli and then for the signed series by domination. In particular

 Rhat_e(n)=(2pi)^(-1) sum_(j>=1)e^j c_j(|n|).                           (2.4)

## 3. Constant-potential estimates, including differences of every mode

We establish the estimates used for nu_j^Q rather than assuming asymptotic formulas for Bessel functions. For constant potential b, the regular radial solution before boundary normalization is

 y_t(r;b)=r^t F_t(br^2),
 F_t(z)=sum_(l>=0) (-z)^l/[4^l l! (t+1)(t+2)...(t+l)],                (3.1)

where an empty product is 1. Substitution proves the ODE. For b near zero, y_t(1;b) is nonzero. Define h_t(b)=t-y_t'(1;b)/y_t(1;b). Green's identity, or its radial Wronskian, gives

 h_t(b)=b integral_0^1 r^t y_t(r;b)/y_t(1;b) r dr
       =sum_(j>=1) b^j c_j^1(t).                                    (3.2)

The radial Neumann series justifies the second identity. Uniformly in t>=0 it converges near b=0: the positive kernel g_t is bounded above by g_0 from its integral representation, and the latter radial inverse has Linfinity norm 1/4. The coefficients of (3.1) give directly

 F_t'(z)=-F_(t+1)(z)/[4(t+1)],
 F_t(z)=F_(t+1)(z)-z F_(t+2)(z)/[4(t+1)(t+2)].

Consequently

 h_t(b)= b/[2(t+1)-h_(t+1)(b)].                                     (3.3)

We use this as a formal power-series identity, so no infinite-continued-fraction convergence assumption enters. Expanding the reciprocal in (3.3), each coefficient c_j^1(t) is a sum of products of exactly 2j-1 factors [2(t+l)]^(-1), with integers l>=1, all with positive coefficient. Counting these terms with multiplicity gives the Catalan number Cat_(j-1): on replacing every denominator by 1 their generating function satisfies H=b/(1-H). This also follows by induction on the coefficient degree; only lower-degree terms occur on the right. Thus for every integer k>=0,

 0<=(-1)^k d^k/dt^k c_j^Q(t)
 <= Cat_(j-1) Q^j (2j-1)_k/[2^(2j-1)(t+1)^(2j-1+k)],                (3.4)

where (p)_k=p(p+1)...(p+k-1). For k=0 this proves the promised finite mass. For k>0 differentiate the positive products. The sum of the multinomial derivative coefficients is (2j-1)_k, by the ordinary product rule, and every t+l is at least t+1. Also c_j^Q=Q^j c_j^1.

Let Delta b(t)=b(t+1)-b(t). Moment domination implies

 |Delta^k c_j(t)|
 <= integral x^t(1-x)^k dnu_j^Q(x)
 <= integral x^t(-log x)^k dnu_j^Q(x)
 =(-1)^k (c_j^Q)^(k)(t).                                           (3.5)

The last identity follows by monotone/dominated differentiation of the Laplace moment; its finite bound is also supplied by (3.4). It can first be used for t>0 and then extended to t=0 by monotone convergence. Since Cat_(j-1)<=4^(j-1), summing (3.4) gives, for a=eQ<=1/2,

 sum_(j>=1)e^j c_j^Q(t)<=C a/(t+1),                                (3.6)
 |Delta^k b_e(t)|<=C_k a^2/(t+1)^(3+k),  0<=k<=6,                 (3.7)
 b_e(t)=sum_(j>=2)e^j c_j(t).

Indeed (2j-1)_k grows only polynomially in j for each fixed k, and the remaining sum is bounded by a geometric series times a^2 after j>=2 is factored out. These estimates hold for arbitrary signed v with the stated Q, with the same constants.

## 4. Endpoint behavior of the boundary kernel

Let mu_e^+=sum e^j nu_j^Q, which dominates |mu_e|. Its t-th moment satisfies (3.6). For 0<h<=1/2 choose N=floor(1/h). On [1-h,1], x^N>=1/4. Hence

 mu_e^+([1-h,1])<=4 integral x^N dmu_e^+ <=C a h.                   (4.1)

For h>=1/2 the same bound follows from its total mass. There is no atom at 1.

For theta away from 2pi Z, differentiating the rational Poisson kernel gives

 |(d/dtheta)^l P_x^circle(theta)|
 <= C_l [1+((1-x)+d(theta))^(-l-1)].                              (4.2)

For x<=1/2 this is immediate by its geometric series. For x>=1/2 use |1-x e^(i theta)|>=c_0((1-x)+d(theta)) and P_x^circle=2 Re(1-x e^(i theta))^(-1)-1. Applying (4.1) on dyadic shells in 1-x yields, for 0<d<=1,

 |R_e(theta)|<=C a(1+|log d|),
 |R_e^(l)(theta)|<=C_l a d^(-l),  1<=l<=6.                         (4.3)

For completeness, the shell 1-x<=d has mass at most C a d and contributes at most C_l a d^(-l); shells 2^k d<1-x<=2^(k+1)d contribute at most C_l a (2^k d)^(-l). Their sum is geometric for l>=1 and has at most C(1+|log d|) terms for l=0. Away from zero all derivatives are bounded by C_l a. These arguments also justify differentiation under (2.3) locally away from zero. The integral is continuous there and defines the actual pointwise Green-chain sum, by Section 2.

Put S_e=pi w R_e and set S_e(0)=0. Since w has a double zero, (4.3) implies

 ||S_e||infinity<=C a,
 |S_e^(l)(theta)|<=C_l a d^(2-l)(1+|log d|),  0<=l<=6.             (4.4)

Choose an absolute a_0<=1/2 so small that ||S_e||infinity<=1/2 whenever a<=a_0. Then N_e=(1+S_e)/(pi w)>0 off the diagonal, and

 f_e(theta)=pi w(theta)/(1+S_e(theta)),  f_e(0)=0,                  (4.5)

is continuous and real even. The earlier bound on W_e gives k_e>0. This proves all positivity and continuity assertions needed for the normalization.

## 5. The uniform nonlinear remainder

Let R_1 mean the coefficient of e in R_e, not the kernel at coupling e=1. By (2.4), its Fourier coefficients are c_1(|n|)/(2pi). Expanding the exact reciprocal once gives

 f_e=pi w-e pi^2 w^2 R_1+E_e,
 E_e=-pi^2 w^2(R_e-eR_1)+pi w S_e^2/(1+S_e).                     (5.1)

We prove ||E_e||_(H^6(S^1))<=C a^2. The choice of equivalent Fourier or derivative norm only changes C.

For B_e=R_e-eR_1, its Fourier coefficients are b_e(|n|)/(2pi). Multiplication by w^2 takes the fourth centered difference. For n>=2,

 (w^2 B_e)hat(n)=(2pi)^(-1) Delta^4 b_e(n-2).

By (3.7) this is at most C a^2 (n-1)^(-7) in absolute value. The finitely many n with |n|<2 are at most C a^2 by (3.6) with j>=2; negative modes follow by evenness. Thus sum_n (1+n^2)^6 |(w^2 B_e)hat(n)|^2<=C a^4, since the tail is bounded by a constant times sum n^(-2). This proves the first part of (5.1) belongs to H^6 with norm at most C a^2.

For U_e=w S_e^2/(1+S_e), differentiate on the punctured circle. Each derivative through order l<=6 is a finite sum of terms involving a derivative of w, at least two factors which are derivatives of S_e, further factors of derivatives of S_e coming from differentiating the denominator, and a bounded power of (1+S_e)^(-1). Use (4.4) on each factor. A derivative of w of order j is bounded by C_j d^(2-j), also for j>2 because the right side then increases as d decreases. If a term has m>=2 factors coming from S_e and a total of l derivatives, its bound is

 C_l a^m d^(2+2m-l)(1+|log d|)^m.

Here m<=l+2. Because a<=a_0<=1 and d^2(1+|log d|) is bounded on (0,1], all these terms are bounded by

 C_l a^2 d^(6-l)(1+|log d|)^(l+2),  0<=l<=6.                     (5.2)

Derivatives through order 5 tend to zero from both sides at zero. Extend them by zero there. The sixth derivative is in L2 because every fixed power of |log d| is square-integrable near zero. Integrating by parts on the punctured circle and sending the excised radius to zero shows that these are weak derivatives, with no delta terms: all boundary terms through order 5 vanish. On the rest of the circle the same derivative bounds are uniform. Therefore U_e belongs to H^6 and ||U_e||_(H^6)<=C a^2. Together with the first part,

 ||E_e||_(H^6)<=C e^2 Q^2,
 |Ehat_e(n)|<=C e^2 Q^2/(1+|n|)^6.                               (5.3)

This estimate is uniform over all bounded radial v with fixed Q. Smoothness of v was never used.

## 6. All Fourier modes and the universal coupling constant

For n>=2, multiplication of R_1 by w^2 yields exactly

 (w^2 R_1)hat(n)
  =(2pi)^(-1) integral_0^1 v(r)r^(2n-3)(1-r^2)^4 dr
  =m_(n-2)/(2pi),                                                (6.1)

where m_k is the weighted moment in the frozen statement. Thus

 fhat_e(n)=-(pi/2)e m_(n-2)+Ehat_e(n),  n>=2.                     (6.2)

The beta integral gives

 beta_n=integral_0^1 (1-r^2)^4 r^(2n-3)dr
       =12/[(n-1)n(n+1)(n+2)(n+3)],  n>=2.                      (6.3)

One elementary uniform lower bound is beta_n>=(1+n)^(-5) for n>=2. For example (n-1)n<=(n+1)^2 and (n+2)(n+3)<=(20/9)(n+1)^2, so the stronger factor 27/5 is available.

Under (M), m_(n-2)>=delta beta_n. If e<=c delta/Q^2, (5.3) gives

 |Ehat_e(n)|<=C c e delta/(1+n)^6<=C c e delta beta_n.

Choose c<=pi/(4C), where C is the fixed constant in (5.3). Equations (6.2)–(6.3) give the frozen bound for every n>=2 simultaneously.

Mode 1 starts with (pi w)hat(1)=-pi. From (4.5), ||f_e-pi w||infinity<=C_1 eQ. Therefore fhat_e(1)<=-pi/2 if eQ<=pi/(2C_1). Since delta<=Q, the hypothesis e<=c delta/Q^2 implies eQ<=c. We now fix a positive absolute c no larger than a_0, 1, pi/(4C), and pi/(2C_1). This single choice gives every smallness requirement in the proof. Its existence and independence of v, Q, delta are established; no claim of a best or numerical constant is made.

The Fourier series of f_e converges absolutely. Indeed (6.1) and |v|<=Q give leading coefficients O(eQ n^(-5)) for n>=2, and (5.3) gives an absolutely summable remainder; the low modes are finite. Since f_e is continuous, it equals this Fourier series everywhere, including at zero.

We recall the elementary circle criterion, including strictness. For any finite real signed combination a_i at angles theta_i, absolute convergence permits

 sum_ij a_i a_j f_e(theta_i-theta_j)
  =sum_(n in Z) fhat_e(n) |sum_i a_i e^(in theta_i)|^2.             (6.4)

If sum_i a_i=0, the constant term disappears. All remaining coefficients are strictly negative for e>0 by the bounds just proved. If distinct s_i=e^(i theta_i) and a_i are not all zero, at least one of the moments sum_i a_i s_i^n for 0<=n<=m-1 is nonzero, by invertibility of the Vandermonde matrix. The zeroth is zero, so one with n>=1 is nonzero. Consequently (6.4) is strictly negative. Multiplication by k_e^2>0 proves (a). At e=0, direct substitution gives D_0=w/(4pi), and its conditional negative semidefiniteness follows from (6.4) with only the modes ±1. This does not assert strictness at e=0.

For later use, the converse circle implication is equally elementary: a continuous translation-invariant conditionally negative semidefinite kernel has nonpositive Fourier coefficients at every nonzero mode. Approximate the real mean-zero density cos(n theta)dtheta by equally spaced signed point masses (take grid sizes larger than 2n so their sum is exactly zero); continuity passes the finite inequalities to the integral quadratic form. That form is 2pi^2 fhat(n). The sine test gives the same result; here the kernel is real even. No abstract Fourier-positivity theorem is needed as an additional hypothesis.

## 7. Necessity and genuinely signed examples

For any bounded radial v, Sections 1–5 hold for sufficiently small e without (M). If Q=0 everything is zero and the moment conclusion is immediate. Otherwise, suppose D_e is CND along positive e tending to zero. As k_e^2>0, so is f_e. By the converse criterion, fhat_e(n)<=0 for n>=1. Fix n>=2, divide (6.2) by e, and let e tend to zero along that sequence. Equation (5.3) forces m_(n-2)>=0. Every k>=0 arises this way. This proves precisely the necessity in (c), without promoting it to sufficiency on the boundary of the moment cone.

For v(r)=r^2-b, the ratio of its k-th weighted moment to the moment with v=1 is

 (k+1)/(k+6)-b.

This follows by substituting x=r^2 and taking the ratio B(k+2,5)/B(k+1,5). It is increasing in k and its minimum is 1/6-b. For 0<b<1/6, (M) holds with delta=1/6-b, Q=1-b, and v is negative on the disk of radius sqrt(b) and positive outside it. This verifies the example as an application of the full bounded-potential theorem, not as a separately nominated toy result.

For b>1/6, m_0=(1/10)(1/6-b)<0. Equation (6.2) at n=2 and (5.3) imply fhat_e(2)>0 for every sufficiently small positive e. The converse circle criterion rules out CND. At b=1/6 the leading obstruction vanishes; no conclusion at this endpoint has been frozen or proved here.

## 8. Exact limits of the proof

The proof establishes the full frozen statement, subject to independent verification. It does not extend the center argument to arbitrary p. At the center radial symmetry makes K_e constant and permits the Fourier criterion. For an off-center p, multiplication by K_e(p,s) changes the zero-sum hyperplane and is not a harmless positive scalar. The all-center signed problem is therefore absent from the scope.

Nor does boundary CND alone establish the full reciprocal-inertia condition for interior Green matrices, or a complete Pick property for a singular infinite-diagonal kernel. The source and the classical primary theorem are distinguished at this interface. No Neumann eigenfunction or eigenmap conclusion is deduced from the signed-potential theorem. Old targets and R041's projection-body operation remain unchanged.

The crucial estimate to attack in an adversarial check is (5.3), including the signed Hausdorff path domination, the coefficient count in (3.3)–(3.4), and the removal of weak-derivative boundary terms in (5.2). Those are fully proved above; naming them here is not an unresolved assumption. A separate contribution review must decide whether this nonlinear lifting is substantial after crediting the source resolvent construction, the classical radial decomposition, positive-kernel theory, and ordinary Fourier analysis. This author proof assigns no such grade.
