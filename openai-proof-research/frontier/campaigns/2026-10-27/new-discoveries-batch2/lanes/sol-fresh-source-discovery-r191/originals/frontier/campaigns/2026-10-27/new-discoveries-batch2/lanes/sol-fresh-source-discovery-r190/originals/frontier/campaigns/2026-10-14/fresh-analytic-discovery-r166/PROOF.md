# Author proof of frozen T366A166

This proves the statement in STATEMENT.md at its frozen scope. It is an author proof offered for independent adversarial correctness and separate contribution review. No grade or count is assigned. The source truth assumption is the stipulated SOURCE366 theorem together with its operative regularity inputs. Exact primary versions, acquisition limits, and comparison are recorded privately. The precise input labels are DF Lemmas 5.0.3-5.0.4, Lemma 5.1.3 and equations (5.1.16)-(5.1.23), the unnormalized nonlinear estimates in the proof of Proposition 5.5.1, Corollary 5.5.2, and Lemma 5.3.7/Proposition 5.3.8 for the homogeneous spectrum. The bounded variational representative and regular-arc interface are Proposition 2.5.2 and Appendix A. These labels refer to the actually acquired arXiv2308.14660v2, not an inaccessible edition. No formalization or manuscript/release stage is opened.

## 1. Paid endpoint input and normalization

Fix an arbitrary loose end p in the statement. SOURCE366, its initial reduction and its endpoint regularity interface give a single arc near p, a tangent, local boundedness of u, and a locally C1,1 parametrization away from p. Restrict to a smaller disk. Translate p to zero, rotate its tangent to the positive horizontal axis, subtract u(p) from u and g, and choose the sign of u if necessary. These operations preserve the problem and the geometry. The modified g remains bounded locally. No uniform global bound on u by g is needed. If the primary normalization on B2 is used literally, choose a fixed spatial scale rho, replace u by rho^(-1/2)u(rho x) and g by rho^(-1/2)g(rho x), and use fidelity coefficient lambda=rho^2<=1. DF (1.1.2) permits any fixed finite M0 bounding this rescaled datum. Rescaling back only changes the coefficient and local constants. The equations below are written at the original scale, with lambda=1 absorbed into the fidelity errors.

We use the actual corrected-conjugate construction and equations in DF Chapter 5, rather than extend the homogeneous C2 theorem by assertion. In polar coordinates put

 gamma(r)=r(cos(theta(t)),sin(theta(t))), t=-log r,
 a(t)=theta'(t), S(phi)=sqrt(2/pi) sin(phi/2), c=1/sqrt(2pi).

Shrink the disk, equivalently increase the initial time T, so these coordinates are valid for all t>T and theta(t) tends to zero. The harmonic conjugate w of u plus the normalized Poisson correction gives f(phi,t)=exp(t/2)w(exp(-t),phi+theta(t)). For nonzero fidelity this uses the auxiliary solution of Delta u_aux=-(u-g), with u_aux(0)=0 and grad u_aux(0)=0. The rotated gradient of u+u_aux is a whole-disk curl-free field; hence the potential w exists across the arc, and is harmonic off it. Its trace on the arc need not be zero.

The following is the paid input, with all estimates on strips of any fixed finite width, a harmless enlargement of the strip on the right understood:

 (i) theta tends to zero, and for some epsilon0>0,
     ||f-S||_H2(strip_t)+||a||_H1(interval_t)
       +||theta||_H2(interval_t) <= C exp(-epsilon0 t).

 (ii) f is uniformly W2,p on such strips for each finite p; a and a' are uniformly bounded. For every finite p there is epsilon_p>0 such that
     ||f-S||_W2,p(strip_t) <= C_p exp(-epsilon_p t).
     In particular f-S has a decaying C1 norm on strips.

 (iii) With L=partial_tt-partial_t+partial_phiphi+1/4,
     Lf=(a'-a)f_phi+2a f_tphi-a^2 f_phiphi,
     f(0,t)=f(2pi,t)=H1(t),
     (a'-a-a^3)/(1+a^2)^(5/2)
        = f_phi(2pi,t)^2-f_phi(0,t)^2+H2(t).

 (iv) For each s<3/2, |H2(t)|<=C_s exp(-s t). H1 and its first derivative have the same rate, in the trace norms specified by the corrected-conjugate construction; in particular H1 is uniformly C1,alpha for every alpha<1 on fixed strips and its H3/2 norm decays exponentially.

Here and below H2 in a norm denotes the Sobolev space; H2(t) with an argument is the scalar fidelity error. Identities with measurable data hold almost everywhere or in distributions. The bounded variational value g_K used in the curvature equation is the one supplied by DF; no pointwise restriction of an arbitrary L-infinity representative to K is assumed.

For clarity about item (ii), it does not add a new regularity hypothesis. The coarse odd H2 decay and H1 decay of a are supplied by the nonlinear three-annuli proof, specifically the unnormalized estimate preceding (5.5.5). The full even error has the C1 decay of Corollary 5.5.2, (5.5.10); the projected even H2 bound is in (5.5.6). Alternatively, full even H2 decay follows directly from the fixed-strip elliptic estimate for f-S, using its C1 decay, the just-established L2 decay of a' and a, and the exponentially decaying H3/2 boundary datum H1. Thus no undetermined constant even amplitude is included in item (i). Recover theta by integrating a toward its zero limit. The equations in (iii), bounded first derivatives of f and the angle equation first give uniform a'. The principal operator for f is partial_tt-2a partial_tphi+(1+a^2)partial_phiphi, whose coefficient matrix has determinant one; its coefficients are uniformly elliptic and uniformly Lipschitz once a is small and a' is bounded. Flat-boundary elliptic estimates, using the C1,alpha trace H1 with alpha>1-1/p, give uniform W2,p bounds on smaller strips. Interpolating the exponentially decaying H2 norm with a uniform W2,q bound, q>p, gives the asserted positive epsilon_p for p>2; p<=2 follows by Holder. Taking p>2 gives decaying C1 norms. Alternatively the same estimates occur in DF's first linearization. The possible constants depend on the fixed minimizer and chart, as allowed in STATEMENT.md.

This proof uses the known coarse exponent only as a starting point; it does not presuppose the sharp exponent or vanishing curvature with fidelity.

## 2. Exact odd equations and residual bounds

Let E=(f(phi,t)+f(2pi-phi,t))/2=S+e and O=f-E. Then E is even and O is odd about pi. Both boundary values of O vanish; moreover O(pi,t)=0. Reflection in phi reverses a phi derivative and preserves t derivatives. Taking the odd part of the first equation in Section 1 gives

 LO=(a'-a)S_phi+R,
 R=(a'-a)e_phi+2a e_tphi-a^2 O_phiphi.                 (2.1)

At the boundary E_phi(2pi)=-E_phi(0), whereas O_phi(2pi)=O_phi(0). Thus the angle equation is exactly

 a'-a=-4c O_phi(0,t)+N,                               (2.2)
 N=a^3-4[(1+a^2)^(5/2)E_phi(0,t)-c]O_phi(0,t)
          +(1+a^2)^(5/2)H2(t).                       (2.3)

The leading coefficient here is -4c; changing it changes the spectral equation, so it is retained explicitly. The equal, possibly rough boundary values H1 cancel from the odd boundary condition. There is no additive term involving e alone in (2.1) or in the nonlinear part of (2.3).

Choose a positive epsilon smaller than the coarse H2, C1, and angle exponents. If X(t) bounds the H2 norm of O and theta on a strip with fixed padding, the trace theorem and one-dimensional H1 embedding give

 ||(R,N)||_L2(strip_t) <= C exp(-epsilon t)X(t)
                              +C_s exp(-s t), s<3/2. (2.4)

Indeed, e_phi is uniformly O(exp(-epsilon t)); e_tphi has L2 norm O(exp(-epsilon t)); ||a||_infinity is bounded by X(t); and O_phi(0,.) has L2 trace norm bounded by ||O||_H2. In the cubic term use two of the coarse factors a, leaving one factor controlled by X. In a^2 O_phiphi use the coarse sup bound for a^2. Products are taken on enlarged fixed strips, so every constant is independent of t. This proves (2.4) without any derivative of H2.

## 3. A boundary-state spectral realization for L2 forcing

We now establish the extension of the homogeneous spectral calculation needed here. Set I=(0,pi), and let

 H=L2(I) direct-sum R,
 ||(z,b)||_H^2=integral_I |z|^2+(pi/2)|b|^2,
 [(z,b),(h,d)]=integral_I zh-(pi/2)bd.

The bracket is an indefinite nondegenerate bounded pairing. Define the closed operator

 D(A)={(z,z(0)): z in H2(I), z(pi)=0},
 A(z,z(0))=(z''+z/4,-(2/pi)z'(0)).                    (3.1)

The H graph norm of A is equivalent to the ordinary H2(I) norm of z. One direction follows from trace inequalities. For the other, z''=(Az)_bulk-z/4 controls z'' in L2, while the standard interval interpolation estimate controls z' by z and z''. Closedness follows by this equivalence and continuity of the traces in H2. Integration by parts gives

 [Az,h]= -integral z'h' +(1/4)integral zh=[z,Ah]

for z,h in D(A); the boundary term at zero is canceled by the boundary coordinate in (3.1).

The zero root sector is generated by

 e1=(cos(phi/2),1),
 e0=((phi-pi)sin(phi/2),0),
 A e1=0, A e0=e1.                                   (3.2)

Its bracket Gram matrix is nonsingular: [e1,e1]=0 and [e1,e0]=-pi/2. In particular this two-dimensional sector must not be discarded as though the operator were positive self-adjoint.

For k>=2, let nu_k be the increasing roots above 1/2 of

 nu cos(pi nu)=(pi/2)(1/4-nu^2)sin(pi nu),
 lambda_k=nu_k^2-1/4, mu_k=nu_k-1/2.

The actual primary spectral proof establishes nu2 in (3/2,2), nu_k in (k-1,k) for k>=3, and the H1 completeness of these sine modes together with e0,e1. The mode

 q_k=(sin(nu_k(phi-pi)), -sin(pi nu_k))

satisfies A q_k=-lambda_k q_k. The bracket norm [q_k,q_k] is positive: integration by parts gives

 lambda_k [q_k,q_k]
    =integral |q_k'|^2-(1/4)integral |q_k|^2>0.

Positivity is the odd Poincare inequality on the reflected interval, with equality only for the cosine mode, to which q_k is not proportional. Normalize q_k to h_k so that [h_k,h_k]=1. Distinct high modes are bracket-orthogonal, and they are bracket-orthogonal to e0,e1 by (3.1)-(3.2).

We require completeness in H, not merely in H1. Here are the needed norm checks. The eigenvalue equation gives

 |sin(pi nu_k)| <= C/nu_k,
 integral_0^pi sin^2(nu_k(phi-pi)) dphi = pi/2+O(1/nu_k).

Thus [q_k,q_k] is bounded above and below by positive constants for k large, and hence, after including the finitely many earlier k,

 |(h_k)_b|<=C/k, ||(h_k)_bulk||_L2<=C.

For finite sums Z=sum d_k h_k,

 [Z,Z]=sum |d_k|^2,
 ||Z||_H^2=[Z,Z]+pi|Z_b|^2.

Cauchy-Schwarz and sum |(h_k)_b|^2<infinity yield

 sum |d_k|^2 <= ||Z||_H^2 <= C sum |d_k|^2.           (3.3)

Consequently the high modes form a Riesz basis of a closed subspace Y of H, on which the bracket is a positive scalar product equivalent to the H norm. The bracket-orthogonal projection onto span{e0,e1} is bounded because its Gram matrix is invertible; hence the sum of that finite-dimensional sector and Y is closed and direct. By the primary H1 completeness it contains every trace state (z,z(0)) with z in H1(I), z(pi)=0. Those trace states are dense in H: approximate any L2 bulk function away from both endpoints, then add a narrow boundary layer prescribing the independent scalar at zero. Their L2 cost tends to zero. Therefore

 H=span{e0,e1} direct-sum Y.                          (3.4)

This proves the required complete state-space expansion. In this decomposition A is the finite Jordan matrix (3.2) and the diagonal operator -lambda_k on Y, with domain given by sum lambda_k^2|d_k|^2<infinity. To see the domain assertion, finite sums with that bound converge in the graph norm and hence in H2(I). Conversely, for Z in D(A), bracket symmetry identifies the coefficients of AZ as -lambda_k d_k, so the bound follows from (3.3). The same reasoning handles the finite Jordan coordinates. Thus the spectral statement includes the operator domain, not just formal eigenfunctions.

## 4. Forced decay and extraction on a half-cylinder

We record a consequence of the preceding realization. Suppose Z(t) in D(A) satisfies

 Z''-Z'+AZ=F(t), t>T,                                (4.1)

and Z has some positive exponential decay in the norm

 ||Z||_H2((t,t+1);H)+||Z||_L2((t,t+1);D(A)).          (4.2)

Assume ||F||_L2((t,t+1);H)<=C exp(-beta t), beta>0. Then (4.2) is O(exp(-d t)) for every d<min{beta,mu2}. If beta>mu2, there is D in R such that

 Z(t)=D h2 exp(-mu2 t)+Z_*(t),                        (4.3)

where Z_* has norm (4.2) O(exp(-gamma t)) for every gamma<min{beta,mu3} with gamma>mu2. Constants may depend on T, the solution, and the exponents.

Proof of this consequence follows. Expand F and Z by (3.4). The coefficient transformation and its inverse are bounded in H. The low coordinates satisfy, in a suitable order,

 y0''-y0'=F0,
 y1''-y1'=F1-y0.

For any exponentially decreasing h, the unique exponentially decreasing solution of y''-y'=h is

 y(t)=integral_t^infinity (1-exp(t-s))h(s) ds.         (4.4)

Differentiate in distributions to verify this; the excluded homogeneous solutions are 1 and exp(t). The two low coordinates are therefore bounded at every positive exponent below beta, together with two time derivatives in local L2. This also explains why the established coarse decay, including its original moment compatibility, cannot be omitted.

For each high coefficient,

 y_k''-y_k'-lambda_k y_k=F_k.

The inverse kernel on the real line is

 G_k(s)= -exp(-mu_k s)/(2mu_k+1), s>=0,
 G_k(s)= -exp((mu_k+1)s)/(2mu_k+1), s<0.              (4.5)

It is continuous and its derivative has jump one at zero. To use (4.5) without imposing artificial data at T, multiply Z by a smooth cutoff which vanishes before T and equals one after T+1. The additional forcing is supported in [T,T+1] and is square integrable. Coarse decay makes the cut-off high part square integrable on the line. Uniqueness of the scalar L2 inverse then gives its convolution with (4.5).

For completeness, uniform graph-norm estimates follow from Fourier multipliers, and not from summing absolute values of all modes. Conjugating by exp(d t) replaces partial_t by partial_t-d. For 0<d<mu2 the multiplier denominator for mode k is

 (i xi-d)^2-(i xi-d)-lambda_k.

Its real part is d(d+1)-lambda_k-xi^2, so its absolute value is at least

 xi^2+lambda_k-d(d+1) >= c_d(xi^2+lambda_k).

Plancherel and (3.3) control two time derivatives and A Z in weighted L2, with constants uniform in k. The compact cutoff forcing is harmless. Weighted L2 of F is finite for d<beta. The interval graph estimate in Section 3 and the usual product-Sobolev mixed-derivative estimate also control the ordinary H2 norm of the bulk on fixed strips. This proves the first assertion of the consequence.

If beta>mu2, the k=2 convolution can be written as a stable coefficient times exp(-mu2 t), plus two future integrals. The coefficient exists because integral_T^infinity exp(mu2 s)|F2(s)| ds is finite by Cauchy-Schwarz on unit intervals. Subtracting it, the remaining two integrals and their first two derivatives have local L2 norm O(exp(-gamma t)) for each gamma<beta. For k>=3 repeat the multiplier argument with d<mu3. The low sector has the bounds from (4.4). This proves (4.3), including the norm (4.2). No trace of the bulk forcing at phi=0 and no derivative of its independent boundary coordinate were used.

## 5. Application to the nonlinear endpoint equations

Define

 zeta(phi,t)=O(phi,t)-c theta(t)cos(phi/2),
 Z(t)=(zeta(.,t),-c theta(t)) in H.

Because O(0,t)=0 and O(pi,t)=0, the second coordinate is exactly zeta(0,t), and zeta(pi,t)=0. The bulk equation (2.1) gives

 L zeta=R.

At phi=0, (2.2) gives

 zeta_tt(0,t)-zeta_t(0,t)=(2/pi)zeta_phi(0,t)-cN(t).

Consequently the exact state equation is

 Z''-Z'+A Z=(R,-cN).                                 (5.1)

This is the reason for the negative sign in the boundary coordinate of A. Replacing it by a spatial boundary condition involving R(0,t) would be unjustified, since R is initially only L2.

The norm in (4.2) controls ||O||_H2 plus ||theta||_H2 on fixed strips: recover theta from the boundary state and O from zeta+c theta cos. Conversely those norms control (4.2), by (3.1) and the trace theorem. Mixed bulk derivatives are controlled as noted after (4.5). Thus we may take this norm as X in (2.4).

Choose once and for all s with mu2<s<3/2. Starting with the paid coarse exponential bound, if X=O(exp(-d t)), (2.4) makes F in (5.1) decay with exponent min{d+epsilon,s}. Section 4 improves X to every exponent below min{d+epsilon,s,mu2}. Iterate in increments smaller than epsilon/2. After finitely many iterations X has an exponent d<mu2 so close to mu2 that d+epsilon>mu2. Then the forcing has an exponent beta>mu2. Applying the extraction part of Section 4 gives, for some gamma>mu2,

 Z=D h2 exp(-mu2 t)+O_(4.2)(exp(-gamma t)).            (5.2)

This is a finite bootstrap of established bounds, not an assumption that a sharper weighted norm is already finite. It also retains the case D=0.

Since theta=-Z_b/c, there is a real B such that

 theta=B exp(-mu2 t)+theta_*,
 a=-mu2 B exp(-mu2 t)+a_*,                           (5.3)

where theta_* has H2 norm O(exp(-gamma t)) on fixed intervals. In particular theta_* and a_* have uniform sup bounds at that rate. The corresponding leading O profile is

 O0(phi,t)=D[(h2)_bulk(phi)-(h2)_b cos(phi/2)]exp(-mu2 t).

The leading pair satisfies LO0=(a0'-a0)S_phi and a0'-a0=-4c O0_phi(0,t), directly from the eigenvalue and boundary equations. It remains to upgrade the L2 bound for a_*' to essential supremum; without this step a pointwise curvature conclusion would not follow.

## 6. Trace upgrade with measurable fidelity

Write V=O-O0 and b=a-a0, where a0=-mu2 B exp(-mu2 t). The H2 strip bound in (5.2) gives V=O(exp(-gamma t)) in H2 and b=O(exp(-gamma t)) in H1. For every finite p, the trace embedding H1/2 on a bounded time interval into Lp yields

 ||V_phi(0,.)||_Lp <= C_p exp(-gamma t).

The full O therefore has an Lp normal-derivative trace of order exp(-mu2 t). Formula (2.3), the coarse decaying sup norm of e_phi, and the sup bound for a from (5.3) imply, for every finite p,

 ||N||_Lp <= C_p exp(-beta0 t)

for some beta0>mu2 (take any beta0 at most min{mu2+epsilon,3mu2,s}). Subtracting the leading angle equation from (2.2) gives

 b'-b=-4c V_phi(0,.)+N.                              (6.1)

Hence b' is Lp with exponent min{gamma,beta0}>mu2, while a' has exponent mu2.

Subtract the leading bulk equation from (2.1), placing a^2 V_phiphi on the left. The exact equation is

 [partial_tt-partial_t+(1+a^2)partial_phiphi+1/4] V
   =(b'-b)S_phi+(a'-a)e_phi+2a e_tphi-a^2 O0_phiphi.  (6.2)

V has zero Dirichlet values at phi=0 and phi=pi. For each fixed p>2, item (ii) in Section 1 supplies a positive epsilon_p such that ||e_tphi||_Lp<=C_p exp(-epsilon_p t). The other terms in (6.2) were just estimated. Thus the right side has Lp norm O(exp(-gamma_p t)) for some gamma_p>mu2, after decreasing gamma_p if necessary. Also ||V||_Lp has the faster H2-strip rate gamma, by the two-dimensional Sobolev embedding.

The principal coefficients in (6.2) are uniformly elliptic and uniformly Lipschitz (a,a' were uniformly bounded already in Section 1). Fixed-strip boundary W2,p estimates therefore give

 ||V||_W2,p(inner strip_t) <= C_p exp(-gamma_p t).     (6.3)

There are no corner issues at temporal ends: the estimate is on a strictly smaller time interval, and the two spatial sides are straight Dirichlet boundaries. Equivalently one may reflect V oddly across each spatial side; the coefficients are independent of phi. Take p>2 in (6.3). The resulting C1,alpha bound gives a sup bound for V_phi(0,t) at a rate greater than mu2.

Now (2.3) has an L-infinity bound at an exponent greater than mu2: O_phi(0,t)=O0_phi(0,t)+V_phi(0,t) is uniformly O(exp(-mu2 t)), e_phi(0,t) decays at a positive rate, the cubic a term decays faster, and H2(t) has exponent s>mu2. Formula (6.1) finally gives

 ess-sup_(t<s<t+1) |a_*'(s)| <= C exp(-gamma_* t)

for some gamma_*>mu2. Combining this with (5.3), and slightly reducing the exponent to use overlapping strips, there is eta>0 such that

 theta(t)=B exp(-mu2 t)+O(exp(-(mu2+eta)t)),
 a(t)=-mu2 B exp(-mu2 t)+O(exp(-(mu2+eta)t)),
 a'(t)=mu2^2 B exp(-mu2 t)+O_ess(exp(-(mu2+eta)t)).    (6.4)

All differentiations of the measurable forcing have been avoided. This is a stronger remainder than the frozen little-o statement requires; no uniform eta or constant over minimizers is being claimed.

## 7. Return to the graph and conclusion

For shortness set mu=mu2. In terms of r=exp(-t), write

 x(r)=r cos theta(t), y(r)=r sin theta(t).

The exact first derivatives are

 x_r=cos theta+a sin theta,
 y_r=sin theta-a cos theta.

By (6.4), x_r tends to one and is positive on a small interval. The curve is therefore the graph y=psi(x). Also x=r(1+O(r^(2mu))), so replacing r by x preserves all leading powers. The first two equations in (6.4) give

 psi(x)=B x^(1+mu)+O(x^(1+mu+eta1)),
 psi'(x)=(1+mu)B x^mu+O(x^(mu+eta1))

for a possibly smaller eta1>0. The second derivative is obtained from the exact determinant, rather than by differentiating a big-O remainder:

 psi''(x(r))
    = [a'(t)-a(t)-a(t)^3]
       /[r (cos theta(t)+a(t)sin theta(t))^3]         (7.1)

almost everywhere. Formula (6.4) implies

 psi''(x)=mu(1+mu)B x^(mu-1)
                 +O_ess(x^(mu-1+eta2))

for some eta2>0. Since mu>1, this is bounded near zero and tends essentially to zero. On the remaining short part of the chart local C1,1 regularity gives the required W2,infinity bound. Together with the continuous tangent this proves psi in C1([0,delta]) intersect W2,infinity((0,delta)). The three remainder estimates imply exactly the three uniform/essential-uniform limits in STATEMENT.md, with b=B. They also give psi'(x)/x ->0, hence the classical one-sided second derivative at zero is zero.

The point p was arbitrary. No nonvanishing coefficient was assumed at any stage, so b=0 remains within the same proof. The argument proves the entire frozen statement, conditional only on the explicitly stipulated source and the identified primary inputs used in its operative endpoint framework. It does not assert a contribution grade or new-to-literature priority.
