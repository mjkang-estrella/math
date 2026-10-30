# Author proof at the unchanged r220 frozen scope

This is a discovery-stage author proof of STATEMENT.md, SHA256 4c71274685f1401193eccbc7c6997b56d1ca2db88fef14cba159d638260aa35d. It is not an independent review, manuscript, formalization, release, or mathematical grade. The source theorem and its operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The proof below explicitly transports the relevant matrix operations to the frozen abstract hypotheses; it does not assert that arbitrary charts in the statement are geometrically realizable.

All integrals below are Lebesgue integrals. Matrix norms in estimates are Frobenius norms; spectral bounds use the operator order. A symbol c or C denotes a positive constant depending only on the frozen parameters indicated in that step, and may change between lines. None depends on the chart A, its middle residue B, the defect Delta, or the auxiliary small numbers rho and eta. Finite-dimensional norm comparisons have constants depending only on m,k. The final constant can be the maximum of the finitely many constants for j=0,...,q-1. The derivation uses explicit algebraic, trigonometric, exponential and finite-interval bounds, so no compactness-only modulus is hidden in C.

## 1. Matrix geometry and the exact nonnegative decomposition

Write h0(t)=csc²(t) on (0,T), p0(t)=4csc²(2t) on (0,D), and

h=det(H')^(1/m), s=det(S)^(1/k), s_i(t)=s(t+iD), i=0,1.

By hypothesis 2, h/h0 and s_i/p0 lie between K^(-1) and K. Consequently their logarithms g_H and g_i have absolute value at most log K. Put

M_H=H'/h, M_i(t)=S(t+iD)/s_i(t).

These matrices have determinant one and eigenvalues in [K^(-2),K²]. H' is positive on all of (0,T), including D. Thus for x<y, H(y)-H(x)=integral_x^y H' is positive definite, even when the interval crosses D. Its sign reverses if the actual order is reversed.

The block determinant identity gives

f=f_H f_K,
f_H=|det(H(y)-H(x))| / sqrt(det H'(x) det H'(y)),
f_K=|det Q(x,y)| / sqrt(det S(x) det S(y)).                    (1)

The identity det A'=det H' det S follows by the same block elimination. These are identities off the diagonal, with continuous limiting interpretations where needed.

For fixed x,y let R=(C(y)-C(x))(H(y)-H(x))^(-1). Direct differentiation gives, at either endpoint z=x or z=y,

partial_y Q = S(y)+(R-C'(y)H'(y)^(-1))H'(y)(R-C'(y)H'(y)^(-1))^T,
-partial_x Q = S(x)+(R-C'(x)H'(x)^(-1))H'(x)(R-C'(x)H'(x)^(-1))^T.       (2)

The calculation requires invertibility, not positivity, of the endpoint difference of H. Taylor expansion within one half-period gives Q(x,y)=(y-x)S(x)+o(|y-x|), so Q has zero diagonal limit. The assumed cut-pair zero and endpoint exchange give zero at both orders of a matched cut pair.

For 0<u<v<D and i,j in {0,1}, set Q_ij=Q(u+iD,v+jD), I_i=integral_u^v S(t+iD) dt. Integrating the first identity of (2) from the matched pair (u+iD,u+jD), and the second towards the matched pair (v+iD,v+jD), proves

Q_ij >= I_i >0,  Q_ij >= I_j >0.                            (3)

Both moving endpoints remain in their own open half-period. This includes i=1,j=0, whose actual endpoint order is reversed. In particular f is positive off the diagonal, cut lines and chart-pole lines.

For a positive matrix function P(t) of size r, let p(t)=det(P(t))^(1/r), I=integral P, a=integral p, and define

D_P(x,y)=log det I-r log a.

The matrix N=P/p has determinant one. With probability measure dmu=p(t)dt/a, I=a E_mu N, hence

D_P=log det(E_mu N)>=0.                                    (4)

For completeness, concavity of logdet gives the inequality because logdet N=0. Concavity itself follows by twice differentiating along positive segments: the second derivative is -tr(Z^(-1)U Z^(-1)U)<=0. This is the actual logdet calculation read in Boyd--Vandenberghe §3.1.5, not an appeal to the determinant-root exercise as a proved theorem. Equivalently the determinant-root bound used in Source344 follows directly from det(M)^(1/r)=inf_(P>0,det P=1) tr(PM)/r.

Use D_H for P=H' on (0,T), and D_i for P(t)=S(t+iD) on (0,D). Define also

E_ij(u,v)=log det Q_ij - (log det I_i+log det I_j)/2 >=0,      (5)

where (3) proves the sign. These are genuine retained matrix remainders, not absolute values of potentially cancelling errors.

For b>0, lambda=pi/b and p_b(t)=lambda² csc²(lambda t), define

dnu_xy(t)=p_b(t)dt/P_b(x,y),  P_b=integral_x^y p_b,
J_b(g;x,y)=log integral exp(g) dnu_xy - integral g dnu_xy.

The exact chord identity is

P_b(x,y)=lambda sin(lambda(y-x))/(sin(lambda x)sin(lambda y)).

If W>=0 is symmetric about b/2 and W(z)/sin(lambda z) is bounded, the scalar identity read and proved in Source344, weighted:scalar, is

integral_(0<x<y<b) W(y-x)[log(integral p_b e^g/P_b)-(g(x)+g(y))/2]
 = integral_(0<x<y<b) W(y-x) J_b(g;x,y).                    (6)

Here g is bounded. Its linear cancellation can be checked independently as follows. The coefficient of g(t) from the interval average is

p_b(t) integral_(x<t<y) W(y-x)/P_b(x,y) dxdy = (1/2) integral_0^b W.

To obtain this equality, differentiate the double integral after inserting the chord identity: its derivative is (integral W) sin(lambda t)cos(lambda t), and its value at zero is zero. The equal endpoint coefficient is (1/2)[integral_0^t W+integral_0^(b-t) W]=(1/2)integral W. Bounded g justifies Fubini. This is the logarithmic form of Kazdan's original E.4--E.16 cancellation, already paid; no new scalar cancellation is being asserted.

Set w_xy=w(|y-x|), Phi(r)=r-1-log r, and on the exceptional measure-zero lines ignore logarithms. For the H factor, taking logs of (1) gives exactly

log(f_H/sin^m(y-x))=D_H+m[log(integral_x^y h/integral_x^y h0)-(g_H(x)+g_H(y))/2]

when x<y. For the K factor in folded coordinates, the corresponding identity is

log(f_K/|sin(2(y-x))/2|^k)
 = E_ij+(D_i+D_j)/2
   +(k/2)[A_i+A_j-g_i(u)-g_j(v)],                           (7)

where A_i=log(integral_u^v s_i/integral_u^v p0). The four weights are

w_ij(z)=(sin(2z)/2)^k [[sin^m z,cos^m z],[cos^m z,sin^m z]]_ij,
W_D(z)=(sin^m z+cos^m z)(sin(2z)/2)^k.

Each row and column sums to W_D, which is symmetric about D/2. Also w(z)/sin z and W_D(z)/sin(2z) are bounded because m,k>=1. Thus (6) applies to the H block and separately to both fast profiles. The four folded triangles and their transposes cover the square except the exceptional lines, with Jacobian one. Therefore the following equality holds:

Delta = 2m integral_Delta_T w J_T(g_H)
      + 2 integral_Delta_T w D_H
      + 2k sum_i integral_Delta_D W_D J_D(g_i)
      + 2 sum_i integral_Delta_D W_D D_i
      + 2 sum_(i,j) integral_Delta_D w_ij E_ij
      + integral_[0,T]^2 w_xy Phi(f/w_xy).                  (8)

Every term is nonnegative. This is the source's full compatible composition, retaining the matrix slacks instead of discarding them.

There is no implicit infinite-minus-infinite operation in (8). The bounded profile ratios and determinant-root inequalities give uniform lower bounds for log(f_H/sin^m) and log(f_K/|sin(2z)/2|^k). The positive part of w_xy log(f/w_xy) is bounded by f. Hypothesis 5 makes f bounded on the square. Each individual logarithm is therefore absolutely integrable with weight w. The scalar terms in (6)--(7) are bounded; the remaining D and E terms are nonnegative, so the equality itself proves their finiteness. This also establishes Delta>=0.

As a subsidiary density estimate, Phi(r)>=(sqrt(r)-1)², since the difference equals 2(sqrt(r)-1-log sqrt(r)). Consequently

integral (sqrt f-sqrt w_xy)² <= Delta,
integral |f-w_xy| <= sqrt(Delta(4W+2Delta)), W=integral w_xy.  (9)

The second bound follows from Cauchy--Schwarz and integral (sqrt f+sqrt w)²<=2 integral(f+w)=4W+2Delta. We do not use (9) to infer matrix, curvature or metric convergence.

## 2. Uniform variance bounds

For |g|<=L and any probability measure nu,

J(g)=log E_nu exp(g)-E_nu g >= (e^(-2L)/2) Var_nu(g).        (10)

Indeed F(s)=log E exp(sg) has F''(s)=Var_nu_s(g). The tilted density exp(sg)/E exp(sg) is at least e^(-2L) for 0<=s<=1. Using Var_mu(g)=inf_c integral(g-c)²dmu gives F''(s)>=e^(-2L)Var_nu(g); integrate with weight 1-s. This proves (10), including its constant, without an unproved quantitative Jensen citation.

For positive matrices N with eigenvalues at most Lambda, strong convexity of -logdet on that convex spectral region gives

log det(E_mu N)-E_mu log det N
 >= (1/(2 Lambda²)) E_mu ||N-E_mu N||_F².                   (11)

To check this, its Hessian at Z in direction U is tr(Z^(-1)U Z^(-1)U)>=Lambda^(-2)||U||_F². Taylor's integral formula about E_mu N, followed by averaging, cancels the linear term. In (4), E logdet N=0, Lambda=K², and (11) applies to D_H,D_i.

Fix 0<rho<=r0 and for b=T or D use the endpoint rectangle

X_rho=[rho/4,rho/2], Y_(b,rho)=[b-rho/2,b-rho/4],
K_(b,rho)=[rho,b-rho].

Every (x,y) in this rectangle encloses K_(b,rho); the rectangle has area rho²/16. The chord integral is at most 1/x+1/(b-y)<=8/rho, since lambda cot(lambda x)<=1/x. Also p_b>=lambda². Thus on K_(b,rho),

dnu_xy/dt >= lambda² rho/8.                               (12)

For the matrix means in (4), the actual density h/integral h, or s_i/integral s_i, is at least K^(-2) times the corresponding reference density. The pairwise variance identity

Var_mu(F)=(1/2) integral integral ||F(t)-F(s)||² dmu(t)dmu(s)

then implies, on restricting both variables to K_(b,rho), a lower bound c rho² times integral_K ||F-bar F_K||². Here bar F_K is the unweighted mean on K; its length is at least b/2, and the identity integral_K²||F(t)-F(s)||²=2|K| integral_K||F-bar F_K||² accounts for the factor. The constants are uniform in rho.

For z=y-x in the rectangle with b=T, T-z lies in [rho/2,rho]. The elementary sine bound sin t>=2t/pi on [0,pi/2] gives

w(z)>=(rho/pi)^d.                                         (13)

With b=D the same argument gives

W_D(z)>=2^(-m/2)(rho/pi)^k,
w_00(z)=w_11(z)>=2^(-m/2)(rho/pi)^k.                        (14)

For (14), sin z=cos(D-z)>=1/sqrt2 and sin(2z)/2=sin(2(D-z))/2>=rho/pi. All arguments are in the indicated sine range because rho<=r0.

Apply (10)--(14) to the first four nonnegative terms of (8). For each of F=g_H and F=M_H-I_m,

integral_K_(T,rho) ||F-bar F_K||² <= C Delta rho^(-(d+4)).   (15)

For each i and each of F=g_i and F=M_i-I_k on (0,D),

integral_K_(D,rho) ||F-bar F_K||² <= C Delta rho^(-(k+4)).   (16)

The exponent consists of two powers from rectangle area, two from the pairwise probability densities, and d or k from the weight. No pointwise inversion of a vanishing weight has been used.

## 3. The coupling block is controlled by the same defect

Write L(t)=C'(t)H'(t)^(-1), a k by m matrix. On any interval [x,y] contained in one half-period put

L_bar=(integral_x^y C')(integral_x^y H')^(-1).

Expansion of both sides, using integral C'=L_bar integral H', gives the exact covariance identity

Q(x,y)-integral_x^y S
 = integral_x^y (L-L_bar)H'(L-L_bar)^T.                     (17)

This identity is the integrated form of the classical Schur-complement minimization. It is valid for noncommuting matrices; multiplication order has been kept explicitly. It follows directly from V'=S+L H' L^T, C'=L H', and the definition of Q.

On a same-half endpoint rectangle, the pole expansions imply ||V(x)||+||V(y)||<=C/rho, on both half-periods. Since Delta H>0 and Q>0 there,

Q <= V(y)-V(x),  lambda_max(Q)<=C/rho.                     (18)

Let P=integral_x^y S and R=Q-P>=0. Integrating the derivative of logdet(P+tR) and using P+tR<=Q gives

E_ii=logdet Q-logdet P >= lambda_max(Q)^(-1) tr R.

Also H'>=K^(-1)I, by hypothesis 2. Thus (17)--(18) give

E_ii >= c rho integral_x^y ||L-L_bar||²
      >= c rho integral_K ||L-bar L_K||².                 (19)

The last inequality first restricts to the common enclosed K, then minimizes over the constant matrix. It does not identify the weighted L_bar with an unweighted mean.

Integrate (19) over the rectangle, use (14), and retain the i=i term of (8). In folded coordinates L_i(t)=L(t+iD),

integral_K_(D,rho) ||L_i-bar L_i,K||²
 <= C Delta rho^(-(k+3)).                                 (20)

This is the required coupling estimate. Merely controlling determinant roots would not have supplied it.

## 4. Exterior poles calibrate the unknown constants

The finite atlas in hypothesis 3 covers I. In particular C' is uniformly bounded, while H'^(-1)<=K sin² t I, so L is uniformly bounded. The exterior pole expansions and their first derivatives give, uniformly near t=0 and near T with tau=T-t,

P_H(t):=sin² t H'(t)=I_m+O(t²) or I_m+O(tau²),
P_S(t):=(sin²(2t)/4)S(t)=I_k+O(t²) or I_k+O(tau²),
L(t)=O(t²) or O(tau²).                                    (21)

For example H'=t^(-2)I+R'_{0,H}, C'=R'_{0,C}, and S=t^(-2)I+R'_{0,V}-C'H'^(-1)(C')^T. The bounds in (21) follow from sin²t=t²+O(t⁴), sin²(2t)/4=t²+O(t⁴), and the uniform bounds on the remainders and inverse H'. Matrix determinant roots and their logarithms are Lipschitz on the specified compact positive spectral region. Therefore g_H,M_H-I,g_0,M_0-I are O(t²) at zero. The second folded profile g_1,M_1-I and L_1 are O((D-t)²) at t=D. These are quantitative estimates with constants depending on m,k,K, not just asymptotic identities for an individual chart.

We use a simple calibration inequality. If a vector/matrix function F on K=[rho,b-rho] satisfies

integral_K ||F-bar F_K||² <= C Delta rho^(-p)

and ||F(t)||<=C t² on [rho,2rho], then averaging on that interval gives

||bar F_K|| <= C sqrt(Delta) rho^(-(p+1)/2)+C rho²,
||F||_(L²(K)) <= C[sqrt(Delta) rho^(-(p+1)/2)+rho²].         (22)

Use the interval [b-2rho,b-rho] if the known normalization is at the right endpoint. To prove (22), the mean of ||F-bar F_K|| on an interval of length rho is at most rho^(-1/2) times its L² norm, while the mean of ||F|| there is at most 4C rho². The L² estimate follows by the triangle inequality and the uniformly bounded length of K.

Suppose first 0<Delta<=delta_* and choose

rho=Delta^(1/(d+9)), eta=rho^(3/4).

The definition of delta_* gives eta<=min(r0,a/4), hence rho<=r0, rho<=eta, and all the endpoint rectangles and calibration intervals are admissible. Since d=m+k and m>=1, all p in (15),(16),(20) are at most d+4. Substitution in (22) gives C rho² in every case. Converting g and determinant-one M back to P=e^g M, using bounded spectra and bounded g, yields

||P_H-I_m||_(L²([rho,T-rho])) <= C rho²,
||P_S-I_k||_(L²([rho,D-rho] union [D+rho,T-rho])) <= C rho²,
||L||_(L²([rho,D-rho] union [D+rho,T-rho])) <= C rho².        (23)

For example the largest calibration term is sqrt(Delta)rho^(-(d+5)/2)=rho². In the fast and coupling blocks its exponent is at least two. This checks that one common rho works; choosing incompatible separate scales is unnecessary.

## 5. The middle residue and one common shear

Write tau=t-D. Hypothesis 3 and the bound on H'^(-1) near D give

S(t)=tau^(-2)B+O(1),
P_S(t)=B+O(tau²),                                          (24)

uniformly on 0<|tau|<=4r0. In detail V'=tau^(-2)B+R'_{D,V}, while H',C' have bounded smooth extensions there and H'^(-1) is uniformly bounded by hypothesis 2. The expansion sin²(2t)/4=tau²+O(tau⁴) proves (24).

Apply (23)--(24) on [D-2rho,D-rho], an interval of length rho. Taking its L² norm gives

||B-I_k|| <= C rho^(-1/2) rho²+C rho² <= C rho^(3/2).       (25)

We have not fixed B to I as an extra hypothesis.

Set F(t)=A(t)-A_mod(t)-R_D(D). At either t=D+eta or D-eta, the pole expansions, the mean-value bound for R_D, and A_mod(t)=-diag(I_k,0)/tau+O(tau) give

||F(D +/- eta)|| <= C[||B-I||/eta+eta].                    (26)

The same R_D(D) appears on the two sides because hypothesis 3 requires one remainder extending across D. This is precisely where the compatible marking of the two branches enters.

For t in the wider set J_(a/2), integrate F' between t and the point D +/- eta on its own half-period. The entire path lies in [a/2,T-a/2] and has distance at least eta from D, except for its endpoint at that distance. On these paths h0=csc²t is bounded by a constant depending on a. From H'=h0 P_H, C'=L H', V'=S+L H'L^T and S=4csc²(2t)P_S, the three blocks satisfy

integral ||H'-H'_mod|| <= C_a rho²,
integral ||C'|| <= C_a rho²,
integral ||V'-V'_mod|| <= C_a[rho² eta^(-3/2)+rho⁴].        (27)

For the last estimate use Cauchy--Schwarz for the normalized S error in (23) and

integral_path [4csc²(2t)]² dt <= C_a eta^(-3).

This follows by comparison with |t-D|^(-4) near D; the other pole is bounded away by a/2. The coupling square has integral at most C_a integral ||L||²<=C_a rho⁴. All the paths are subsets of the domains in (23) because eta>=rho and eta<=a/4.

Combining (25)--(27),

||F||_(C^0(J_(a/2)))
 <= C_a[rho^(3/2)/eta+eta+rho² eta^(-3/2)+rho²+rho⁴]
 <= C_a rho^(3/4)=C_a Delta^gamma.                         (28)

Indeed eta=rho^(3/4), and the three leading exponents are 3/4,3/4,7/8. All remaining exponents are larger, and rho<1. This completes the common-gauge estimate, including the formerly free middle residue.

## 6. Derivatives and zero defect

The finite atlas bounds in hypothesis 3 imply a uniform C^q bound for A on J_(a/2): outside the pole neighborhoods this is an explicit assumption; inside them each derivative of the rational pole term is bounded because J_(a/2) stays a fixed positive distance from its pole, while the remainder is C^q bounded. The same holds for A_mod, and ||R_D(D)||<=K. Thus

||F||_(C^q(J_(a/2))) <= C(m,k,q,K,a).                      (29)

Finite-interval interpolation, applied on each component of J_a inside the corresponding component of J_(a/2), gives, for 0<=j<q,

||F^(j)||_(C^0(J_a))
 <= C_a[||F||_C0^(1-j/q) ||F||_Cq^(j/q)+||F||_C0].        (30)

One direct proof takes q equally spaced nearby points, applies Taylor's formula with integral qth-derivative remainder, and solves the fixed Vandermonde system for the derivative. With step h the bound is C(epsilon h^(-j)+M h^(q-j)); choose h=(epsilon/M)^(1/q), capped by a fixed fraction of the distance to the wider interval boundary. The capped case contributes the additive C_a epsilon. This proves the uniform form (30) without a regularity improvement assumption.

Combining (28)--(30) and Delta<1 proves exactly

sup_(J_a)||F^(j)|| <= C Delta^(gamma(1-j/q))

for every j in the frozen range, with one common final constant C.

If Delta=0, keep rho arbitrary in (15)--(22). The variance terms vanish; (22) gives the same O(rho²) normalized estimates. Equations (24)--(28), with eta=rho^(3/4) and arbitrarily small rho, show F=0 on J_(a/2). Its derivatives there are zero. Thus the zero-defect conclusion also holds and does not require taking a fractional power of zero to define an auxiliary interval. This finishes the proof of every clause in STATEMENT.md.

The coordinate operation is the single linear symplectic shear (q_coord,p_coord) -> (q_coord,p_coord-C_*q_coord). It is symplectic because C_* is symmetric, fixes the vertical plane, and sends the graph of A to the graph of A-C_*. It changes neither A' nor any endpoint difference and hence preserves f and Delta. No time reparametrization is part of the conclusion.

## 7. Nonempty scope and limits of the operation

For fixed m,k,q, let psi_epsilon(t)=t+epsilon sin³(4t), with |epsilon|<1/24. Its derivative is 1+12epsilon sin²(4t)cos(4t)>0, psi(t+D)=psi(t)+D, and its derivatives at 0,D,T have first derivative one. Define

A_epsilon(t)=diag(-2cot(2psi_epsilon(t))I_k,-cot(psi_epsilon(t))I_m).

The pole residues are I at all three poles, the remainders extend smoothly, and Q(u,u+D)=0. The normalized velocities are positive and extend across each endpoint. On a small closed epsilon interval all frozen bounds hold for some finite K (depending on m,k,q and that interval). Its determinant is

f_epsilon(x,y)=sin^m(psi(y)-psi(x)) |sin(2(psi(y)-psi(x)))/2|^k
              / (psi'(x)psi'(y))^(d/2)

for x<y, extended symmetrically; it is continuous on the square. Since psi(t)=t+64epsilon t³+O(t^5), the H logarithmic profile has expansion g_H(t)=64epsilon t²+O(t^4). For epsilon nonzero it is nonconstant. The strict scalar Jensen gap in (8) is positive on an open set of intervals, so Delta>0. Thus the quantitative theorem is not vacuous on its abstract domain. It does not contradict Source344, which already forces the charts of a globally Blaschke Riemannian metric to be those of a standard model.

The proof uses exact cut pairs, one compatible pole remainder across D, and uniform chart bounds. A small global inj/diam defect alone supplies none of these exact hypotheses. We claim no metric near-equality rate, no curvature estimate, no quotient regularity, no extension to singular metrics, and no geometric reconstruction from determinant data. The compactness baseline and the exact source equality case remain paid constructions. Whether the full uniform matrix-chart operation has a substantial contribution beyond compatible classical quantitative convexity and endpoint estimates is left to the parent's separate contribution review; no literature-priority claim is made here.
