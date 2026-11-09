# Truncated cosine: sustained mechanisms, no full source resolution

30 October 2026. Status: UNRESOLVED. No PROOF or acceptance recommendation.
Counts remain 9 additional / 39 total / next 40. Root alone counts.

## Literal endpoint and source reduction

Frozen 1003.1278v1, Conjecture 2.1, PDF p2: for every integer M>=1, every strictly increasing doubly infinite real sequence with lambda[n+M]-lambda[n]>=pi, and every finitely supported real coefficient sequence, G=sum a[n] H(x+lambda[n])^M satisfies ||G'||_2^2<=M^2||G||_2^2. H is cos on [-pi/2,pi/2] and zero outside. M=1,2 are proved in the source. A positive M=3 result alone would not resolve it. A finite negative witness at ANY M>=3 would refute the full assertion.

Put h_j=H^j for j>=1; h_0 means the indicator of the support interval, not the everywhere-one convention for zero to the zeroth power. For M>=2, h_M and its first derivative are continuous and vanish at support endpoints. Its weak second derivative is the bounded piecewise function -M^2 h_M+M(M-1)h_(M-2). There is no endpoint delta because the first derivative has no jump. Integration by parts for compactly supported H^1 functions gives

M^2||G||^2-||G'||^2=M(M-1) sum_ij a_i a_j g_M(lambda_i-lambda_j),
g_M(d)=integral h_M(t+d)h_(M-2)(t) dt.

Reflection t -> -t proves g_M(-d)=g_M(d), since both factors are even. This does not require interchanging their exponents. Source Lemma 4.1's proof retains the positive prefactor omitted in its displayed statement. This is uncredited source bookkeeping. For M=1 use disjoint interiors directly.

Finite extension is exact: retain the N finite centres, put new centres at lambda_1-k*pi to the left and lambda_N+k*pi to the right, k>=1, and assign zero coefficients. Any M-window lying inside is a hypothesis. Any crossing an end contains at least one gap pi and otherwise positive gaps, hence has span >=pi. This also covers N<M and windows crossing both ends. Both tails diverge. No bridge from a finite negative witness remains.

Spacing implies K_ij=0 if |i-j|>=M. At most M centres lie in an OPEN interval of length pi; a CLOSED interval may contain M+1 when the first and last are exactly pi apart. The overlap at equality has measure zero. Closed-interval count <=M is false.

## Mechanism 1: asymmetric clusters, exact basis, leading form

Use clusters lambda[j,i]=j*pi+epsilon*u[j,i], 0<=i<M, with increasing offsets inside each cluster, and u[j+1,i]>=u[j,i]. For epsilon small enough to keep successive clusters ordered, every M-step difference is exactly pi+epsilon*(u[j+1,i]-u[j,i])>=pi. There is no rescaling by a possibly negative minimum. At positive common scale c, linear constraints c*s>=pi require s>0 before division; scaling signed linear constraints without that sign check is invalid.

The exact divided-difference basis has column k coefficients
B[j,k]=epsilon^(-k)/product_(l<=k,l!=j)(u_j-u_l), j<=k,
and zero otherwise. Its interior limit is h_M^(k)/k!. It is invertible for every positive epsilon and distinct nodes. Congruence B^T K B preserves inertia. cluster.py uses three clusters, M=3,4,5,6, offsets u[j,i]=i(i+1)/2+j*D_i, with D_i=0, i+1, or M*1_(i=M-1), and epsilon/pi=1/100,1/1000,1/10000. All 36 matrices had positive 65-digit numerical minima. These are NOT interval certificates; no negative candidate survives.

### Analytic leading term at M=3

This is a new sustained reduction of the proposed mechanism, NOT a source-wide result. Write each cluster's three offsets u0<u1<u2, weights w_i=1/product_(l!=i)(u_i-u_l). The divided differences satisfy sum w_i=sum w_i*u_i=0 and sum w_i*u_i^2=1. In the limiting basis (h,h',h''/2), the null vector is q=(1,0,2): h''+h=-2 cos(3x) inside the support. Parseval on the length-pi interval gives exactly one null direction and a positive complementary form. There is no proposed counterexample at complete coalescence.

The source's explicit g_3 gives the one-sided expansions
g_3(d)=3*pi/8-3*pi*d^2/16+pi*d^4/64+d^5/20+R_0(d),
g_3(pi-s)=s^5/20+R_pi(s),
with |R_0(d)|<=D6*d^6/720, |R_pi(s)|<=D6*s^6/720 for 0<=d,s<=pi, and D6=(12*pi+810)/32. Indeed the sixth derivative of [12(pi-d)cos d+9 sin d+sin(3d)]/32 is bounded by (12*pi+72+9+3^6)/32 throughout this interval. This is an explicit uniform Taylor bound, not a fitted asymptotic.

On the direct sum of cluster null vectors, the first-order Gram form is 4*epsilon*C, where C is tridiagonal and
C[j,j]=sum_ab w[j,a]w[j,b]|u[j,a]-u[j,b]|^5/20,
C[j,j+1]=sum_ab w[j,a]w[j+1,b](u[j,a]-u[j+1,b])_+^5/20.
All other offdiagonal entries are zero for sufficiently small epsilon. Even Taylor terms contribute zero at order zero on this null space and no term linear in epsilon: the denominators are epsilon^0, epsilon^2, epsilon^4. The cusp supplies the displayed linear term. For bounded offsets, the remainder after congruence is explicitly bounded by the above entry remainder times absolute basis coefficients; the worst epsilon power is epsilon^6/epsilon^4=epsilon^2. Polynomial even-term corrections are also explicit O(epsilon^2). No constant uniform over unbounded offsets or arbitrary N is asserted.

### Proof that this entire leading mechanism is nonnegative

Define b_u(s)=sum_i w_i(s-u_i)_+. It is the nonnegative triangular spline on [u0,u2], with integral 1/2. Its second distributional derivative is sum_i w_i delta_(u_i). Integration by parts twice in each variable, with compact support and zero boundary terms, yields
C[j,j]=6 integral integral b_u(s)b_u(t)|s-t| ds dt,
C[j,j+1]=6 integral integral b_u(s)b_v(t)(s-t)_+ ds dt.
The fourth mixed derivatives of |s-t|^5 and (s-t)_+^5 are respectively 120|s-t| and 120(s-t)_+; there is no delta at this derivative order. This verifies the constants.

The probability density 2*b_u is that of X_u=sum_i Z_i*u_i, where (Z0,Z1,Z2) is uniform on the probability simplex. This follows directly by the piecewise linear slice areas (or by integrating the displayed two linear pieces). If u_i<=v_i, the same Z couples X_u<=X_v. For independent variables with these marginal laws,
C[j,j]=(3/2) E|X_u-X'_u|,
C[j,j+1]=(3/2) E(X_u-X_v)_+.
Stochastic order shows that each adjacent offdiagonal at row j is <=(3/4)E|X_u-X'_u|=C[j,j]/2. Thus C has nonnegative offdiagonals and C[j,j]>=C[j,j-1]+C[j,j+1]. The exact source-M2-style decomposition
z^T C z=sum_j C[j,j+1](z_j+z_(j+1))^2+sum_j (C[j,j]-C[j,j-1]-C[j,j+1])z_j^2
proves PSD for ANY finite number of componentwise ordered three-node clusters. Each connected component has an end row with strictly positive slack, so the finite leading form is positive definite. This rules out a negative leading term throughout this class, not merely at enumerated samples.

leading.py independently checks rational LDL pivots for all 980 monotone three-cluster chains chosen from the 20 triples in {0,...,5}. Every pivot is positive; the smallest is exactly 7/15. This is a certificate for the finite list of LEADING matrices only. The analytic argument, not the finite enumeration, covers arbitrary cluster count in this restricted leading-order problem.

The missing bridge is material: in long equal-cluster chains the leading tridiagonal form approaches a critical Toeplitz form; its least eigenvalue decays with chain length. An O(epsilon^2) error estimate does not preserve an O(epsilon/N^2) lower bound uniformly in N. Schur elimination of the positive complementary modes changes the null form at order epsilon^2. Neither this calculation nor positivity at M=3 proves the all-M conjecture.

## Mechanism 2: banded factorization and actual spline comparison

Source M=2, Lemmas5.1-5.2, pp4-5: all overlaps are nearest-neighbour, and g2(a)+g2(b)<=g2(0) when a+b>=pi gives the square decomposition. For M>=3 the same pair-square formula is an identity but the diagonal slack can be negative: three nearly coincident centres give two offdiagonals near g_M(0), larger than the diagonal. Such a cluster extends feasibly; this obstruction is real. Thus scalar diagonal dominance does not generalize directly to the original K.

A true banded Schur certificate must prove, for every N, nonnegative pivots of K (and zero-pivot compatibility). With bandwidth M-1 its update is S_ij=K_ij-K_i1*K_1j/K_11. Sampling pivots is not such an invariant. The leading spline argument above provides an exact spacing-aware decomposition after removing confluent positive modes, but no finite-epsilon invariant was found.

Actual retrieved proof body 1708.08110v1, pp1-5, treats polynomial minimal-defect splines on equally spaced knots, using a periodic Fourier multiplier, alias sums, and Euler-Frobenius roots. The proof explicitly factors a common periodic coefficient multiplier. Irregular real translates of truncated cosine powers have no such periodic multiplier, and are trigonometric pieces rather than the stated polynomial B-splines. It cannot be invoked. The previously frozen 1708.08116v1 orthonormal integer-shift generator result has the same missing translation-structure bridge. No irregular-translate or local-density inverse theorem was body-verified here; irregular.xml and extra1.xml show the bounded searches, mostly irrelevant or empty. This is a documented shortfall, not a subsumption claim.

The Fourier sign-changing obstruction from r243 remains: hat(g_M)=(M^2-omega^2)|hat(h_M)|^2/[M(M-1)]. Arbitrary-configuration positive definiteness is false. Neither generic Bochner nor integer-shift spline inequalities solve the constrained problem. No finite witness was found; no interval negativity certification was attempted without one.
