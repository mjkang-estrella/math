# All-deficit weighted primitive reduction

Author supporting calculation, not a proof or narrowed replacement of the frozen target. It retains all mixed blocks. Parent supplied the covariance-gap normalization; the Gaussian primitive construction and commuting comparison below are author derivations.

## 1. A retained covariance remainder and polar normalization

Use source notation B=sum X_r² and

 W=(37I/40+3B/40)^(-1), s=40/37, C=Cov(F),
 D=W^(1/2) C W^(1/2), G=tr D-log det D-m.

Here F is the centered Gaussian Brenier transport to the nonlinear affine normalization. The source matrix.tex155–205 supporting-plane inequality discards EXACTLY G. Carrying it unchanged through matrix.tex526–590 yields, for EVERY deficit,

  2delta >= G+||gradientY||²/1000+Omega_B/1000.        (1)

The previously stated ||Y||²<=1000delta also remains. G>=0 by the scalar function u-1-log u. This is paid proof reuse, not a new input theorem.

For original centered isotropic X realized as X=P^(-1)F, C=P². Set Q=D^(-1/2)W^(1/2)P; QQ*=I, so Q is orthogonal. Under this very coupling W^(1/2)F=D^(1/2)QX. Hence

 E|W^(1/2)F-QX|²=tr(D+I-2sqrt D)<=G<=2delta.         (2)

The scalar comparison follows because u-1-log u-(sqrt u-1)²=2(sqrt u-1-log sqrt u)>=0. No inverse-covariance bound, B operator bound, or discarded rank is used.

## 2. An explicit primitive of an arbitrary linear matrix pencil

For a finite family of real symmetric matrices X_r let L(x)=sum x_rX_r, K(x)=q(L(x)). This K belongs to Gaussian L2 since q is Lipschitz and has linear growth. Let N=-Delta+x·gradient. For each output coordinate j define the centered h_j by

  h_j=N^(-1) sum_i (x_i-partial_i)K_ij,               (3)

where (3) is first interpreted by Gaussian Sobolev duality. Equivalently h is the unique centered H1 minimizer of

  sum_j E|gradient h_j-K_·j|².

Existence follows from the closedness of the gradient range on centered Gaussian H1: Poincare makes the gradient norm complete. The variational equation is E<gradient h_j,gradient phi>=E<K_·j,gradient phi>. Thus Pi K:=gradient h is the orthogonal projection onto that closed range, applied COLUMNWISE. Formula(3) follows from the variational equation; it is not an assumption of classical differentiability.

For a symmetric J=DF, its j-th column is gradient F_j. Projection contraction and Poincare give

  ||F-h||2<=||J-K||2,  epsilon_T²:=||(I-Pi)K||2²<=||J-K||2².  (4)

Constant linear combinations of the output columns commute with Pi. With Psi_T=W^(1/2)h, the weighted estimate is

  ||W^(1/2)(F-h)||2²
    <=||(J-K)W^(1/2)||2²<=s||J-K||2².               (5)

The right multiplication is intentional: our columns encode output coordinates, so the usual Jacobian of W^(1/2)h is the TRANSPOSE of (Pi K)W^(1/2). This resolves the potential row/column curl ambiguity. The curl acting on the first two indices of K vanishes for these column gradients. No symmetry of the weighted Jacobian is asserted.

For source coefficients, spectral Lipschitz contraction gives ||J-K||²<=||Y||²<=1000delta. Combining (2),(5) in the SAME Gaussian coupling yields

 E|Psi_T-QX|² <= A delta,
 A=(sqrt(2)+sqrt(1000s))².                           (6)

Moreover epsilon_T²<=1000delta and Omega_B<=2000delta. All assertions hold without a small-deficit or Bop restriction.

This is an exact all-deficit reduction to a Gaussian function determined by finitely many matrices; it has not constructed exponential factors. In particular one may not replace q(L) by q of a compressed pencil: the primitive retains every block of L.

## 3. A sufficient weighted rounding statement, still unproved

For each arbitrary symmetric-slice tensor T (no full tensor symmetry assumed), form B, W, K, h, Psi_T and epsilon_T exactly as above. A sufficient deterministic/stochastic matrix-pencil theorem would be

 inf_(U orthogonal) W2²(Law(Psi_T),Law(U(E-1)))
      <=C0[Omega_B+epsilon_T²],                     (WR)

with universal C0 and all dimensions. Together with (6) and W2 triangle, WR gives the frozen full theorem with C=2A+6000C0. WR is NOT proved, and its validity for the full arbitrary-pencil class must itself be tested. It is stronger than needed if some pencils do not come from source transports. Its formulation is not a claimed equivalence to the full log-concave target.

The stronger available H1(Y) remainder can help test mixed-block coercivity, but (3)–(6) require only its L2 part. No informal derivative bound with a hidden Bop appears.

## 4. Commuting fully symmetric pencils: an all-deficit check

This paragraph verifies WR in the classical diagonalizable tensor subclass, with constants independent of dimension and of all scalar scales. It is supporting paid-algebra/scalar calculus, not a nomination.

Suppose T is fully symmetric and its slices commute. A simultaneous orthogonal basis and full symmetry give T=sum_i c_i u_i^tensor3, with arbitrary real c_i (zero allowed). After the common rotation, L=diag(c_i x_i), K is already a column-gradient field and epsilon_T=0. Its centered primitive has independent coordinates

 h_i(G_i)=[t(c_iG_i)-E t(c_iG_i)]/c_i  (c_i!=0),
 h_i(G_i)=q(0)G_i  (c_i=0).

Consequently Psi_T has coordinates r_c(G)=w(c²)^(1/2)h_c(G), w(lambda)=(37/40+3lambda/40)^(-1). For c>0 couple it to t(G)-1; for c<0 couple it to -(t(-G)-1). Either sign is an orthogonal image of a centered exponential. At c=0 either sign may be used.

There is an absolute K0 with

 E|r_c(G)-sign(c)(t(sign(c)G)-1)|²<=K0 omega(c²).      (7)

To prove it, first consider 1/2<=|c|<=3/2. Scalar differentiation of h_c, centering, q Lipschitz and |q(a)|<=q(0)+|a| bound its c-derivative in L2(G) uniformly on this compact interval (the derivative is a linear combination of t(cG)/c² and Gq(cG)/c; t has at most quadratic growth). The weight w and derivative are bounded there. At |c|=1 the two coupled variables agree exactly. Thus the left side is <=K1(|c|-1)². The explicit omega has omega(c²)>=k1(c²-1)² throughout this compact interval, with k1>0, hence this proves(7) there.

Outside that interval, Poincare applied to h_c gives

 Var(r_c)<=w(c²) E q(cG)²
       <=2w(c²)(q(0)²+c²)<=K2,

also valid at c=0. Thus the coupled squared distance is <=2K2+2. Meanwhile omega(c²) has a positive infimum on {|c|<=1/2 or |c|>=3/2}: it is continuous, has its only zero at c²=1, and grows at infinity. This proves(7) globally. Sum the independent coordinate costs to establish WR for this subclass.

Thus arbitrary large or small commuting scales do NOT obstruct the weighted all-deficit architecture. The missing issue is mixed noncommuting structure and its quantitative relation to epsilon_T, not scalar frequency/amplitude growth or covariance normalization.

## 5. Extension to every commuting symmetric-slice pencil

Parent author assistance, checked here at the Gaussian projection interface. This strengthens §4 without assuming full cubic symmetry. Simultaneously diagonalize the symmetric slices and rotate Gaussian input by the same orthogonal basis. Then K is diagonal with entries q(a_j·x), for arbitrary row vectors a_j. B is diagonal with entries r_j²=|a_j|²; W has entries w(r_j²). Although the primitive coordinates may be dependent, the comparison below uses independent target exponentials from the SAME independent Gaussian coordinates x_j.

For r_j>0 put v_j=a_j/r_j and c_j=(v_j)_j. Expand q(r_j Z)=sum_(d>=0) b_jd H_d(Z) in normalized one-dimensional Gaussian Hermite polynomials. A column of K of degree d is b_jd H_d(v_j·x)e_j. Its Gaussian divergence lies in chaos d+1. The creation-operator identity gives its squared norm b_jd²(1+d c_j²): the longitudinal creation has norm sqrt(d+1), while an orthogonal creation has norm1, and their outputs are orthogonal. Since the Ornstein–Uhlenbeck inverse on chaos d+1 is multiplication by 1/(d+1), the squared norm of the gradient projection is b_jd²(1+d c_j²)/(d+1). Orthogonality of chaos degrees therefore yields EXACTLY

 epsilon_j²=(1-c_j²) sum_(d>=1) [d/(d+1)] b_jd².       (8)

The constant field d=0 is an exact gradient, as required. Gaussian integration by parts gives b_j1=r_j E q'(r_j Z). Since q''>=0 and q'(0)=2/pi, the positive half-line alone gives E q'(r_j Z)>=1/pi. Consequently

 r_j²(1-c_j²)<=2pi² epsilon_j².                       (9)

For 1/2<=r_j<=3/2 choose sigma_j=sign((a_j)_j), with either sign if it vanishes. The comparison exponential coordinate is Z_j=sigma_j[t(sigma_j x_j)-1]. Its gradient is e_j q(sigma_j x_j). Projection contraction, scalar q Lipschitz, and Gaussian Poincare imply

 E|h_j-Z_j|² <= E|q(a_j·x)-q(sigma_j x_j)|²
             <=|a_j-sigma_j e_j|²
              =(r_j-1)²+2r_j(1-|c_j|)
             <=(r_j-1)²+2r_j(1-c_j²).

On this interval (9) bounds the last term by 8pi² epsilon_j². The bounded smooth weight sqrt(w(r_j²)), equal to1 at r_j=1, changes the comparison cost by at most a constant times (r_j-1)². The explicit omega bounds that squared radial deviation on this compact interval. Hence the weighted coordinate cost is at most an absolute constant times omega(r_j²)+epsilon_j².

If r_j lies outside [1/2,3/2], including r_j=0, projection contraction and Poincare instead give E|sqrt(w(r_j²))h_j|²<=w(r_j²)E q(r_j Z)²<=2w(r_j²)(q(0)²+r_j²), uniformly bounded. Any chosen sign of Z_j has variance1, so its coupling cost is bounded absolutely and charged to the positive lower bound of omega(r_j²) on this range. Sum all coordinate costs. The Z_j are independent centered exponentials up to coordinate signs, despite possible dependence between the h_j. This proves (WR) for ALL commuting symmetric-slice pencils, with no restriction on dimension, slice magnitudes, or cubic symmetry.

This removes nonsymmetric commuting pencils as an obstruction to (WR). Noncommuting pencils remain unresolved. The calculation is collaborative author support, not a full-target claim or independent gate.
