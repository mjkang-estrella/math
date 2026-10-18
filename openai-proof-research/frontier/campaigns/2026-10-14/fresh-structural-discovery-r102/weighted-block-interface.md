# General conditional block adjoint bound

Active author assistance for the unchanged all-deficit target. This is a precise consequence of the negative-curl interface, not a new full stability theorem. It generalizes the star test but does not supply the needed coercivity in the tensor coefficients.

## Output indices must be kept fixed

Write a vector-map Jacobian as J_{j i}=partial_i F_j: the first index is the output coordinate. It satisfies partial_a J_{j i}=partial_i J_{j a}, without any symmetry premise. For the unweighted symmetric pencil K=q(L), the earlier star notation K_ij=K_ji gives the same test. After left weighting K by S^{1/2}, the matrix is not generally symmetric; one must not exchange its indices.

Let S be any fixed positive definite matrix. Assume

 epsilon_S²=E||S^{1/2}(K-J)||F²<infinity.

Split Gaussian input coordinates orthogonally as x=(u,v), with u in a selected bad subspace of dimension k and v in its complement of dimension d. Rotate both input and output coordinates if S is diagonalized in this split; the estimate below itself does not require S to preserve the input split.

For every output j, good input i, and bad input a, define the distribution on u

 D_{a j i}(u)=partial_a E_v K_{j i}(u,v)-E_v[v_i K_{j a}(u,v)].

For J this conditional defect vanishes. This follows by distributional commuting derivatives followed by Gaussian integration by parts in v_i. Test first with compact u support and Gaussian radial cutoffs in v, then pass by L2 integrability.

For a smooth test tensor h_{a j i}(u), integration by parts pairs D with a matrix field A having disjoint input-column blocks:

 A_{j i}=sum_a (u_a-partial_a) h_{a j i},
 A_{j a}=-sum_i v_i h_{a j i}.

Therefore

 |<D,h>|² <=epsilon_S² E||S^{-1/2} A||F²
 <=epsilon_S² (2||S^{-1/2}h||²+||S^{-1/2}gradient_u h||²).       (WB)

S^{-1/2} acts only on output index j. To prove the last bound, use independence and E[v_i v_l]=delta_il for the bad-column block. For the good-column block, the Gaussian divergence identity is

 ||sum_a delta_a h_a||²
 =sum_a||h_a||²+sum_ab <partial_b h_a,partial_a h_b>
 <=||h||²+||gradient h||².

The constant2 and the gradient coefficient1 are independent of k,d,S and B. No matrix functional-calculus derivative estimate is used.

Equivalently, in the normalized Hermite basis on u, writing D_alpha for the tensor coefficient, (WB) implies

 sum_alpha ||S^{1/2}D_alpha||F²/(2+|alpha|) <=epsilon_S².       (WH)

For finite Hermite sums this follows by choosing h_alpha=S D_alpha/(2+|alpha|); monotone limits give the distributional version. The Gaussian adjoint bound extends from compact tests to finite Hermite polynomials by Gaussian cutoffs. This is an H^{-1}-type bound, not an unweighted L2 bound on D.

## Application to the source and parent covariance observation

The parent's retained support-plane metric is S=(37I/40+3B/40)^{-1}, with ||S||op<=40/37. Its retained covariance logdet gap G controls the normalization coupling by cost<=G<=2delta (parent derivation; not independently rederived here). Since q is Frobenius1-Lipschitz,

 epsilon_S² <= ||S||op E||q(L)-q(A)||F²
 <=(40/37)||Y||² <=(40000/37)delta.

Thus(WH) holds at every deficit, with no Bop factor. On output eigenspaces where B<=b, S>=40/(37+3b), so the corresponding unweighted conditional defect has H^{-1} norm squared at most ((37+3b)/40)epsilon_S².

The star proof is a special case with one bad coordinate and h_{0 j i}=h(u)delta_ji on the good output block. Its order-d lower bound is exactly a lower bound for a component of this conditional defect.

## Exact missing step

No inequality bounding general mixed tensor energy by the left side of(WH) has been proved. The conditional average E_v q(L) can contain several noncommuting exceptional blocks, and its derivative can cancel E_v[v_i q(L)_{j a}]. There is no justified replacement by q(E_v L), nor by q(PLP). Full coefficient symmetry is itself not known in the all-deficit regime. Source H1 slack controls Y but does not directly control the conditional defect's tensor coercivity.

The output metric also does not automatically repair the strong derivative estimate: S^{1/2} does not commute with the unitary factors in the Fourier representation of D²q(L). The inequality S^{1/2} B S^{1/2}<=40/3 I cannot be moved through e^{itL}. Any such step needs an additional argument.

## First-chaos off-block coercivity, valid at every scale

There is a useful general estimate that does not require Bop, coefficient symmetry in all three indices, or any Jacobian premise. Put

 Z_r=E[x_r q(L)], X_r^off=P X_r Q+Q X_r P,
 Z_r^off=P Z_r Q+Q Z_r P,

for any orthogonal complementary projections P,Q on the matrix/output space. Then

 sum_r ||X_r^off||F² <= pi² sum_r ||Z_r^off||F².                (FC)

The corresponding inequality for just P X_r Q has the same constant, because both off-block matrices are symmetric and their two blocks have equal norm.

Proof. Let R(t)=(q(t)-q(-t))/2. The source q''>=0 and q'(0)=2/pi imply

 R'(t)=(q'(t)+q'(-t))/2 >=1/pi,

since one of t,-t is nonnegative. Hence all first divided differences R[a,b]>=1/pi. The spectral derivative formula along a line of real symmetric matrices gives

 tr((R(H)-R(H0))(H-H0)) >=(1/pi)||H-H0||F².

Repeated eigenvalues use the continuous derivative. Explicitly integrate tr(DR(H0+sD)[D]D), whose eigenbasis expression is sum_ij R[lambda_i,lambda_j]|D_ij|². This is Frobenius strong monotonicity, not an assertion of operator monotonicity.

Apply this pointwise to H=L(x), H0=PL(x)P+QL(x)Q. The matrix R(H0) is block diagonal, so its pairing with H-H0 vanishes. Integrate Gaussian x. Evenness of (q(t)+q(-t))/2 under x->-x gives E[x_r R(L)]=Z_r. Therefore

 sum_r tr(Z_r^off X_r^off) >=(1/pi)sum_r ||X_r^off||F².

Cauchy-Schwarz proves(FC). All functions have at most linear growth, so the integrals are finite.

This is genuine mixed-pencil mass control by a measurable part of q(L), but not by delta. A compatible Jacobian may itself have large off-block first chaos. Comparing q(L) with J bounds the discrepancy of their Z_r by ||Y||, but does not force the first-chaos off-block part of J to vanish. Its integrability only permutes its two input indices. Passing from(FC) to a deficit charge therefore still requires nonlinear compatibility, covariance/entropy structure, or an actual factor-recovery argument. It is not valid to replace Z_r by the curl residual alone in(FC).

## A precise obstruction to a naive weighted pointwise derivative bound

The preceding concern about unitary factors is not merely lack of a convenient estimate. For the star slices, take H=0, perturbation E=e0 e0*, and S=(37I/40+3B/40)^{-1}. For i=1,...,d,

 D²q(0)[E,X_i]=(q''(0)/2)(E X_i+X_i E)
               =(q''(0)/(2sqrt(2)))(e0 ei*+ei e0*).

Since S_ii=1 for all good indices i,

 sum_i ||S^{1/2}D²q(0)[E,X_i]||F² >= d q''(0)²/8,

whereas ||E||F=1 and ||S^{1/2} B S^{1/2}||op<=40/3. Here q''(0)=q(0)(4/pi-1)>0. Thus replacing Bop by ||S^{1/2}BS^{1/2}||op in the pointwise column estimate is false.

This does not refute a Gaussian-integrated estimate using H=L(x), nor an estimate using both ||Y||² and ||gradient Y||²: a remainder localized near x=0 can incur gradient cost. It only closes the direct pointwise left-weight substitution. No actual entropy counterexample follows.

The generic Gaussian-integrated H1 replacement also fails if it discards Omega(B) and the actual Jacobian premise. In dimension3 let

 L=diag(M x0,x1,x2), B=diag(M²,1,1),
 E(x)=(x2²-1)(e0 e1*+e1 e0*).

E has zero zeroth/first chaos and ||E||²+||gradient E||²=12, independent of M. Let X0=M e0e0*. The good-output (1,0) entry of S^{1/2}D²q(L)[E,X0] is exactly

 M q[x1,M x0,M x0](x2²-1).

On |x0|<=1/M and |x1|<=1, the second divided difference has an absolute positive lower bound, because q'' is strictly positive on[-1,1]. Independence and E(x2²-1)²=2 show that the squared Gaussian norm is at least c M for M>=1. The probability of |x0|<=1/M is at least c'/M, giving the stated rate. No asymptotic derivative exchange is involved.

This only refutes a generic estimate by the H1 norm of E alone. Here Omega(B)=omega(M²) is itself order M, and q(L+E) is not claimed to be a Jacobian. An estimate involving Omega(B), or exploiting that actual compatibility, is still possible. This auxiliary perturbation is not a source transport or log-concave counterexample.
