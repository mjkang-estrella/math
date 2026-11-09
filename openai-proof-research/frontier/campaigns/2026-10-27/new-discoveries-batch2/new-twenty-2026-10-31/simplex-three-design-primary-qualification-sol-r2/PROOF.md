# Independent second qualification: MathDB 362896

All mathematics below was checked personally, without enumeration, numerical experiments, CAS, Lean or children. The inherited mechanism was disclosed; this is verification, not independent invention. Credit 0.

## Exact scope and equal-weight audit
For every integer d>=3 there do not exist d real vectors p_r with sum_i p_ri=1 such that d^-1 sum_r f(p_r) equals the normalized flat simplex integral for every polynomial f of total degree <=3. In particular there is no d-point simplex 3-design in Delta_d. Repetitions do not help. The pseudoprobability extension is not a second outcome.

I read every step of inputs/review-r1-PROOF.md before opening FULLCANDIDATE.md. Its beta-integral normalization, central second moment, sum-of-squares Gram reconstruction, cubic tensor contractions, three index patterns and cancellation are correct. No ordinary gap found. This file includes that complete audited proof below, verbatim as supplied, followed by an independently checked stronger free-weight obstruction.

# Independent ordinary reconstruction, before author proposal read
Target: d >= 3, d equally weighted points in Delta_d={x in R^d: x_i>=0, sum x_i=1}; flat probability measure. No computation/CAS used. Mechanism disclosed in task; independent verification, not independent invention.

For nonnegative integer exponents alpha, k=sum alpha, the normalized flat moment is
E prod X_i^alpha_i = (d-1)! prod alpha_i!/(d+k-1)!.
Indeed in coordinates x_1,...,x_{d-1}, x_d=1-sum x_i, iterated beta integration gives prod alpha_i!/(d+k-1)!; the coordinate volume is 1/(d-1)!, so normalization multiplies by (d-1)!. Intrinsic Euclidean surface measure has constant Jacobian sqrt(d), which cancels on normalizing. The beta formula for integers follows by integration by parts starting from integral_0^1 t^a dt=1/(a+1). This pays actual flat probability, not unnormalized ambient d-dimensional measure (which is zero).

Write u=(1/d,...,1/d), H=I-J/d, a=1/(d+1), and y_r=p_r-u, r=1,...,d. Degree <=3 matching implies sum_r y_r=0 and (1/d)sum_r y_r y_r^t=H/[d(d+1)]. The raw moments used here are EX_i=1/d, EX_i^2=2/[d(d+1)], EX_iX_j=1/[d(d+1)] for i!=j. Central moments are polynomials of degree <=3, so they too must match. Let Y have columns y_r and G_rs=<y_r,y_s>. Thus YY^t=aH, G1=0, tr G=a(d-1).

No rank or unstated independence argument is needed: sum_rs G_rs^2 = sum_rs sum_ij y_ir y_is y_jr y_js = sum_ij (sum_r y_ir y_jr)(sum_s y_is y_js) = sum_ij (aH_ij)^2 = a^2(d-1). All sums are finite, so distributivity and reordering suffice. Here H^2=H, tr H=d-1. On the node indices H_rs=delta_rs-1/d, and sum_rs G_rs H_rs=tr G-(1/d)sum_rs G_rs=tr G. Consequently
sum_rs (G_rs-aH_rs)^2=a^2(d-1)-2a^2(d-1)+a^2(d-1)=0.
Every real square vanishes. Thus G=aH, including diagonal a(d-1)/d and off-diagonal -a/d. Repeated points cannot occur for d>=2 because their squared distance would instead be 2a>0.

For arbitrary vectors z_r, expand the squared Frobenius norm of sum_r z_r^{tensor3}: sum_ijk sum_rs z_ir z_jr z_kr z_is z_js z_ks = sum_rs (sum_i z_ir z_is)^3. This is again a finite interchange. Therefore the empirical central tensor T_emp=(1/d)sum_r y_r^{tensor3} satisfies
(A) ||T_emp||^2 = d^-2 [d(a(d-1)/d)^3+d(d-1)(-a/d)^3] = (d-1)(d-2)/[d^3(d+1)^3].
The simplification uses (d-1)^3-(d-1)=d(d-1)(d-2).

For v_l=e_l-u put S=sum_l v_l^{tensor3}. For three equal indices S_iii=((d-1)^3-(d-1))/d^3=(d-1)(d-2)/d^2. For i=i!=k, S_iik=[-(d-1)^2+(d-1)-(d-2)]/d^3=-(d-2)/d^2. For three distinct indices, S_ijk=[3(d-1)-(d-3)]/d^3=2/d^2.
Raw cubic moments are 6/D,2/D,1/D in these same three patterns, D=d(d+1)(d+2). Expansion of (X_i-1/d)(X_j-1/d)(X_k-1/d) subtracts (EX_iX_j+EX_iX_k+EX_jX_k)/d and adds 2/d^3. Hence T_cont entries are respectively 2(d-1)(d-2)/[d^3(d+1)(d+2)], -2(d-2)/[d^3(d+1)(d+2)], 4/[d^3(d+1)(d+2)]. Thus T_cont=2S/[d(d+1)(d+2)]. Inner products <v_l,v_m>=delta_lm-1/d give ||S||^2=(d-1)(d-2)/d by the same cube identity. Therefore
(B) ||T_cont||^2=4(d-1)(d-2)/[d^3(d+1)^2(d+2)^2].

Matching all cubic moments implies equality of tensors and hence equality of squared norms. The converse is NOT asserted or needed. For d>=3 cancellation is valid, giving (d+2)^2=4(d+1), i.e. d^2=0, contradiction. Positivity was never used after prescribing the moments; impossibility holds even for arbitrary real nodes with these moment equations (indeed covariance/mean already enforce the affine hyperplane). This does not concern arbitrary unequal weights.

Boundaries: d=1 is a trivial design. For d=2 the factor (d-2) vanishes and no cancellation is legal; two symmetric interval Gauss nodes (1/2 +/- 1/(2sqrt(3)), complementary coordinate) give an equal-weight degree-three rule. For d=3 (A)=1/864 and (B)=1/1350, unequal. For d=4 their ratio is (d+2)^2/[4(d+1)]=9/5. More generally the ratio is 1+d^2/[4(d+1)]>1 for d>2. These are hand arithmetic checks, not numerical experiments.


## Free weights: the classical Gaussian obstruction, paid in full

Let H={a in R^d: sum a_i=0}, u=1/d, Y=X-u, P=I-J/d. Work on the d-dimensional real space V of affine functions on the affine hyperplane sum x_i=1, written f=s+b.Y with b in H. From the same normalized beta moments,
 E(a.Y)(b.Y)=kappa (a.b), kappa=1/[d(d+1)],
 E(a.Y)(b.Y)(c.Y)=2 sum_i a_i b_i c_i/[d(d+1)(d+2)].
Write lambda=2/(d+2) and a*b=P(a componentwise-multiplied by b).
The orthogonal projection of (a.Y)(b.Y) to V is
 kappa(a.b)+lambda(a*b).Y.
This follows by pairing with 1 and with each c.Y; the displayed second and third moments pay both components, and the positive definite affine inner product gives uniqueness.

Define M_a:V->V by compressed multiplication, M_a f=projection_V[(a.Y)f]. Then
 M_a(1)=a.Y,
 M_a(b.Y)=kappa(a.b)+lambda(a*b).Y.
These are precisely the degree-one truncations of the classical multiplication/Jacobi operators underlying the Gaussian common-zero criterion.

Suppose, now, a formula with d nodes z_r in the affine hyperplane and arbitrary real weights w_r is exact through degree three. No positivity premise is needed for this stronger statement. Its evaluation map E:V->R^d is injective: if f vanishes at all nodes, exactness of f^2 gives integral f^2=0, so f=0. Since dim V=d, E is bijective. In particular there are affine Lagrange functions ell_r, with ell_r(z_s)=delta_rs. Exactness gives
 w_r=integral ell_r^2>0.
Thus even signed weights are automatically positive in this minimal regime, and zero weights/repeated nodes are impossible. Fewer than d nodes would already contradict injectivity.

For a in H and f,g in V, exactness through degree three gives
 integral (M_a f)g=integral(a.Y)fg=sum_r w_r(a.(z_r-u))f(z_r)g(z_r).
Exactness through degree two gives the left side also as sum_r w_r(M_a f)(z_r)g(z_r). Taking g=ell_r and using w_r>0 proves
 E M_a = D_a E,
where D_a is diagonal with r-th entry a.(z_r-u). Hence all M_a must commute. This proves from scratch the necessity used from Gaussian cubature, not merely a title-based assertion of standardness.

They do not commute. On 1 their commutator vanishes. On c.Y, direct substitution of the two displayed formulas gives zero constant part (symmetry of sum_i a_i b_i c_i) and linear part
 [M_a,M_b](c.Y) = (kappa-lambda^2/d) [(b.c)a-(a.c)b].Y
 = d/[(d+1)(d+2)^2] [(b.c)a-(a.c)b].Y.
For completeness, the only cancellation here is
 a*(b*c)-b*(a*c)=-[(b.c)a-(a.c)b]/d:
expand P(b componentwise c)=b componentwise c-(b.c)1/d, then apply P once more. The common triple-product term cancels, and P fixes a,b. Also kappa-lambda^2/d=((d+2)^2-4(d+1))/[d(d+1)(d+2)^2]=d/[(d+1)(d+2)^2]>0.

For d>=3, dim H>=2. Choose nonzero orthogonal a,b in H and c=b. Then the commutator is the nonzero affine function
 d ||b||^2 (a.Y)/[(d+1)(d+2)^2],
a contradiction. Existence of the orthogonal pair requires only elementary inner-product linear algebra; for an explicit pair take a=(1,-1,0,...), b=(1,1,-2,0,...). Thus no free-weight d-node degree-three formula exists for any d>=3, even with nodes outside the simplex in its affine hull. For d=2 the affine linear part is one-dimensional and the two Gauss interval nodes with equal weights do exist; no erroneous universal nonexistence is asserted.

## Complete primary-criterion bridge and significance
The actual retrieved Fialkow-Petrovic manuscript, A moment matrix approach to multivariable cubature, dated December16,2003, pp1-2, defines positive cubature with arbitrary nodes in R^n, gives N>=dim P_floor(m/2), and states Mysovskikh's Gaussian criterion in Theorem1.2: for square-positive measures with finite moments of all orders, degree2r+1 Gaussian rules exist iff the degree r+1 orthogonal polynomials have binomial(n+r,n) common zeros. Its general criterion, rather than a directly printed all-simplex theorem, is the authenticated classical prior used here.
Use n=d-1, r=1, m=3. Eliminate x_d=1-sum_{i<d}x_i to identify the simplex with a full-dimensional compact region in R^n. Normalized Lebesgue measure is positive Borel, has all moments, and is square positive because a nonzero polynomial cannot vanish on its open interior. dim P_1=n+1=d. Our assumed equal-weight design is therefore a Gaussian rule in exactly that theorem's minimal regime. The projected quadratic residuals above are orthogonal to P_1. The computed noncommutation, and the fully proved diagonalization necessity, exclude the Gaussian rule without any support or weight loophole. The fixed moment calculation works uniformly in d. This supplies a complete classical-criterion-to-literal routine reduction, not a claim that the source printed this exact conjecture or that short proofs are automatically routine.

The full free-weight case follows quickly: just project quadratic products onto affine functions and check their commutator. Equal weights do no work for the obstruction. On campaign standards I recommend EXCLUDE AS ROUTINE OR KNOWN, specifically the ROUTINE branch. Exact historical attribution of the stronger simplex theorem remains unqualified; a 1973 Flatto-Haber primary abstract is a concrete older direct claim but its actual proof was not retrieved. Fritsch and the fingerprint-only Xu work remain closed and unread. Neither is silently credited as the proof of this conclusion.
