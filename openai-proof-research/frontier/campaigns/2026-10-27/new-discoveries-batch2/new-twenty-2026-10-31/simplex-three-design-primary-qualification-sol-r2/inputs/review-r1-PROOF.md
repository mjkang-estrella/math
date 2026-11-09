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
