# Finite microstates entropy in the two-matrix slice

Author supporting proof for the full frozen target. It supplies finiteness of both entropies for an explicit pair encoding, not their strict separation. All constants may depend on the fixed integer k; none depend on the matrix approximation size d.

Use D,B,V from normal-slice-construction.md, n=k²+1, and bounded self-adjoint X with chi(X)>-infinity. Fix a finite cutoff R with chi_R(X)>-infinity. Choose an orthonormal basis V_a of the normal slice for normalized tr_k. The pair to be encoded is

 Z_r=D_r tensor1+epsilon sum_(a=1)^n V_ar tensor X_a.

For all sufficiently small fixed epsilon>0, depending on k,R, this pair has chi(Z)>-infinity. In particular both chi(Z) and chi-star(Z) are finite, by the source-stated comparison and the finite covariance upper bound.

## Uniform linear decomposition

Let H_d be the real Hermitian kd-by-kd space. Let K_d be the orthogonal complement of I_k tensor M_d^sa in H_d. The derivative at zero of

 Phi_d(K,Y)=exp(iK)(D_pair tensor1+Y)exp(-iK)

is

 L_d(K,Y)=i[K,D_pair tensor1]+Y,

where Y lies in V tensor_R M_d^sa. The two displayed summands are orthogonal, and the first has kernel zero on K_d. Hence L_d is an isomorphism from a real space of dimension

 (k²−1)d²+(k²+1)d²=2k²d²

to the pair space. Its least Hilbert-Schmidt singular value s_k>0 is independent of d: in orthonormal Hermitian coefficient bases it is the fixed finite k linear map tensored with the identity on M_d^sa.

There is also an operator-norm inverse bound independent of d. Expand each block matrix in a fixed real Hermitian basis of Mk. Each coefficient is obtained by a finite sum of block extractions with fixed coefficients, hence has norm at most C_k times the input operator norm. Apply the fixed inverse coefficient matrix of L_1 and reconstruct. This bounds L_d^-1 from max pair operator norm to max(||K||op,||Y1||op,||Y2||op) by C_k. This is a finite coefficient calculation, not an assertion that Hilbert-Schmidt inversion controls operator norm dimension freely.

## Uniform nonlinear chart and volume Jacobian

On the convex domain ||K||op<r, max_r||Y_r||op<r, the exponential conjugation formula and its derivative satisfy

 ||D Phi_d-L_d|| <= C'_k r

both for the preceding operator norms and for Hilbert-Schmidt norms. To see this, use exp(iK)-I=integral_0^1 iK exp(itK)dt and the derivative formula D exp(iK)[H]=integral_0^1 exp(i(1-t)K)iH exp(itK)dt. Multiplication by a matrix of operator norm a has Hilbert-Schmidt norm at most a times the input norm; conjugations are isometries. The derivative in Y differs from the identity by O(r), and the derivative in K differs from commutation with the base pair by O(r)(1+||D||+||B||). These bounds depend on k, not d.

Choose r>0 so that both ||L_d^-1(D Phi_d-L_d)|| in the operator-norm domain and ||D Phi_d-L_d||HS/s_k are below1/2. The first gives injectivity on this convex domain: integrate the derivative along the segment between two inputs to obtain

 ||L_d^-1(Phi_d(x)-Phi_d(y))-(x-y)|| <=(1/2)||x-y||.

The second bounds every singular value of D Phi_d below s_k/2. Its real volume Jacobian is therefore at least(s_k/2)^(2k²d²). This remains valid at nonzero Y; it is not just a tangent dimension count.

Choose epsilon so small that epsilon R sum_a max_r||V_ar||op<r/2. The map x=(x_a)->epsilon sum V_a tensor x_a then places every cutoff-R microstate tuple in the allowed Y domain. For unnormalized Hilbert-Schmidt volume its linear Jacobian is epsilon^(n d²) k^(n d²/2), because the V_a basis is orthonormal for normalized tr_k. All k factors may be absorbed into a constant exp(C_k d²).

## Enough volume in the orbit-parameter domain

Let H_b,1<=b<=k²−1, be an orthonormal basis of traceless Hermitian Mk for normalized tr_k. Write K=sum_b H_b tensor K_b. Take independent standard GUE(d) coefficient matrices G_b, scaled by a sufficiently small fixed rho_k>0. The standard GUE operator-norm tail used in source298 implies that with probability at least1/2 for every sufficiently large d, all ||G_b||op<=3, hence ||sum_b H_b tensor rho_k G_b||op<r/2. Here the number k²−1 is fixed before d tends to infinity.

The joint coefficient density is bounded by(d/(2pi rho_k²))^((k²−1)d²/2). Therefore the Lebesgue volume in K_d of its operator-norm ball of radius r/2 is at least

 exp(-C_k d²) d^(-(k²−1)d²/2).

The fixed coefficient-to-K Hilbert-Schmidt Jacobian only changes C_k. This step uses operator-norm bounded Gaussian matrices; an ordinary Hilbert-Schmidt ball with radius proportional to sqrt(d) would not justify the same operator-norm restriction.

## Original-limsup microstate lower bound

Take increasingly accurate cutoff-R microstate sets Gamma_d for X along dimensions with

 log Vol(Gamma_d)>=d²[chi_R(X)-o(1)]-(n/2)d² log d.

Such a subsequence exists by the original limsup definition, exactly as in source298's selected-ensemble construction. For every K in the above orbit-parameter ball and every x in Gamma_d, Phi_d(K,epsilon Vx) has the same normalized trace moments as D_pair tensor1+epsilon Vx, because the conjugating unitary cancels in every word. These moments converge uniformly to those of Z; the norm cutoff is also uniform. Thus the whole chart image lies in each prescribed cutoff microstate neighborhood of Z for all sufficiently large selected d.

Injectivity and the volume Jacobian bound give

 log Vol(image)>=d² chi_R(X)+n d² log epsilon
                 -k²d² log d-C_k d²-o(d²).

Output matrix size is kd and there are exactly two variables. Its entropy normalization adds log(kd) after dividing by(kd)². The log d terms cancel, leaving

 chi(Z)>=k^-2 chi_R(X)+(n/k²)log epsilon-C'_k>-infinity.

No all-size limit or ultrafilter equality is substituted. The subsequence kd is sufficient for a lower bound on the original limsup. Every encoded moment neighborhood is eventually covered, so the infimum over those neighborhoods preserves the lower bound.

The source comparison chi<=chi-star gives a finite lower bound for chi-star(Z). Its finite upper bound follows from the standard covariance/semicircular maximum bound; equivalently integrate the conjugate-variable Cauchy-Schwarz lower bound on Fisher information along free Gaussian noise. Boundedness of Z makes that bound finite. Thus the full target's two finiteness requirements are achieved by the chart. No positive entropy difference has been proved. In particular this support result is not a replacement or separate nominee for the frozen strict-gap target.
