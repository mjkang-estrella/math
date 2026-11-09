# Unconditional scores through the coarse normal slice

Author derivation, not independent review. This supports the unchanged two-variable strict-gap target; it does not prove the target. In particular matching microstates upper-volume constants have not been established.

## 1. The coarse decomposition

Write N=M_k(A), with normalized trace tr_k tensor tau. The coarse bimodule is N tensor N, with left multiplication on its first factor and right multiplication on its second. All Hilbert norms below use normalized traces. Put

 w_bc = sum_i E_ib tensor E_ci.

For every scalar matrix H, H w_bc=w_bc H. Conversely these k² vectors span the scalar-matrix-central subspace of M_k tensor M_k. For the normal pairs V_a from normal-slice-construction.md, put W_a,bc=(V_a1 w_bc,V_a2 w_bc). Direct matrix-unit multiplication gives

 <W_a,bc,W_e,fg> = delta_ae delta_bf delta_cg / k.

Let J eta=([D_1,eta],[D_2,eta]). Then J*W_a,bc=0, because sum_s[D_s,V_as]=0. The kernel of J is the scalar-matrix-central subspace: the pair D_1,D_2 generates M_k. Consequently rank J=k⁴−k², while the W span has dimension k²(k²+1). These dimensions add to 2k⁴. Thus J on its kernel complement and the W span give an orthogonal direct sum of the entire coarse pair space. Tensoring this finite coefficient identity with A tensor A preserves the identity.

This is a coarse-bimodule statement, not an inference just from ordinary tangent dimensions.

## 2. Perturbative exact derivations

Let U=(U_a) and T=(T_b) be bounded self-adjoint tuples, with U free from T. Assume U has finite conjugate system xi_a, which is then also a conjugate system relative to T. Choose an orthonormal basis O_b of the ordinary orbit tangent and set

 Z_s = D_s + epsilon (sum_a V_as U_a + sum_b O_bs T_b).

On polynomials in M_k,U,T define normal derivations Delta_a,bc by vanishing on M_k and T and by Delta_a,bc(U_e)=delta_ae w_bc. They are well defined as free-polynomial derivations; the conjugate-system identities supply their adjoints and passage to the represented algebra. Their adjoints on 1 tensor 1 are E_cb xi_a/k. Indeed on E_ij p the two trace contractions give delta_ib delta_jc/k² times the entry difference quotient. This also fixes the normalization.

Coefficient placement is important. For an entry coefficient a tensor b, replace the value w_bc on a generator by sum_i (E_ib tensor a) tensor (E_ci tensor b), in the evident identification of matrix and entry factors. On a word P U_e Q its contribution is P [delta(U_e)] Q: a sits on the RIGHT of the first-leg prefix, and b on the LEFT of the second-leg suffix. Equivalently this is the inner-leg action on a difference quotient, which commutes with both outer bimodule actions. Multiplying a derivative by arbitrary coefficients on the outer legs would not preserve the derivation rule and is not used. Extend from generator values by Leibniz, vanishing on the matrix units and on T. The central-intertwiner relation for w_bc ensures compatibility with the matrix-unit commutation relations.

A general derivation used here is a sum of these coefficient-inserted normal derivations and an inner derivation P -> [P,eta]. At epsilon=0 the map from (epsilon times the normal coefficients, eta) to the two values on Z is exactly the invertible direct-sum map in Section 1. Restrict eta to the fixed finite coefficient kernel complement. At positive epsilon its only additional term is epsilon times commutation with the bounded perturbation of D.

This can be inverted by a Neumann series. For precision, use the projective tensor norm on A tensor A, sum norm on the finitely many matrix coefficients, and the induced norms on the two fixed finite coefficient subspaces. Let K be the norm of the inverse at zero and let H_R bound the commutator perturbation when all U,T norms are at most R. If epsilon K H_R <=1/2, the inverse exists, has norm at most 2K, and differs from the inverse at zero by at most 2 epsilon K² H_R. These constants depend on k,R and the chosen finite bases, never on a matrix approximation size.

The series consists of words in U,T on its two legs. Differentiating with respect to a U variable inserts a w_bc in each occurrence. The l-th summand has at most l insertions; its differentiated norm is bounded by a fixed coefficient constant times l epsilon (epsilon K H_R)^(l−1). Summing proves that the difference from the constant inverse has derivative norm O_(k,R)(epsilon). This is the needed adjoint-domain control, not just convergence in operator norm.

Apply this inverse to the desired value (delta_js 1 tensor 1)_s. It yields a derivation delta_j with delta_j(Z_s)=delta_js 1 tensor 1. Therefore its adjoint at 1 tensor 1, projected onto L²(W*(Z)), is a conjugate variable of the unconditional pair Z.

For a coefficient u tensor v multiplying an entry derivative, its adjoint is obtained by the Leibniz identity: the leading term is multiplication of xi by u,v, and the two correction terms contract the derivatives of u,v against the trace. Hence its L² norm is bounded by the projective coefficient norm times ||xi||_2 plus the two differentiated coefficient norms. The adjoint of an inner derivation at 1 tensor 1 is the difference of the two partial traces of eta (with the appropriate adjoints under the Hilbert pairing); its L² norm is at most twice the projective norm of eta. These identities applied termwise to the absolutely convergent series justify the preceding projection, including integrability.

## 3. Sharp leading normal coefficient

The projection of the value (delta_js 1 tensor 1)_s onto the normal subspace is

 (1/k) sum_a,b,c (V_aj)_cb W_a,bc.

The adjoint formula from Section 2 therefore gives the leading score

 Xi_j^0 = (1/(epsilon k²)) sum_a V_aj tensor xi_a.

Orthonormality of the V pairs gives exactly

 sum_j ||Xi_j^0||_2² = Phi*(U)/(epsilon² k⁴).

The coefficient and differentiated-coefficient estimates above show that the full unprojected scores satisfy

 (sum_j ||Xi_j−Xi_j^0||_2²)^(1/2)
 <= C_(k,R) (1+sqrt(Phi*(U))).

Projection decreases the norm. Consequently, for 0<epsilon<=epsilon_(k,R),

 Phi*(Z) <= Phi*(U)/(epsilon² k⁴)
             + C_(k,R) epsilon^−1 (1+Phi*(U)).

Increasing C absorbs the bounded square-remainder term. The inner part is essential: the leading normal scores alone fail the linear test against Z_s by the missing orbit projection. This bound accounts for that part without conditioning on fixed scalar matrix units.

## 4. Exact noisy source, not upper semicontinuity

For the original encoding Z(epsilon)=D+epsilon sum V_a X_a, free scalar standard semicircular noise in the pair can be represented by 2k² free standard semicircular coefficient variables divided by k. Orthogonally rotate these coefficients into normal variables S_a and orbital variables R_b. At t=epsilon²k²u the noisy pair is exactly

 D+epsilon sum_a V_a (X_a+sqrt(u)S_a)
   +epsilon sum_b O_b sqrt(u)R_b.

Here U(u)=X+sqrt(u)S is free from T(u)=sqrt(u)R. This corrects an overly pessimistic statement in the earlier normal-slice note: for THIS linear encoding, a gauge correction need not retain a separate hidden X. The displayed expression already depends only on U(u),T(u), and the score construction above requires no gauge correction or Fisher upper semicontinuity.

For each fixed U_max<infinity, all coefficient operator norms are uniformly bounded for 0<=u<=U_max. The source tuple used here is already Gaussian smoothed, so Phi*(X)<infinity; projecting its conjugate system after adding free noise gives Phi*(U(u))<=Phi*(X). The preceding estimate is uniform on that interval. Integrating the Fisher bound under t=epsilon²k²u gives

 limsup_(epsilon->0) [chi*(Z(epsilon)+epsilon k sqrt(U_max) S_pair)
                       −chi*(Z(epsilon))]
 <= k^−2 [chi*(X+sqrt(U_max)S_normal)−chi*(X)].

The error before taking the limit is at most C_(k,R,U_max) epsilon (1+Phi*(X)). This uses the standard free heat-flow entropy identity; finite chi and bounded covariance ensure finite chi* for the original pair by the already established finite-entropy-chart argument and chi<=chi*. The heat-flow variables are not independent copies on the two sides; the formula refers to their indicated laws.

## 5. What remains unpaid

This is a one-sided NONMICROSTATES entropy-increment estimate. To obtain a strict gap from the large source tuple, one still needs a matching MICROSTATES entropy-increment lower bound, or matching finite-part upper/lower chart formulas, with the original limsup matrix-size definition. The finite-entropy-chart proof supplies only a coarse lower-volume constant; it does not identify the constant needed to cancel the orbit contribution.

In particular one must control all relevant microstates near the base pair, unequal spectral-band ranks, the global quotient-orbit volume, chart multiplicity, and the original limsup through compression sizes. Nothing here assumes these facts or replaces the frozen pair target by a relative/ultrafilter claim.

The old general warning remains true: closeness of generators alone does not provide upper Fisher continuity. It is bypassed here by an exact free normal/orbital decomposition and an explicit inverse derivation construction, not refuted as a general warning.
