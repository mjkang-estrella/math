# Explicit good-pencil recovery conditional on Euclidean mixed energy

Author deduction for the unchanged all-deficit problem. This is a sufficient construction with an explicit unpaid input, not a claim that the source supplies that input. It avoids applying an entropy theorem to an averaged law whose log-concavity has not been proved.

Use the original source notation, J=DF a symmetric positive Jacobian, K=q(L), L=sum x_r X_r, B=sum X_r², epsilon²=E||J-K||F². Let Q be the bad spectral projection outside[1/2,2], P=I-Q. Rotate the common coordinates so x=(u,v), with u bad, v good. Set

 k=rank Q, d=rank P, kappa=E||P K Q||F².

The missing input in this construction is an O(delta) upper bound for kappa. The already proved inverse-good-block Schur estimate does not supply it.

## 1. Recover a pencil using only good inputs and outputs

Let A_r=P X_r P as a d-by-d matrix and L_P=sum_all x_r A_r. The first-chaos off-block coercivity proved in weighted-block-interface.md, followed by Bessel, gives

 a:=sum_r ||P X_r Q||F² <=pi² kappa.

With L_diag=PLP+QLQ, E||L-L_diag||F²=2a. Spectral Frobenius Lipschitzness of q therefore gives

 E||q(L_P)-P K P||F² <=2a.                            (1)

For every bad input index b and good indices i,j, Hessian compatibility gives the exact Gaussian first-chaos identity

 E[x_b J_ji]=E[x_i J_jb].                             (2)

One proof is the distributional commuting-derivative identity tested against Gaussian density, with cutoffs. The L2 Jacobian suffices for the cutoff limit. Applying Bessel in the good input i, then in the bad input b for the approximation errors, yields

 sum_bad b ||E[x_b q(L_P)]||F²
 <=2 E||P J Q||F²+2 E||q(L_P)-P J P||F²
 <=(4+8pi²)kappa+8epsilon².                         (3)

Here E||PJQ||²<=2kappa+2epsilon², and (1) gives E||q(L_P)-PJP||²<=4a+2epsilon². Constants are loose but absolute.

Now define the EXPLICIT reduced pencil

 L_g(v)=sum_good r v_r A_r.

The odd response R(t)=(q(t)-q(-t))/2 has derivative at least1/pi. Compare L_P and L_g in the Frobenius strong-monotonicity inequality and integrate. Since L_g is independent of u, E[x_b R(L_g)]=0 for bad b. Since the even response contributes no first chaos, the result is

 b:=sum_bad r ||A_r||F²
 <=pi² sum_bad r ||E[x_r q(L_P)]||F²
 <=pi²[(4+8pi²)kappa+8epsilon²].                     (4)

This is a bound on bad-input dependence, not an assumption of full symmetry of the coefficient tensor. Only the actual comparison Jacobian uses symmetry/integrability.

The reduced Gram matrix satisfies

 B_g=sum_good r A_r²<=PBP<=2I_d,
 H:=PBP-B_g=sum_all r P X_r Q X_r P+sum_bad r A_r²>=0,
 tr H=a+b, 0<=H<=2I_d, ||H||F²<=2(a+b).             (5)

On[1/2,2], the source omega dominates a positive constant times(lambda-1)². Hence

 ||B_g-I_d||F²<=C Omega(B)+4(a+b)
               <=C[Omega(B)+kappa+epsilon²].         (6)

No beta^4 term or hidden dimension factor occurs. This is a bounded-B, strong-Frobenius-residual reduction.

## 2. The actual averaging and its law

Center F, and put barF(v)=E_u[P F(u,v)] under the ORIGINAL product Gaussian input. This is a centered gradient of a convex potential in v, with weak Jacobian E_u[PJP]. We do not assert that its output law is log-concave.

Gaussian Poincare in u gives

 E|P F-barF|²<=E||PJQ||F²<=2kappa+2epsilon².           (7)

Combining J-K, (1), and (4), then conditional Jensen, gives

 E||D barF-q(L_g)||F²
 <=3epsilon²+6a+3b=:eta²
 <=C(kappa+epsilon²).                               (8)

Indeed q(L_P)-q(L_g) has L2 Frobenius norm squared at most b. All maps in(7)-(8) live on the correct Gaussian inputs; no partial Legendre pushforward is treated as Gaussian.

Let h_g be the centered Gaussian primitive obtained by orthogonal projection of the columns of q(L_g) onto gradients, as in the main author's weighted-primitive-reduction.md. Since D barF is such a column gradient, projection and Poincare imply

 E|barF-h_g|²<=eta²,
 dist(q(L_g),column gradients)²<=eta².               (9)

Thus the law that survives is an explicit d-dimensional pencil primitive, not an assumed log-concave law.

## 3. Output normalization remains controlled

Write W_P=(37I_d/40+3PBP/40)^(-1),
 W_g=(37I_d/40+3B_g/40)^(-1), Psi_g=W_g^(1/2) h_g.

On the fixed spectral interval[0,2], the scalar function f(t)=(37/40+3t/40)^(-1/2) is Lipschitz. Its divided-difference derivative therefore gives Frobenius matrix Lipschitzness. By(5),

 ||W_g^(1/2)-W_P^(1/2)||F²<=C||H||F²<=C(a+b).        (10)

Moreover Cov(h_g)<=C I_d. To check this matrix inequality, apply scalar Poincare and the gradient projection contraction to each constant output combination z·h_g:

 Var(z·h_g)<=E|q(L_g)z|²
 <=z^t[2q(0)² I_d+2B_g]z<=C|z|².

Thus multiplying h_g by the weight difference in(10) incurs expected squared cost at most C(a+b); no upper bound on Cov(barF) or inverse covariance is used.

Finally, use the parent retained-gap coupling W^(1/2)F= D^(1/2) OX, with X the original isotropic vector and O orthogonal, whose squared cost from OX is at most G. Project it to good output coordinates. Combine that projection with(7),(9),(10) in the SAME input coupling, using the squared triangle inequality a fixed number of times. This gives the actual sufficient transport estimate

 W2²(Law(P OX),Law(Psi_g)) <= C[G+kappa+epsilon²].    (11)

P OX is isotropic in its d-dimensional space. All C here are universal finite constants. If d=0, there is no good law and the elementary completion bound handles the entire space.

## Exact debt after this construction

For source coefficients G,epsilon²,Omega=O(delta), and k=O(delta). If one proves kappa=O(delta), (11) gives a good-dimensional primitive within O(delta) cost, with B_g<=2I, beta_g²=O(delta), and column-Jacobian residual O(delta). An exponential-factor rounding theorem for this primitive would then complete the original target after independent exponential completion of the k removed original output coordinates, at cost2k.

Two assertions remain unpaid: the kappa bound itself, and uniform rounding for this bounded-B primitive when its TOTAL residual is not absolutely small. The new GR correction applies to a fully symmetric cubic with small absolute residual; it cannot be invoked merely because residual/d is small. No recursive entropy argument is available for Law(barF) without proving log-concavity. This conditional construction is not claimed as the full all-deficit proof.
