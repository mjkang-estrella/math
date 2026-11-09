# First concrete interfaces (author calculations; no theorem claim)

## Source-paid quantitative input

For smooth strongly log-concave densities, source101 mat:entropy-smooth in its nonlinear affine normalization gives A=q^{-1}(DF), E A=0, L(x)=sum x_r X_r, Y=A-L, B=sum X_r^2, and

    ||Y||_(L2(gamma;F))^2 <= 1000 delta,
    sum omega(lambda_i(B)) <= 2000 delta.

Here q=phi/Phi(-.), and omega is exactly matrix.tex15–20. q is 1-Lipschitz in Frobenius norm (source rigidity lemma). Thus

    ||DF-q(L)||_2 <= sqrt(1000 delta).                 (1)

For sufficiently small absolute delta all eigenvalues of B lie in [1/2,3/2]: omega has a positive infimum off that interval. On the interval direct substitution in the displayed rational formula yields omega(lambda)>=(lambda-1)^2/200 (use denominator<=83/2, second factor>=3/20+(49/100)(74/83), minimum=13/100). Consequently

    ||B-I||_F^2 <= 400000 delta.                      (2)

This is dimension independent. It does not show closeness of the coefficients to an orthogonal cubic tensor.

To state the actual differential control without silently differentiating L2 errors, let K=q(L), J=DF and take any compactly supported smooth tensor Phi_{rij}. Gaussian integration by parts gives

  sum E[(partial_r K_ij-partial_j K_ir) Phi_rij]
  = sum E[(K-J)_ij (x_r-partial_r)Phi_rij
             -(K-J)_ir (x_j-partial_j)Phi_rij].        (3)

Hence its absolute value is bounded by sqrt(1000 delta) times the L2 Frobenius norm of the resulting adjoint-divergence matrix. This is a negative-order curl bound, not a pointwise bound on curl or its derivatives at zero.

At exact equality, the source Taylor expansion at x=0 gives X_r e_s=X_s e_r and [X_r,X_s]=0; classical associative symmetric-cubic-tensor algebra then gives orthogonal decomposition. Turning (3) into these identities with dimension-uniform error is unpaid. Evaluating an arbitrary L2 error at zero is invalid. Localizing to a fixed-radius Gaussian ball costs its dimension-dependent reciprocal mass. Standard fixed-dimensional compactness does not remove that cost.

Even if a dimension-uniform approximate tensor theorem is obtained, quantitative control of the source affine normalization P and passage to nonsmooth densities must be supplied. The exact source argument bounds P only after identifying a limiting covariance; this is not already a uniform rate.

## Conditional scalar route: an exact cancellation term

Let X have a log-concave joint density with nonsingular covariance. In coordinates, let v_i be the variance of the residual after optimal affine regression of X_i on X_1,...,X_{i-1}; then det Cov(X)=product v_i. Conditional densities are log-concave a.e. Put s_i^2=Var(X_i|X_<i) and delta_i=h(X_i|X_<i=x)-1-(1/2)log s_i^2. In the integrable case, the chain rule gives exactly

  delta(X)=sum_i E delta_i + (1/2)sum_i(E log s_i^2-log v_i).  (4)

Moreover E s_i^2<=v_i by the least-squares projection property; Jensen makes every correction nonpositive. Thus scalar stability cannot simply be summed to bound joint distance using delta(X).

This correction genuinely occurs for a log-concave density. For uniform density 2 on the triangle {x>=0,y>=0,x+y<=1}, Var(X)=Var(Y)=1/18, Cov(X,Y)=-1/36, so v_2=1/24. Conditional Y|X=x is uniform on [0,1-x], with s_2^2=(1-x)^2/12. Since X has density2(1-x), E log(1-X)=-1/2. Therefore

    E log s_2^2-log v_2=log 2-1<0.

This is an obstruction to an unsigned conditional-gap aggregation, not a counterexample to the proposed full stability statement. It identifies a dependence/conditional-scale term that any triangular-transport proof must recover with its correct sign.
