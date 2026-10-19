# CP unitalization interface for the unchanged global tensor target

Parent author analysis, not an independent gate or a nominee. The exact T101G69 scope remains in `fresh-arithmetic-discovery-r69/scope.md`. The channel/Gram reformulation is credited to that packet's existing channel-density and simplex analysis; rewriting it here earns no new-result credit.

Let T be a fully symmetric real cubic on R^m, with real symmetric slices X_r and B=sum_r X_r^2<=2I. Write g^2=||B-I||_F^2. Full tensor symmetry identifies the slice Gram matrix (Tr(X_r X_s)) with B, so its operator norm is at most2. Set

    E(A)=sum_r X_r A X_r,
    P(A)=sum_r Tr(X_r A)X_r.

These act on the full real matrix Hilbert space with its unnormalized Frobenius inner product. The same maps extend complex linearly. If mu is tensor multiplication and Delta=mu*, then Delta*Delta=B and

    ||mu(mu tensor I)-mu(I tensor mu)||_HS^2
      = ||E-P||_HS^2
      = 2 sum_(r<s) ||[X_r,X_s]||_F^2.

Indeed the associator coefficient at (d;a,b,c) is [X_a,X_c]_(b,d). Also ||E||_HS^2=||P||_HS^2=Tr(B^2), while <E,P>=sum_(r,s)Tr(X_r X_s X_r X_s). Finally ||P^2-P||_HS<=2g. These are identities and a spectral inequality, not a rounding theorem.

## A dimension-free unitalization at the channel level

There is an exactly unital CP map F, not asserted self-adjoint or tensor-derived, such that

    ||F-E||_HS <= sqrt(6)(sqrt(2)+sqrt(5)) g,
    ||F*(I)-I||_F <= 7g.

Here HS on maps is the Hilbert–Schmidt norm of their full matrix superoperator; it is not a completely bounded norm. The statement holds for every error size and m.

Proof. Let Q be the spectral projection of B for [1/2,2], let d=rank(I-Q), and let f(B) be lambda^(-1/2) on that interval and zero elsewhere. Choose an orthonormal basis of (I-Q)R^m with its rank-one projections R_j. Define the Kraus list

    Y_r=f(B)X_r  (1<=r<=m),
    Y_(m+j)=R_j (1<=j<=d).

Then sum Y_r Y_r*=Q+sum_j R_j=I. Thus F(A)=sum Y_r A Y_r* is unital CP. Pad the old Kraus list with d zeros and put D_r=Y_r-X_r. Spectral calculus gives

    d <= 4g^2,
    sum_r ||D_r||_F^2
      = sum_(lambda>=1/2)(1-sqrt(lambda))^2
        + sum_(lambda<1/2)(lambda+1)
      <= 6g^2.

For high eigenvalues use (1-sqrt(lambda))^2<=(1-lambda)^2; for low eigenvalues use lambda+1<=6(1-lambda)^2. The linear Kraus-column map of the old list has squared norm at most2. That of f(B)X_r has squared norm at most4, and that of the orthonormal R_j has squared norm1. The combined new list therefore has slice-Gram norm at most5.

For any two real Kraus lists U,V,

    ||sum_r U_r tensor V_r||_F^2
      <= ||Gram(V)||_op sum_r ||U_r||_F^2.

Expand F-E as the two sums D_r A X_r* and Y_r A D_r*. The last inequality and the two Gram bounds give

    ||F-E||_HS <= (sqrt(2)+sqrt(5)) (sum_r||D_r||_F^2)^(1/2).

For the second claim, let H=f(B)^2-I. The eigenvalue inequalities above give ||H||_F<=2g. Since E is self-adjoint and CP with E(I)=B<=2I, its induced Schatten2 norm is at most2 (interpolate its induced Schatten1 and infinity bounds). Therefore

    F*(I)-I = E(H)+(B-I)+(I-Q),
    ||F*(I)-I||_F <= 2||H||_F+g+sqrt(d) <=7g.

This proves only the stated channel interface. Output-side Kraus normalization need not preserve symmetry of each slice or full cubic symmetry. F need not preserve trace exactly. No passage from this map to a nearby unit orthodecomposable cubic has been proved.

## Bounded primary navigation and remaining gap

Kitaev's *Almost-idempotent quantum channels and approximate C*-algebras*, [arXiv:2405.02434v2](https://arxiv.org/html/2405.02434v2), uses a UCP map and a small completely bounded idempotence defect. The parent read its abstract, Section1.2 statement/functional-calculus discussion and the Section12 premise/conclusion passages; not the full proof. Its abstract C*-factorization is a research lead. The HS bounds here do not establish its cb hypothesis, nor the trace-paid control of extra classical modes or cubic compatibility required by the frozen target. No theorem from that paper is invoked in the lemma above.

The parent also saw the abstract of [Zenodo22906336](https://zenodo.org/records/22906336), reporting a simplex obstruction to nearby same-space idempotent channels. Its proof body is unread and is not a premise. The existing r69 simplex proof already illustrates the relevant distinction: an extra latent mode can be affordable for the tensor target even when exact same-space channel projection fails. Gowers–Hatami1510.04085 was seen through its abstract only; no approximate finite-group representation domain is constructed here. Poinsot2003.04149 and near-odeco perturbation results were navigation leads, not quantitative global premises.

The full all-error tensor estimate, hence the original source101 entropy target, remains unresolved. This note supplies no acceptance or count increment.
