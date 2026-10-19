# Full-scope attempts and precise stopping point

The target is the identical text in scope.md, copied byte-for-byte from r69. The new structured deflation obstruction is support only. No commuting subclass, small-total-error case, small-operator-density case, or conditional theorem is substituted for the target.

## Global best-basis route

For exact B=I let F(T)=max over orthonormal bases sum_i T(u_i,u_i,u_i), choosing orientations as part of the maximum. Then

 dist(T,O_m)^2=2m-2F(T).

At a maximizer, put a_i=T_iii. Independent sign choices give 0<=a_i<=1. Stationarity under rotation of each i,j pair gives T_iij=T_ijj=:b_ij. The second derivative of the same two-coordinate rotation gives

 12b_ij<=3(a_i+a_j).

More generally, for every real skew matrix Z, the full second-variation inequality is

 6 sum_i T(Ze_i,Ze_i,e_i)+3 sum_i T(Z^2e_i,e_i,e_i)<=0.

These assertions follow by differentiating exp(tZ), without claiming that a local maximum is global. If E is the tensor with every fully diagonal coefficient removed, then

 ||E||F^2=m-sum_i a_i^2,
 sum_i(1-a_i)<=||E||F^2<=2 sum_i(1-a_i).

Thus a dimension-free bound ||E||F^2<=K C(T) at a GLOBAL maximizing basis would finish the exact-Gram case. This is the unresolved coercivity statement. The local linearized commutator estimate only controls the part weighted by sufficiently large a_i; it does not control many small a_i or cancellations with the quadratic off-diagonal commutator. No valid deduction of this coercivity statement from the stationarity/Hessian inequalities was obtained. It is not entered as a lemma.

For B<=2I, neither a_i<=1 nor ||T||F^2=m is available. A separate Gram residual accounting or a direct variational inequality is needed. The congruence normalization obstruction from r69 prevents silently imposing exact B=I first.

## Copying-map and channel route

Parent author assistance restated the exact tensor as the adjoint pair mu:V tensor V->V and Delta=mu*. Full symmetry gives Delta*Delta=B. The squared HS norm of its coassociator is 2C; this is just the associator identity [X_a,X_c]_{bd}. It identifies a special commutative Frobenius-type stability problem but supplies no stability constant.

With J(v)=X_v, P=JJ* on full real matrix Hilbert space, and K(A)=sum_r X_r A X_r, the existing r69 index identities give

 ||K-P||HS^2=2C,
 ||P^2-P||HS^2=tr((B^2-B)^2)<=4||B-I||F^2,
 ||P||op, ||K||op<=2.

The bound for K follows directly from the elementary-operator row/column factorization and sum X_r^2=B. Consequently, expanding K^2-P^2=K(K-P)+(K-P)P gives the total estimate

 ||K^2-K||HS<=5sqrt(2C)+2||B-I||F.

This does not give a small completely bounded norm. Spectral thresholding changes only O(R) matrix-space modes at total HS cost O(R), but preserving complete positivity, the physical trace/unit, full cubic symmetry and unit-weight factors is a separate operation. A small-rank matrix-space mode can have full physical matrix rank; deleting its physical range is not trace-paid. No repair theorem satisfying these contracts was proved.

Parent screened an approximate C*-algebra primary lead but its body was not read by this worker and no theorem from it is used. In particular no finite-group approximate representation was constructed, no group stability theorem is invoked, and no same-space conditional expectation is inferred from an abstract factorization.

## Metric-deflation experiment and rigorous outcome

An initial rational four-dimensional unital example suggested that metric correction can increase both defects. That example was not used as the final witness because an arbitrary unital product need not possess the required HS-isometric matrix representation. The final witness in structured-metric-deflation-obstruction.md has an explicit such representation, small physical/cubic dimension difference, B<=I and H<=I. The global maximum and exact corrected residuals are proved, not inferred from the numerical search.

The only exploratory numerical commands used a pre-existing /tmp/agvenv Python with numpy/scipy; no runtime package was installed. These calculations are discovery diagnostics. Their floating output does not form any premise of the final proof. check_exact.py uses only the Python standard library and exact rational arithmetic in Q(sqrt(5)).

The ordinary-deflation obstruction was already paid in discovery-analytic-r100-parent/global-deflation-potential-obstruction.json. The new calculation concerns the subsequent specific metric correction and includes the structured ambient contract. Neither obstruction rules out grouped amortization or a new potential. Both forbid claiming that the two existing residuals decrease at every step.

## Status

No complete global bridge, full cubic theorem, weighted noncommuting pencil theorem or full entropy stability theorem has been obtained. The corrected operation now has an additional rigorous obstruction. The remaining obligations are unchanged: arbitrary Gram preprocessing at strong squared-residual cost and a noncascading all-density rounding operation. No nomination or count change is justified.
