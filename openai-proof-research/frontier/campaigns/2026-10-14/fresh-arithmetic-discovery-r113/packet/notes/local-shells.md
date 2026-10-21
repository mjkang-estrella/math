# Phase-free shell calculation, before any freeze
This continues the old r84 local model and credits the actual quartic local-fourier.tex proof (all 680 lines read). These are feasibility calculations, not a separate nomination.

Let E/Q_p have degree n=6, M its maximal order, O an arbitrary order, and gamma(A)=[O:O intersect A^-1 O]^-1. For invertible A put B=A^-1. Changing variables in O intersect A^-1 O gives EXACTLY
 gamma(A)=|N(A)|_p^-1 gamma(B).
For an integral scalar s, gamma(A+s)=gamma(A): Ax is in O iff (A+s)x is in O for x in O. No Gaussian phase, square-class choices or division by 2 occurs. If j is the least nonnegative integer for which p^j B belongs to O, the multiplication matrix of B on O has minimum Smith exponent -j (unless all nonnegative). Therefore gamma(B)<=p^-j. This strengthens the generic quadratic square-root estimate but is the elementary Smith/orthogonality mechanism already present in the companion.

Let h=product P_nu^h_nu be a denominator ideal, H=N(h), g=log_p[h:h intersect O]. Choose s from {0,...,6}. For p>7 at most six integral components forbid a scalar residue, so one choice makes A+s a unit in every integral component. Pole components keep valuation -h_nu. For p<=7, distinct choices differ in p-adic valuation at most 2, so at most one is forbidden per component by the stricter condition v_p(A_nu+s)>2. Thus alpha=A+s is invertible, beta=alpha^-1 belongs to p^-2 h, and |N alpha| is between p^-12 H and H. At p>7 the exact norm is H and beta belongs to h. Consequently
 gamma(A)<=C_p H^-1 p^-j,
where C_p=1 off {2,3,5,7}, and C_p<=p^12 otherwise.

Put N0=4(g+3). The shell restriction gamma_h is periodic under p^N0 h^-1. Indeed a translation t in this ideal leaves the shell and the selected shift's valuation bounds unchanged. Then
 beta' - beta = -t beta^2/(1+t beta) in p^(N0-4)h subset O,
using p^g h subset O and N0-4>=g. The denominator is a maximal-order unit. The inverse gamma and norm are unchanged, and hence gamma(alpha+t)=gamma(alpha). Zero extension is periodic too. Its inverse Fourier transform K_h therefore has support in p^-4(g+3)h d_E^-1. The original O-period also gives support in O^vee, so all traces are integral.

When g=0 and p>7, beta belongs to h subset O, so gamma_h(A)=H^-1 on the whole denominator shell. Its inverse is explicitly
 vol(M) product_nu k_nu(z_nu),
 k_nu=1_(d_nu^-1) for h_nu=0,
 k_nu=1_(P_nu^h_nu d_nu^-1)-q_nu^-1 1_(P_nu^(h_nu-1)d_nu^-1) for h_nu>0.
This has boundary saving product_boundary q_nu^-1, stronger than the companion's square-root saving. No factor independence of the original lattice O is assumed: h subset O is exactly the condition making the inverse multiplication integral, hence the Fourier function itself becomes constant on that shell.

At any output z with nonzero components, only finitely many K_h(z) are nonzero. Since g<=log_p[M:O], the support inequalities bound every h_nu in terms of v_nu(z_nu), the different, and that fixed index. Integrating gamma over p^-k M and using character orthogonality shows that the finite shell sum is the locally constant density f_p(z). This is the same finite-inversion operation as the companion, without an absolute-convergence shortcut.

For a scalar a with v_p(a)=-k, gamma(a)=p^-6k. The trace density d_p(t), t in Z_p, has a uniformly absolutely convergent Fourier series, with
 |d_p(t)-1| <= (1-p^-1)/(p^5-1).
Its product over any finite set of primes is bounded above and below by absolute positive constants. These are trace marginals only, not the needed full vector density bound.
