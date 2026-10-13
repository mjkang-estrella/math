# Supporting sharpness calculation for S302

2026-10-13. Parent analytic calculation, not independently reviewed and not a separate finding. This supplements the full S302 proposal without modifying its frozen analysis or the current I303 contribution target. It uses the same local scalar Hessian already studied in I128/I131.

Fix a,r in (0,1). For sufficiently small real epsilon, the implicit function theorem gives a positive even analytic c(epsilon) with c(0)=a and

    [psi(c(epsilon)+epsilon)+psi(c(epsilon)-epsilon)]/2=psi(a),
    c(epsilon)=a-epsilon^2/[2(1-a^2)atanh(a)]+O(epsilon^4).

Indeed the derivative with respect to c at (a,0) is atanh(a)>0, and the second derivative with respect to epsilon is 1/(1-a^2). Small epsilon ensures c(epsilon)+|epsilon|<1.

On the two-dimensional uniform cube take

    u_epsilon(X)=c(epsilon)X_1+epsilon X_2.

Its mean is zero, its range is in [-1,1], and its information is exactly psi(a). For sufficiently small epsilon the closest signed soft coordinate is aX_1: its correlation c(epsilon) is positive and larger than |epsilon|. Consequently

    d_a(u_epsilon)=[c(epsilon)-a]^2+epsilon^2
                   =epsilon^2+O(epsilon^4).

The noisy information is the average of psi(r(c(epsilon)+epsilon)) and psi(r(c(epsilon)-epsilon)). Taylor expansion therefore gives

    Delta_r(u_epsilon)=K(a,r)epsilon^2+O(epsilon^4),
    K(a,r)=1/2 [r atanh(ra)/((1-a^2)atanh(a))
                         -r^2/(1-r^2a^2)].

This coefficient is strictly positive. Put f(t)=(1-t^2)atanh(t)/t. Then

    f'(t)=[t-(1+t^2)atanh(t)]/t^2<0

for 0<t<1, since atanh(t)>t. The assertion K>0 is equivalent to f(ra)>f(a), which holds because ra<a.

Thus d_a/Delta_r tends to the finite positive number 1/K(a,r). No proposed replacement d_a<=C Delta_r^p with p>1 can hold even at one fixed interior parameter pair and n=2: its ratio diverges like |epsilon|^(2-2p). Equivalently the exponent one half in the ordinary L2 norm bound is optimal. On compact interior parameter rectangles the scalar Taylor expansion and positivity can also be made uniform, but that uniform strengthening is not needed for this optimality obstruction.

This is a supporting optimality example for the same global stability theorem. It does not change the unreviewed status of S302, establish its upper bound, or increase the accepted count.
