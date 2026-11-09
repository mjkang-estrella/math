# PREFREEZE calculation: changing the scalar tube potential

This is an elementary ansatz calculation after the source tube transfer and classical Calabi/momentum formulas, not a frozen finding or nominee. It concerns the one-sided Source359 tube only; it does not combine its Liouville property with the different threefold's two-sided pinching.

## Exact scope and metric convention

Let ell be the smooth strictly plurisubharmonic base potential used in the source, on C^(n+1). Its real potential metric is g_ell=Re(ell_{i bar j} dz_i tensor dbar z_j), without the companion threefold's factor of two. Suppose it has at least one strictly negative real sectional plane. Keep the entire tube T={b=Im w-ell(z)>0} and use a scalar potential f(b), with f smooth on (0,infinity),

    a(b)=-f'(b)>0, c(b)=f''(b)=-a'(b)>0.

These conditions are exactly positivity of this ansatz. With theta=du+d^c ell and d^c=-d composed with J,

    g_f = a pi^*g_ell + (c/4)(db^2+theta^2).

No assumption that T is biholomorphic to a product is made; the (z,u,b) product coordinates are smooth real coordinates only.

## Curvature computation

At any fixed base point choose Kahler normal coordinates and a holomorphic w-translation absorbing the pure terms in the three-jet of ell. Then that jet is constant+|z|^2. At the point, g_f is diagonal with entries a I and c/4. Write Rcal for the Hermitian curvature convention of one-sided equation tube:hermitian-curvature.

Differentiating the potential through fourth order, including the inverse-metric cubic contractions, gives

    Rcal^f_{i bar j k bar l}
       = a Rcal^ell_{i bar j k bar l}
         - c(delta_ij delta_kl + delta_il delta_kj),
    Rcal^f_{i bar j w bar w}
       = (c' + c^2/a) delta_ij / 4,
    Rcal^f_{i bar w k bar w}=0.

For example, at the normal point the direct fourth derivative in the mixed component contributes c'/4, while contraction of partial_i g_{w bar q}=i c delta_iq/2 with its conjugate gives c^2/(4a). This records the term that would be missed by treating the horizontal and vertical blocks as a direct product.

For base-orthonormal real X,Y, let Xhat,Yhat be their theta-horizontal lifts. Using precisely the real/complex conversion of source equation tube:real-complex-curvature yields

    K_f(Xhat wedge Yhat)
       = K_ell(X wedge Y)/a
         - (c/a^2)(1+3 g_ell(JX,Y)^2).                 (1)

For a plane spanned by a horizontal unit direction and a real vertical direction, the unbalanced Hermitian component vanishes, and its sectional curvature is

    K_mix = c'/(a c) + c/a^2
          = (1/a) (log(c/a))'.                      (2)

Substitution f=-log b gives a=1/b,c=1/b^2, K_mix=-1 and exactly the source horizontal formula K=b K_ell-1-3 g_ell(JX,Y)^2. This also fixes the real sectional normalization; holomorphic sectional curvature in the flat-base model is -4, not -2.

## Completeness and an upper negative bound force a to tend to zero

Assume, within this ansatz, that g_f is complete and that all real sectional curvatures are <=-A for a fixed A>0. Since a is positive and decreasing, a_infinity=lim_{b->infinity}a exists and is nonnegative.

If a_infinity>0, equation (2) gives

    (log(c/a))' <= -A a <= -A a_infinity.

For b>=b0, integration and a(b)<=a(b0) imply

    c(b) <= c(b0) exp[-A a_infinity (b-b0)].

The vertical curve with z and u fixed and b->infinity then has length

    (1/2) integral_{b0}^infinity sqrt(c(b)) db < infinity.

It escapes every compact subset of the full tube. This contradicts metric completeness. Therefore a_infinity=0.

Fix the negative base plane with K_ell=-kappa<0 and move upward above that same base point. Formula (1) gives K_f<=-kappa/a(b), which tends to minus infinity. Thus a complete metric from any such scalar f(b) with a uniform strictly negative real sectional upper bound cannot have a finite sectional lower bound on this full tube.

## What this does and does not pay

This closes the scalar-potential repair attempt at its full ansatz scope; it is not an assertion about all Kahler metrics on T. It uses no global lower bound on base curvature and no assumption about a complex product decomposition. The source already supplies a negative base plane and the special logarithmic case; the added scalar ODE is a classical calculation. It is not offered as the requested substantial additional result.

It does not exclude a spatially dependent potential, a genuinely different domain or gluing construction, or a different way to implement the analytic tests. A two-sided-pinched Liouville example would still need an actual complete all-real-plane curvature construction preserving the source's exponentially large testing disks. No such operation has been proved here. The two-sided threefold's bounded base coordinates are nonconstant, so that existing example cannot supply the Liouville property by relabeling or rescaling.

The momentum construction of Hwang–Singer (actual v1, physical pp.8–18) supplies relevant metric/completeness calculus; it does not automatically yield a two-sided real sectional estimate on this noncompact source base. The bundle constructions of Hao–Chen–Wang and Hao–Chen–Wang–Zhang have additional base/curvature hypotheses; those must not be silently assigned to ell. Detailed reading and compatibility limits are recorded separately.
