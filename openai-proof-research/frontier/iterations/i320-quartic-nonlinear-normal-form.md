# I320 — optimal quartic correction near weak affine signals

2026-10-13. Parent analytic derivation, **not independently reviewed** and not a new acceptance. This is a finite-dimensional local calculation toward unresolved S313. It does not justify uniform expansions over arbitrary low-information kernels, dimensions or means approaching an endpoint. A first file-writing attempt failed on Python quote syntax and wrote no file; this patch supplies the intended record.

## Statement

Fix a finite cube, |m|<1, h=1-m², and a first-level function f=sum_i c_i X_i with E f²=h. Let g be orthogonal to constants and all first-level Walsh functions. Consider a bounded family

    u_a=m+a f+a²g+a³j+O(a^4)

in the finite-dimensional supremum norm, with Eu_a=m and exactly I(u_a)=psi(a). The leading direction f is fixed, psi(x)=((1+x)log(1+x)+(1-x)log(1-x))/2, and r is fixed in (0,1). Orthogonality makes Efg=0; symmetry makes Ef³=0. Thus third-order matching is automatic, and the fourth-order information equation determines E(fj). Higher-order changes enforce exact information without changing the coefficient below.

Write g=sum_(k>=2) g_k in Walsh levels and V=Var(f²)=2(h²-sum_i c_i^4). Then

    lim_(a->0) [psi(ra)-I(T_r u_a)]/a^4
      = r²(1-r²) [ m²/(3h)+(1-3m²)V/(12h³)
          + ||g_2+(m/h)(f²-h)||_2²/(2h) ]
        + sum_(k>=3) (r²-r^(2k)) ||g_k||_2²/(2h).       (N320)

In particular the unique optimal second-order correction is

    g_opt=-(m/h)(f²-h),

with no higher Walsh modes. If kappa=sum_i c_i^4/h², its minimum coefficient is

    r²(1-r²) [kappa*m²/(3h)+(1-kappa)/6].             (M320)

The bracket is at least (m²+1-kappa)/12. Fixed nonzero bias therefore has a positive quartic deficit even after optimizing this correction, and diffuse leading directions also have a positive quartic deficit. The only zero of the minimum on a finite cube is m=0 with f a signed coordinate. This statement concerns the normal form, not arbitrary small-information sequences.

## Calculation

At the fixed mean m, the second, third and fourth derivatives of psi are respectively 1/h, 2m/h² and 2(1+3m²)/h³. Because f is first level, f²-h is exactly second level and Ef³=Eg=Efg=0. Taylor expansion gives

    I(u_a)=a²/2 + a^4 [ (||g||²+2Efj)/(2h)
                + m E(f²g)/h² + (1+3m²)Ef^4/(12h³)] + O(a^5).

The mean of the O(a^4) remainder is zero by the exact fixed-mean condition; its linear entropy term therefore vanishes. Exact information psi(a)=a²/2+a^4/12+O(a^6) determines the displayed bracket as 1/12. Noise sends f to rf and g_k to r^k g_k. In the fourth-order output expansion,

    E[(rf)² T_rg]=r^4 E(f²g_2),
    E[(rf) T_rj]=r² E(fj).

Eliminate E(fj) using the input constraint to obtain

    lim Delta/a^4 = sum_(k>=2)(r²-r^(2k))||g_k||²/(2h)
       + r²(1-r²)[m E(f²g_2)/h²
          +(1+3m²)Ef^4/(12h³)-1/12].

Complete the square on g_2. Since Ef^4=h²+V, the constant after completion is m²/(3h)+(1-3m²)V/(12h³). This proves N320. Substituting V=2h²(1-kappa) gives M320. Its bracket is at least m²/6, since both endpoints of that convex mixture are at least m²/6. It is separately at least (1-kappa)/6. Averaging proves the stated bound. Every remaining term in N320 is nonnegative.

## Exact attainability

Fix f and g_opt. For small a put u_a=m+a alpha(a)f+a²g_opt. The finite-cube analytic function

    [I(m+a alpha f+a²g_opt)-psi(a)]/a²

extends analytically to a=0, with value (alpha²-1)/2 there and derivative one in alpha at alpha=1. The analytic implicit-function theorem produces alpha(a) and exactly matching information. Orthogonality and Ef³=0 give alpha'(0)=0. Since g_opt is even under simultaneous sign reversal and f is odd, uniqueness also makes alpha even. Thus alpha(a)=1+O(a²), and this family has the claimed normal form. It remains within (-1,1) for sufficiently small a because m is fixed and the cube is finite. This proves attainability rather than a formal infimum alone.

## Boundary of the deduction

I313 proved the affine endpoint but left a nonlinear reduction unpaid. Here the dangerous quadratic correction is optimized explicitly. For |m|>1/sqrt(3), spreading the leading direction can reduce the quartic deficit relative to a biased coordinate; it still cannot cancel it. Treating every biased coordinate as a transverse local maximizer would therefore be invalid.

The remainder is not uniform as m approaches either endpoint, dimension increases, coefficients vary with a, or fixed-height rare spikes appear. I313's exactly normalized spikes show that uniformity cannot be presumed. No argument yet puts an arbitrary low-information kernel in this normal form. The full S313 theorem still needs a relative-error nonlinear reduction or appropriately weighted coercivity, including exact information and control of rare events. This is a technical partial, with no inherited contribution credit from R020. A future independent round must check every coefficient and this boundary before using it.
