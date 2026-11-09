# Retaining the source gradient slack and a matrix column estimate

Author deduction of a stronger source-paid supporting estimate; no full stability claim.

## Gradient remainder already retained in the proof

Actual reading of matrix.tex526–590 shows the final polynomial difference is (1/50)(1-2u)(1+68u). At chaos degree d>=2, u=1/d, its discarded contribution is

 [(d-2)(1+68/d)/50] ||Y_d||².

Together with the displayed 1/500 remainder, its coefficient is at least d/1000: equality at d=2, and for d>=3 already (d-2)/50>=d/1000. Therefore precisely the same source proof gives

    2delta >= ||gradient Y||²/1000 +Omega_B/1000.    (G)

This is credited proof reuse, not an independently new entropy inequality.

## Dimension-free mixed derivative estimate

Let q be the inverse Gaussian hazard used in the source. There is a finite absolute constant M such that, for every real symmetric H,D and every family of symmetric X_r with sum X_r²<=bI,

    (sum_r ||D²q(H)[D,X_r]||_F²)^(1/2)
       <= M sqrt(b)||D||_F.                         (F)

Here D²q is the second Frechet derivative. A scalar bound on q'' alone is NOT the proof.

First q'' belongs to H¹(R), so its Fourier transform is integrable by Cauchy–Schwarz with (1+t²)^-1. To check the tails directly, for a>0 the Gaussian tail integral gives

 q(a)=a/F(a^-2), F(u)=integral_0^infinity exp(-v-u v²/2)dv.

F is C-infinity on u>=0 with derivatives controlled near0 by integrable powers of v; F(0)=1 and F'(0)=-1. Taylor's formula with differentiated remainders gives q(a)=a+a^-1+O(a^-3), with differentiated errors through order3. Thus q''=O(a^-3), q'''=O(a^-4). For a->-infinity, q=phi(a)/Phi(-a), with denominator bounded below, so these derivatives are bounded by polynomials times a Gaussian. Smoothness handles the compact interval.

Write q''(s)=integral alpha(t)e^(its)dt with integral|alpha|<infinity, fixing any consistent Fourier normalization. The second-divided-difference simplex formula and spectral functional calculus express D²q(H)[D,X] as the integral of

 e^(its0H) D e^(its1H) X e^(its2H)
   + e^(its0H) X e^(its1H) D e^(its2H)

against alpha(t) dt and Lebesgue measure on s0+s1+s2=1, sj>=0 (area1/2). Each term has the family column norm at most sqrt(b)||D||F. For instance sum_r||D U X_r||F²=tr(D*D U B U*)<=b||D||F²; the reversed term uses sum X_r*X_r=B. Unitary factors do not change Frobenius norm. Minkowski proves(F) with M=integral|alpha|. Real symmetric matrices may be complexified for these unitary factors.

Apply(F) along H=L+tY, with D=Y, at each Gaussian point. Since partial_r L=X_r and partial_r A=X_r+partial_rY,

 partial_r q(L)-partial_r q(A)
   =(Dq(L)-Dq(A))[X_r] -Dq(A)[partial_rY].

The last term has column norm at most ||gradientY|| because 0<q'<1 gives contraction in Frobenius norm. Integrating(F) in t and then in Gaussian x yields

 ||gradient(q(L)-q(A))||_2
      <= M sqrt(b)||Y||_2+||gradientY||_2.         (H)

When delta is below the absolute threshold giving B<=2I, the source remainder and(G) make the right side at most (M sqrt(2000)+sqrt(2000))sqrt(delta). Since q(A)=DF is a Jacobian, its curl vanishes. Thus curl q(L) has a genuine dimension-uniform L2 bound O(sqrt(delta)), stronger than the previous negative-order statement.

This removes one analytic regularity obstacle. It does NOT extract full symmetry of T, prove a positive coupled odd/even coercivity estimate, or supply global approximate-associativity stability. Those remain distinct debts. Scalar exact q'' tail estimates, Fourier inversion, and simplex functional calculus here are original author derivations using standard calculus, not claims that those precise estimates were stated in the source.
