# Amplitude assembly from the two pressure comparisons

Myeongjin Kang. Original prose CC BY 4.0. Author-side proof component for frozen T216A. The lattice input is proved in lattice-interface.md. The continuum equality is proved in the copied parent author note continuum-boundary-pressure.md; exact authorship and hash are recorded in parent-provenance.json.

Put p_*=16/15 and gamma=1/15. Use the exact model, a_n, A=A_XY and kappa from lattice-interface.md. Let

    c_* = lim_(t→infinity) [log E exp(t Re mu_*(D))]/[4t^(p_*)]

in the ultraviolet-only convention beta=1/2. This is positive finite by the corrected whole-plane imaginary-chaos tail theorem of Aru–Baverez–Jego–Junnila and the elementary Laplace principle, as proved in continuum-boundary-pressure.md. That author lemma proves that the same limit holds with mu_D in the ultraviolet-only normalization.

For every fixed t>0 the lattice note proves

    F_*(kappa t)/4 <= liminf_(n→infinity) n² Delta p(t/(n²a_n))
       <= limsup_(n→infinity) n² Delta p(t/(n²a_n)) <= F_D(kappa t)/4.       (1)

The fixed-t Laplace convergence also holds for any sequence t_n→t. Indeed the uniform lattice exponential moment bound at, say,2t+2 makes exp(t_n X_n) uniformly integrable, while the convergence of X_n and t_n gives convergence in law. This observation is essential for the full real h limit below.

For 0<h<e^(-1), and fixed t>0, choose the integer

    n(h,t)=floor[(t/A)^(8/15) (15/8)^(1/30)
                    h^(-8/15) (log(1/h))^(-1/30)].                       (2)

For small enough h it is positive and tends to infinity. Write u=log(1/h). Directly,

    log n / u -> 8/15,
    h n² a_n -> t,
    n² h^(16/15) u^(1/15)
          -> (t/A)^(16/15) (15/8)^(1/15).                                (3)

For example, n²a_n~A n^(15/8)(log n)^(1/16). The powers in (2) give u^(−1/16)u^(1/16)=1, and the constants (15/8)^(1/16)(8/15)^(1/16) cancel. The floor has relative error tending to zero. No monotonicity of n²a_n is required.

Apply the exact lattice sandwich at h and n(h,t). Its finite-box tilt is t_h=h n(h,t)²a_(n(h,t))→t, so fixed-tilt convergence with moving t_h and (3) imply

    A^(16/15)(8/15)^(1/15) F_*(kappa t)/(4t^(16/15))
      <= liminf_(h↓0) Delta p(h)/[h^(16/15)u^(1/15)]
      <= limsup_(h↓0) Delta p(h)/[h^(16/15)u^(1/15)]
      <= A^(16/15)(8/15)^(1/15) F_D(kappa t)/(4t^(16/15)).                 (4)

This holds for every fixed t. Now, and only now, send t→infinity. The two continuum limits coincide, giving the full pressure amplitude

    C_p=c_* (A kappa)^(16/15) (8/15)^(1/15) in(0,infinity).               (5)

In particular no simultaneous lattice/growing-tilt limit was exchanged. The two one-parameter limits are coupled by inequalities valid before either limit. The factor1/4 is the area of the reference square D; changing the reference square changes A and kappa consistently and does not change the physically normalized result.

For completeness derive magnetization, rather than differentiating an asymptotic without justification. Convexity of p and differentiability for h>0 give, for each lambda>1,

    [Delta p(h)−Delta p(h/lambda)]/[h−h/lambda]
        <= m(h) <= [Delta p(lambda h)−Delta p(h)]/[(lambda−1)h].            (6)

Since log(1/(lambda h))/log(1/h)→1 and similarly for h/lambda, divide (6) by h^(1/15)u^(1/15) and use (5):

    C_p (1−lambda^(−16/15))/(1−lambda^(-1))
       <= liminf m(h)/g(h) <= limsup m(h)/g(h)
       <= C_p (lambda^(16/15)−1)/(lambda−1).

Sending lambda↓1 proves

    C_m=(16/15)C_p,
    m(h)/g(h) -> C_m in(0,infinity).                                     (7)

This is exactly the full frozen target. The source zero-field bulk amplitude equals (A kappa)², so (5) may also be written using its8/15 power; that is only a normalization check, not another result.

## Scope of this component

Everything after the two continuum pressure limits is ordinary asymptotic inversion and convex secant comparison. These steps receive no independent substantiality claim. The potential contribution is the complete source-specific passage through the lattice neutral sector and the rigorous continuum boundary-pressure identification. Closest antecedents, including the Ising continuum pressure boundary argument, must be assessed separately even if the proof is correct.
