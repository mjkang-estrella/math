# Selected cutoffs do not inherit the small-time commutator

We prove a scoped obstruction on R². It is NOT a counterexample to maximal boundedness: the field below is constant and its classical maximal transform is bounded.

Fix any a>0 and v=(1,0). Write H^r_a for the fixed-cutoff horizontal transform. Let E={y:cos y>0} and set ε(y)=a/4 on E and a/2 off E. The selected operator is

    A_a = H_a^{a/2} + M_E D_a,
    D_a = H_a^{a/4}−H_a^{a/2}.

Let P=p(D_y) where p is smooth, equals1 on[−1/10,1/10], and is supported in(−1/2,1/2). It is a fixed vertical multiplier satisfying the source Mihlin seminorm assumptions with a constant independent of a. Choose nonzero Schwartz h with Fourier support in(−1/10,1/10). The periodic function1_E has mean1/2 and its other Fourier frequencies are nonzero integers. The frequency translates of h by these integers are disjoint and outside supp p. Thus

    Ph=h,      P(1_E h)=h/2,
    [P,M_E]h=(1/2−1_E)h,
    ||[P,M_E]h||₂ = ||h||₂/2.                                   (1)

The Fourier-series argument is justified in L² by bounded periodic approximation or by summing its disjoint translated Fourier bands; the square-wave coefficients are square summable. Equality of the final norm also follows pointwise since|1/2−1_E|=1/2 almost everywhere.

Choose nonzero Schwartz g_a with Fourier support in[1/a,11/(10a)], using Fourier convention e^(−ixξ). The multiplier of D_a is

    m_a(ξ)=−2i ∫_{a/4}^{a/2} sin(ξt) dt/t.

On this support, 1/4≤ξt≤11/20<1. Since sin s≥s−s³/6≥s/2 for0≤s≤1,

    |m_a(ξ)| ≥ 2∫_{a/4}^{a/2} ξ/2 dt = aξ/4 ≥ 1/4.

Plancherel gives||D_a g_a||₂≥||g_a||₂/4. Set f_a(x,y)=g_a(x)h(y). Fixed horizontal transforms commute with P, so

    [P,A_a]f_a = (D_a g_a)⊗([P,M_E]h),
    ||[P,A_a]f_a||₂ ≥ ||f_a||₂/8.                               (2)

Therefore no bound||[P,A_a]||₂→₂≤C a, with C independent of a and of measurable cutoff selection, can hold as a↓0. For a fixed cutoff and this constant field the commutator is identically zero. The new term is exactly[P,M_E]D_a; it has nothing to do with turning of v.

The source O(a) integrated commutator keeps the time integration domain independent of output. Its proof integrates the O(|t|) commutator of a Lipschitz composition and a vertical multiplier. Selected cutoffs add the rough output multiplier above, outside that hypothesis. An argument which works with all cutoff values as a Banach-valued output before selection might evade this obstruction; no such complete reassembly estimate is proved here.
