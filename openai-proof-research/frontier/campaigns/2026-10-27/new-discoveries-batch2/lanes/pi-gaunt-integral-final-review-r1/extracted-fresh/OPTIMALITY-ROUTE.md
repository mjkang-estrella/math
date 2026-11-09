# Optimality without a full asymptotic expansion

Work in progress, 28 October 2026; credit0. The completed lower-bound
checkpoint is untouched. This is an alternative ordinary proof of its
remaining optimal-order converse, with an explicit Lean plan.

Let δ≥0, ν>δ, μ²=δ²+2ν+1, and η>δ. By evenness it is enough to consider η>0.
Define A=(ν+η)/(2η), B=(η−ν)/(2η), and

    h(u)=cosh(μu)−A cosh((η+1)u)−B cosh((η−1)u).

Then h(0)=h'(0)=0 and h''(0)=δ²−η²<0. Continuity of h'' and two elementary
mean-value arguments give ε>0 with h(u)<0 on (0,ε]. Choose
0<a<b<ε and c>0 such that h≤−c on [a,b]. The function
exp(-cosh u)|h(u)| is integrable, by the already proved integrability of each
of the three Bessel integrands. Denote its integral by C≥0.

For x≥1, writing D(x)=∫_(u>0)exp(-x cosh u)h(u)du, direct domination gives

    D(x) ≤ −c(b−a)exp(−x cosh b)
               +C exp(−(x−1)cosh ε).

Indeed, on [a,b] the first term's constant integrand is a pointwise upper
bound, elsewhere in (0,ε] the integrand is nonpositive, and on (ε,∞) its
absolute value is at most exp(−(x−1)cosh ε)exp(−cosh u)|h(u)|.
One can add this nonnegative tail envelope on the whole domain, so no
unproved decomposition of improper integrals is needed. Since cosh b<cosh ε,
the displayed upper bound is eventually strictly negative. Hence D(x)<0
for every sufficiently large x.

The proved recurrence identifies

    D(x)=K_μ(x)−K_(η−1)(x)−(ν+η)K_η(x)/x.

Multiplying by x^(−ν), integrating to infinity, and using the proved
weighted-K derivative and zero boundary yields

    ∫_x^∞ t^(−ν)K_μ(t)dt − x^(−ν)K_η(x)
        = ∫_x^∞ t^(−ν)D(t)dt < 0

once x is beyond the eventual-negative threshold. Thus every absolute order
larger than δ fails. Orders at most δ follow from the completed bound and
monotonicity of cosh in its nonnegative order. This is one combined source
family; no additional credit for the argument or its generic lemmas.

This ordinary argument uses only the canonical integral, basic calculus,
positive integral comparison, and exponential decay. It does not assert
that the generic Laplace-domination principle is new. Formal work is not
complete until the literal converse and iff endpoints compile and pass a
fresh source replay. Source/novelty/substantive review remains independent.
