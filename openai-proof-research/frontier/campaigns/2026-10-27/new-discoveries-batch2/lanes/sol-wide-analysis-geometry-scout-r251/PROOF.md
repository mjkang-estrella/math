# Literal Conjecture 6.1 is false

Source: Dmitrii M. Ostrovskii and Pavel S. Shcherbakov, *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*, https://arxiv.org/pdf/2508.13554v2, Definition 6.1 and Conjecture 6.1, printed p15. The same statement occurs in v1. Frozen original/copy SHA256 bindings are in sources.jsonl.

Let D be the unit disk, I=[-1,1], E_n(D) the source class of entire functions satisfying ||g^(n)||_D <=1, f(z)=product_j(z-z_j), and Lg the polynomial of degree<n interpolating g at the source grid (confluent interpretation when needed). The first clause asserts, for EVERY 0<=k<n and EVERY self-conjugate grid in D^n,

    sup_{g in E_n(D)} |g^(k)(1)-(Lg)^(k)(1)| = |f^(k)(1)|/n!.

Self-conjugacy requires conjugate pairs and even multiplicity of every real node. Our grid has no real nodes and is simple, so both requirements hold without using confluent interpolation. We refute precisely this universal assertion, rather than a reformulation or normalization variant.

Take n=2, k=1, w=3/4+i/2, conjugate(w)=3/4-i/2, and g(z)=z^3/6. Each node has squared modulus 13/16<1. Since g''(z)=z, g belongs to E_2(D), whether the disk is taken open or closed. Also

    f(z)=z²-(3/2)z+13/16,
    Lg(z)=(23/96)z-13/64,
    g(z)-Lg(z)=f(z)(z+3/2)/6.

The last identity proves interpolation at both nodes. Since they are distinct, the degree-one interpolant is unique. Direct differentiation gives

    g'(1)-(Lg)'(1)=1/2-23/96=25/96,
    |f'(1)|/2=|2-3/2|/2=1/4=24/96.

Consequently the asserted supremum is at least 25/96, strictly larger than 24/96. This closes the full logical negation of the literal universal first clause. No maximizer existence or optimal constant is required. The adjacent uniform-in-z Conjecture 6.3 is NOT refuted by this argument.

For completeness, the additional z=0 clause also fails even with STRICTLY positive real parts. Use w=1/100+i/2, its conjugate, and the same g. Here |w|²=2501/10000<1. The interpolation slope is (3/10000-1/4)/6=-2497/60000, so

    |g'(0)-(Lg)'(0)|=2497/60000 > 1/100 = |f'(0)|/2.

This is a second witness in the same family, not a separate discovery. Neither witness exploits repeated nodes, zero denominators, a boundary grid, non-entire functions, or a non-real target function.

A general derivation and a separate recurrence route are in discovery.md. checks.py verifies all polynomial identities and rational inequalities without floating-point arithmetic. Mathematical validity does not settle novelty or substantive acceptance; those gates remain open.
