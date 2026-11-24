# MathDB announcement draft

Status: local draft, not posted. Author: Myeongjin Kang, Independent researcher.

Target: [Parity conjecture for the Möbius function on shifted primes](https://mathdb.com/p/377990/parity-conjecture-for-the-mobius-function-on-shifted-primes).

Suggested title: **A conditional proof via factor-count residues of prime predecessors**

I have prepared an AI-assisted manuscript, *Factor-count residues and Poisson–Dirichlet limits for prime predecessors*, which gives a proof of this conjecture conditional on specified analytic inputs from the OpenAI mathematics repository.

The main statement is broader: in every fixed reduced arithmetic progression, the number of prime factors of $p-1$, counted with multiplicity, is asymptotically uniform modulo each fixed integer and independent of the limiting ranked logarithmic factor sizes, whose law is Poisson–Dirichlet with parameter 1. The parity case also includes the squarefree indicator and its progression-dependent density.

For the problem stated here, the relevant consequence is that, for every fixed finite set $S$ of primes and fixed valuations $e_q$,

$$
\sum_{\substack{p\leq x\\v_q(p-1)=e_q\ (q\in S)}}\mu_S(p-1)=o(\pi(x)).
$$

The assumptions are listed by source statement in the manuscript. They include dilation-graph transference, long-prime and extraction estimates, a scalar marked-coefficient estimate, and a zero-free half-plane for Dirichlet $L$-functions, all at [the immutable corpus revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). I am not presenting these premises as independently verified here.

AI systems assisted with the mathematical development, checks, reviews, and writing. The draft has not undergone external human peer review or formal proof verification. I welcome scrutiny of the deduction from the stated premises, particularly the fixed-progression transfer and the reconstruction of the complex principal term.

The preprint and LaTeX source are available on [Zenodo](https://doi.org/10.5281/zenodo.23270419).

---

Preparation note, not part of the post: accompany the announcement with the reviewed manuscript or a stable public link. Update its unpublished status if needed. Do not label this an unconditional solution, invent an arXiv identifier, or mark the problem solved on the strength of internal AI reviews. The source conjecture is [Moree and Hommersom, Conjecture 1](https://arxiv.org/abs/math/0307352v1). The MathDB target was checked on October 9, 2026; it displayed no posted solutions at that time.
