# TARGET — r2 (family 113)

**Source family:** 113 — "Approximate counting and entropy of perfect matchings"
(fresh by bounded evidence: no tasks.json claim, absent from the accepted audit; only a
catalogue entry and an unrelated K₆/Metropolis mention elsewhere).

**Pinned sources (blob-verified via private/fetch.py against the canonical tree):**
- `A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026` (main.tex)
- `Entropy-and-Face-Dimension-of-the-Perfect-Matching-Polytope-September-23-2026` (sections 01 intro, 02 polytope, 03 entropy, 10 examples)

**The genuinely-unpaid finite estimate.** On the perfect-matching polytope $P(G)$, for a
point $x$ let $F(x)=\sum_e -x_e\log x_e$, $B(x)=\sum_e -(1-x_e)\log(1-x_e)$, and $H(x)$ the
entropy of the maximum-entropy perfect-matching law with marginals $x$. The source proves
$$F(x)-\Big(2-\tfrac{2}{m}\Big)B(x)\;\le\;H(x)\;\le\;F(x)\qquad(|V(G)|=2m),$$
and constructs the Klee / triangle-expansion family $G_m$ forcing the lower-bound constant
$$c\;\ge\;\frac{\ln 3}{2\ln(3/2)}\;\approx\;1.3548.$$
The source **explicitly does not establish optimality of the coefficient two**, leaving the
optimal coefficient
$$c^\*\;\in\;\big[\,\tfrac{\ln 3}{2\ln(3/2)}\approx1.3548,\;2\,\big]$$
as a flagged open problem. This is the unpaid finite estimate.

**Specific question resolved here.** Can the cut-forcing (Klee/triangle-expansion)
lower-bound method be pushed to higher degree to raise $c$ above
$\tfrac{\ln3}{2\ln(3/2)}$ toward $2$? I.e., do higher-degree *forcing gadgets* exist, and
what structural constraints must they satisfy?

**Outcome (see candidate.md):** A structural necessary condition (Hetyei-type) showing the
degree-$3$ Klee triangle is the *unique* zero-non-port forcing gadget and that degree-$k\ge4$
forcing gadgets require $\ge k-1$ non-port vertices, together with exhaustive/sampling
computation showing no degree-$4$ forcing gadget exists at small orders. The forcing method
is therefore obstructed below $2$; the open coefficient is not resolved (barrier result).
