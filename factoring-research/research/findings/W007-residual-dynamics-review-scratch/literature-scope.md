# Literature scope for the residual-dynamics review

Read 2026-10-08. No theorem below is imported into the identities.
The drift law and the depth-1/depth-3 counts are proved directly in
`W007-residual-dynamics-review.md`.

## Dense modular composition does not price this chain

Neiger, Salvy, Schost, and Villard, "Faster Modular Composition",
arXiv:2110.08354v2, abstract retrieved from https://arxiv.org/abs/2110.08354.

The problem stated there is composition of two polynomials modulo a third,
for dense inputs of degree bounded by n, in O(n^1.43) field operations.
The abstract attributes the previous general bound O(n^1.63), and the
power-series bound n^{3/2+o(1)}, to Brent and Kung (1978). The 1978 paper
itself was not opened.

That operation expands or reduces dense degree-n polynomials. For the nested
map here the dense degree is n=2^k, so those algorithms are exponential in
the number of quadratic stages. They do not provide an o(k) evaluation of
one succinct nonautonomous tower, nor an o(k^2) acquisition of the triangular
training values. Nothing from this abstract is used as a lemma.

## Degree lower bound

The one-point bound in the review is the elementary degree-doubling argument
written there: after m non-scalar multiplications the degree in the probe is
at most 2^m, while the monic tower has degree 2^k. Ostrowski's polynomial-evaluation
bounds and the Baur–Strassen derivative bound were not used. In particular,
no Ω(kL) multi-point lower bound is claimed. Cancellation across several
training indeterminates is exactly the missing operation, not a proved obstacle.
