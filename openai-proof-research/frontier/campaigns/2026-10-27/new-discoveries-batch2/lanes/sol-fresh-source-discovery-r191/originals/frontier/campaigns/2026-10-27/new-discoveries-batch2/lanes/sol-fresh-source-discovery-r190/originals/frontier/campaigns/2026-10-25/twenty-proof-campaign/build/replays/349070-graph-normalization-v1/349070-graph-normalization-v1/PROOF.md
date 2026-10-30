# The graph-normalization adjacency inequality

Let B be any finite symmetric matrix with nonnegative entries, x a nonnegative vector, and s_i=∑_j B_ij x_j>0 for each i. Define y_i=x_i/s_i. Then yᵀBy≤∑_i y_i.

For any real vector a, the elementary inequality 2a_i a_j≤a_i²+a_j², multiplied by the nonnegative weight B_ij x_i x_j and summed, gives

\[
2\sum_{ij}B_{ij}(x_i a_i)(x_j a_j)
\le \sum_{ij}B_{ij}x_i x_j(a_i^2+a_j^2)
=2\sum_i x_i a_i^2 s_i.
\]

The last equality follows by interchanging i and j in the second squared term and using symmetry. Take a_i=1/s_i. The left side is 2yᵀBy and the right side is 2∑_i x_i/s_i. This proves the claim.

Now let G be any finite simple undirected graph, A its adjacency matrix, and B=A+I. Its entries are nonnegative and symmetric. For strictly positive x, each s_i≥x_i>0 because B_ii=1. Thus the claim applies. Every y_i is positive, so ∑_i y_i=∑_i |y_i|=‖y‖₁. This is exactly Conjecture8.1, equation(19), in Guigues, [arXiv:2012.07764v1](https://arxiv.org/html/2012.07764v1), the target of MathDB349070. Connectivity is unnecessary.

## Formal coverage

`symmetric_energy_le` proves the summed weighted Young inequality for arbitrary finite types. `normalized_energy_le` substitutes the actual reciprocals. `closedKernel` is the explicit graph kernel; `closedKernel_eq_adj_add_one` identifies it with mathlib's `SimpleGraph.adjMatrix` plus the identity. Positive row sums and the absolute-value bridge are proved in `graph_normalization_inequality`. Finally `mathdb349070` states the result using mathlib's actual matrix-vector product and dot product. There are no assumed graph or normalization bridges.

## Status and scope

The diagonal majorization inequality is standard. Guigues's later [arXiv:2605.05330v1](https://arxiv.org/html/2605.05330v1), Appendix B, explicitly uses this majorization for symmetric nonnegative matrices. Substituting the normalized vector into that displayed inequality yields the result here. This is an elementary complete formal verification of the consequence, without a claim of mathematical novelty. We do not prove or endorse the later paper's separate global-convergence claims. No convergence of the iterated weights, convergence to a maximum independent set, or nonlinear-activation claim follows merely from the inequality proved here.
