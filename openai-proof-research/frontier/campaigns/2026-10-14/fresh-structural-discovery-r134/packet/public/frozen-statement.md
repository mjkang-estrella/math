# Frozen statement (r134)

Frozen before proof drafting, after the prefreeze calculations recorded in working-notes.md.
Provenance: Factory Droid / claude-opus-5-5 / high. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (stipulated true).

## Conventions

All graphs are finite and simple; the graph with no vertices is allowed. Logarithms are natural.
For a graph G, i(G) is the number of independent sets of G, the empty set included, and d_v is the
degree of v in G. For nonnegative vertex weights w,

    F_G(w) = sum_v w_v (1 - log w_v) - M_G(w),    M_G(w) = sum_{uv in E(G)} w_u w_v,    0 log 0 = 0,

and F*_G = max_{w >= 0} F_G(w), with F*_G = 0 for the graph with no vertices. This is the functional of
`sec:optimizer` in the pinned manuscript *A logarithmic independence bound for clique-free graphs*
(September 25, 2026). For an integer r >= 2, B_r = C_triangle(16 r^2) is the constant of that manuscript's
display `eq:optimizer-triangle`, and

    C_r = 2 + (3/2) B_r.

## Theorem

Let r >= 3 be an integer, and let G be a finite simple K_r-free graph with n vertices. Then

1. log i(G) >= F*_G / (3 C_r);
2. log i(G) >= (1 / (12 C_r)) * sum_{v in V(G)} (log(d_v + 16))^2 / (d_v + 16);
3. if n >= 1 and G has average degree d, then
   log i(G) >= n (log(d + 16))^2 / (12 C_r (d + 16)),
   and if moreover d >= 2, then log i(G) >= n (log d)^2 / (108 C_r d).

The constant C_r depends only on r. No maximum-degree, minimum-degree or regularity hypothesis is made.

## Scope notes (part of the frozen record, not extra hypotheses)

- Part 3 for average degree is, up to the constant, already a routine consequence of the pinned
  average-degree theorem and Cooper-Dutta-Mubayi Theorem 4 / Remark 5 (arXiv:1310.6672v1). The claimed
  increment is parts 1-2: a degree-sequence (vertexwise) bound without a global degree scale.
- For r = 3 (triangle-free graphs) degree-sequence bounds of this type are already in the primary
  literature (Davies, arXiv:2609.04654v1, Theorem 5 with a = 0). No novelty is claimed for r = 3.
- No degree-sequence bound for the independence number alpha(G) is claimed.
