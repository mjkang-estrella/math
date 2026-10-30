# Author proof: a degree-sequence count of independent sets in clique-free graphs

Provenance: Factory Droid / claude-opus-5-5 / high, round r134 (2026-10-20). Author proof only; no correctness,
contribution, acceptance or count is self-assigned. The exact claim is packet/public/frozen-statement.md
(SHA-256 4d491e34d80254c3b6b0d4d7a289500505bb2826fc4e4db4b3de55a92913221c), restated below without change of scope.

## 1. Statement

Conventions: finite simple graphs, possibly with no vertices; natural logarithms; i(G) counts independent sets
including the empty set; d_v is the degree of v in G. For w in [0,∞)^{V(G)},

    F_G(w) = Σ_v w_v(1 − log w_v) − M_G(w),   M_G(w) = Σ_{uv∈E(G)} w_u w_v,   0 log 0 = 0,
    T_G(w) = Σ_{triangles {a,b,z}} w_a w_b w_z,   F*_G = max_{w≥0} F_G(w)   (F*_G = 0 with no vertices).

B_r = C_△(16r²) is the constant in display `eq:optimizer-triangle` of the pinned manuscript *A logarithmic
independence bound for clique-free graphs* (below: the source), and C_r = 2 + (3/2)B_r.

**Theorem.** Let r ≥ 3 and let G be a K_r-free graph with n vertices. Then

1. log i(G) ≥ F*_G/(3C_r);
2. log i(G) ≥ (12C_r)^{-1} Σ_v (log(d_v+16))²/(d_v+16);
3. if n ≥ 1 and the average degree is d, then log i(G) ≥ n(log(d+16))²/(12C_r(d+16)), and if d ≥ 2 then
   log i(G) ≥ n(log d)²/(108 C_r d).

## 2. Source inputs (pinned, stipulated true)

All from the source, `build/sections/*.tex`, authenticated against preprints-tree.json by Git blob SHA-1.

- (S1) `lem:optimizer` (optimizer.tex). For every nonempty finite simple graph G, F_G attains its maximum; every
  maximizer w has positive coordinates, satisfies the stationarity equations `eq:stationarity`
  log(1/w_v) = w(N_G(v)), hence 0 < w_v ≤ 1, and for every nonnegative q the divergence identity
  `eq:optimizer-divergence` holds:
  F_G(w) − F_G(q) = Σ_v (q_v log(q_v/w_v) − q_v + w_v) + M_G(q − w), where a term with q_v = 0 equals w_v.
- (S2) `eq:optimizer-triangle` (end of coupling.tex), obtained from `thm:weighted-triangles` and `lem:cross-mass`
  (valid for every integer r ≥ 2): for every maximizer w of F_G on a finite K_r-free graph,
  T_G(w) ≤ B_r M_G(w).
- (S3) `eq:closed-neighborhood-cost` (closure.tex), a consequence of (S1): for a maximizer w and A_v = {v} ∪ N(v),
  F*_G − F_{G−A_v}(w|_{V∖A_v}) = w(A_v) + M_{G[A_v]}(w).
  It is re-derived in Lemma 1 below, so the proof does not depend on the surrounding text of
  `prop:maximum-degree`.

Nothing else from the source is used. In particular the global maximum-degree scale of `prop:maximum-degree` is
not used.

## 3. Deletion costs

**Lemma 1.** Let G be nonempty and let w maximize F_G. For a vertex set A, let q equal w off A and 0 on A. Then

    F_{G−A}(w|_{V∖A}) = F_G(q) = F*_G − w(A) − M_{G[A]}(w).

Consequently F*_{G−A} ≥ F*_G − w(A) − M_{G[A]}(w). For A = {v} this reads F*_{G−v} ≥ F*_G − w_v, and for
A = A_v it reads F*_{G−A_v} ≥ F*_G − c_v with

    c_v := w(A_v) + M_{G[A_v]}(w).

*Proof.* Coordinates equal to zero contribute 0 to the entropy sum and nothing to M, so F_G(q) equals F_{G−A}
evaluated at the restriction of w; this restriction is a nonnegative vector on V∖A, so it is at most F*_{G−A}
(if A = V both sides are 0 and F*_{G−A} = 0 by convention). In (S1) the vertex sum equals Σ_{a∈A} w_a = w(A),
since the terms with q_v = w_v vanish and those with q_v = 0 equal w_v. The vector q − w equals −w on A and 0
elsewhere, so M_G(q − w) = Σ_{ab∈E(G[A])} w_a w_b = M_{G[A]}(w). Hence F*_G − F_G(q) = w(A) + M_{G[A]}(w).
For A = {v} there are no edges inside A (no loops). ∎

## 4. A vertex with self-normalised cost

**Lemma 2.** Let r ≥ 2, let G be a nonempty K_r-free graph and let w maximize F_G. Put
ℓ_v = log(1/w_v) = w(N(v)). Then some vertex v satisfies

    c_v ≤ C_r (1 + ℓ_v).

*Proof.* Write W = Σ_v w_v > 0 and M = M_G(w), T = T_G(w). Since M_{G[A_v]}(w) consists of the edges from v to
N(v), of mass w_v ℓ_v, and the edges inside N(v),

    Σ_v w_v c_v = Σ_v w_v² + Σ_v w_v ℓ_v + Σ_v w_v² ℓ_v + Σ_v w_v M_{G[N(v)]}(w).

Here Σ_v w_v ℓ_v = Σ_v w_v w(N(v)) = 2M. An edge ab lies in G[N(v)] exactly when v is a common neighbour of a
and b, so the last sum is Σ over triangles of three products, namely 3T. Using 0 < w_v ≤ 1 from (S1),
Σ_v w_v² ≤ W and Σ_v w_v² ℓ_v ≤ Σ_v w_v ℓ_v = 2M. With (S2), T ≤ B_r M. Since 2C_r = 4 + 3B_r,

    Σ_v w_v c_v ≤ W + (4 + 3B_r) M = W + 2C_r M ≤ C_r W + C_r Σ_v w_v ℓ_v = Σ_v w_v C_r(1 + ℓ_v),

where C_r ≥ 2 ≥ 1 was used for W ≤ C_r W. Thus Σ_v w_v (c_v − C_r(1 + ℓ_v)) ≤ 0. All w_v are positive, so at least
one bracket is nonpositive. ∎

## 5. The counting induction

**Proposition 3 (part 1).** Let r ≥ 3, c = 1/(3C_r). Every K_r-free graph G satisfies i(G) ≥ exp(c F*_G).

*Proof.* Induction on the number of vertices. With no vertices, i(G) = 1 = exp(0).

Let G be nonempty, w a maximizer of F_G (S1), and v the vertex given by Lemma 2. Independent sets not containing
v are exactly the independent sets of G − v; those containing v are exactly {v} ∪ J with J independent in
G − A_v. Hence

    i(G) = i(G − v) + i(G − A_v).

Both graphs are induced subgraphs of G, hence K_r-free, with fewer vertices. By induction and Lemma 1,

    i(G) ≥ exp(c F*_{G−v}) + exp(c F*_{G−A_v}) ≥ exp(c F*_G) · (e^{−c w_v} + e^{−c c_v}).

It remains to show e^{−c w_v} + e^{−c c_v} ≥ 1. By Lemma 2 and c C_r = 1/3,

    e^{−c c_v} ≥ e^{−c C_r (1 + ℓ_v)} = e^{−1/3} w_v^{1/3} ≥ e^{−1/3} w_v,

because 0 < w_v ≤ 1. As C_r ≥ 2, c ≤ 1/6 < e^{−1/3} (≈ 0.7165), so e^{−c c_v} ≥ c w_v ≥ 1 − e^{−c w_v},
using 1 − e^{−x} ≤ x. This completes the induction. ∎

The constant c depends only on r; the same r is used for every graph in the induction, and no degree parameter
appears.

## 6. Test weights (part 2)

**Lemma 4.** For every graph G and every choice of reals y_v ≥ max(d_v, e),

    F*_G ≥ (1/4) Σ_v (log y_v)² / y_v.

*Proof.* With no vertices both sides are 0. Otherwise put s_v = log y_v ≥ 1 and p_v = s_v / y_v ∈ (0, 1/e].
By 2p_up_v ≤ p_u² + p_v²,

    M_G(p) ≤ (1/2) Σ_v d_v p_v² ≤ (1/2) Σ_v y_v p_v² = (1/2) Σ_v p_v s_v.

Also −log p_v = s_v − log s_v. Hence

    F*_G ≥ F_G(p) ≥ Σ_v p_v (1 + s_v/2 − log s_v) ≥ (1/4) Σ_v p_v s_v,

since 1 + s/4 − log s ≥ 2 − log 4 > 0 for all s > 0 (minimum at s = 4). Finally p_v s_v = (log y_v)²/y_v. ∎

Part 2 follows from Proposition 3 and Lemma 4 with y_v = d_v + 16 (≥ 16 > e):
log i(G) ≥ (1/(3C_r)) · (1/4) Σ_v (log(d_v+16))²/(d_v+16).

## 7. Average degree (part 3)

Let h(x) = (log(x+16))²/(x+16) for x ≥ 0. With y = x + 16 and L = log y,

    h''(x) = (2L² − 6L + 2)/y³,

whose roots in L are (3 ± √5)/2. Since L ≥ log 16 ≈ 2.773 > (3+√5)/2 ≈ 2.618, h is convex on [0, ∞). For n ≥ 1
and average degree d, Jensen's inequality gives Σ_v h(d_v) ≥ n h(d), so part 2 yields the first inequality of
part 3. If d ≥ 2, then log(d+16) ≥ log d > 0 and d + 16 ≤ 9d, so h(d) ≥ (log d)²/(9d), giving
log i(G) ≥ n(log d)²/(108 C_r d). ∎

## 8. Compatibility checks

- (S2) is stated for every maximizer of F_G on every finite K_r-free graph; it is applied only to G itself in
  each induction step, never to modified weights. Lemma 1 compares maxima, so the restricted weights need not be
  maximizers of the smaller graphs.
- (S1) is applied only to nonempty graphs; the empty graph is the base case.
- The recursion uses induced subgraphs only; K_r-freeness is hereditary.
- The theorem uses B_r from the source for r ≥ 3 (the source's `lem:cross-mass` holds for all r ≥ 2). No claim
  about the numerical size of B_r is made.

## 9. Strongest integrated reduction and what is new

- **Routine part.** Part 3 for average degree, up to the constant, follows from the source's `thm:main` and
  Cooper–Dutta–Mubayi, arXiv:1310.6672v1, Theorem 4 and Remark 5 (a hereditary average-degree independence bound
  implies a count bound by uniform sampling). Proposition 3 restricted to bounded maximum degree would also follow
  by replacing the counting recurrence with the source closure.
- **Claimed increment.** Parts 1–2: a lower bound by the mean-field quantity F*_G and hence by the degree
  sequence, with no global degree scale. The source closure (`prop:maximum-degree`) charges every deletion to
  one global log Δ; CDM sampling uses one global density and needs an average-degree independence bound in each
  sample; maximal-subgraph and dyadic degree-class reductions discount lower-degree classes (author calculation in
  working-notes.md). The operation used here is different: the two-branch recurrence
  i(G) = i(G−v) + i(G−A_v) pays the deletion of v alone by w_v, and Lemma 2 chooses v with cost at most a constant
  multiple of 1 + log(1/w_v). The factor w_v^{1/3} on one branch then dominates the loss c·w_v on the other, so
  the induction closes vertex by vertex.
- **Triangle-free comparison.** For r = 3, degree-sequence log Z bounds with sharp constants are in Davies,
  arXiv:2609.04654v1, Theorem 5 (a = 0). No novelty is claimed for r = 3. Davies' Theorem 2 framework needs a
  uniform weighted triangle density over all weights, which K_r-free graphs do not have for r ≥ 4 (complete
  tripartite graphs with uniform weights). Its Theorem 7 needs fractionally r-colourable neighbourhoods.
- **The clique hypothesis is essential to part 1.** For the complete graph K_n, log i(K_n) = log(n+1), while the
  constant test weight (log n)/n gives F*_{K_n} ≥ (1/2 − o(1))(log n)² as n → ∞. So no inequality
  log i(G) ≥ c F*_G holds for all graphs; the input (S2) is where clique exclusion enters.
- **Not obtained.** A degree-sequence bound for α(G) itself; multivariate or fugacity versions; explicit or
  optimal constants. The order (log d)²/d in part 3 cannot be improved for triangle-free graphs of average
  degree d (Buys–van den Heuvel–Kang, arXiv:2503.10002v1, Theorem 1 redux upper bound; Cooper–Mubayi's
  display (2) argument), but the constant 1/(108C_r) is not optimized.

## 10. Validation by the author

The argument was checked line by line. A bounded numerical script (packet/public/sanity.py, one process, 60
random graphs on at most 11 vertices) checks the identities of Lemmas 1, 2 and 4 and the branching inequality at
approximate stationary points with C computed from the observed T/M ratio. It printed
"checked 39 K4-free random graphs: all inequalities hold". This is a test of algebra, not a mathematical gate;
it uses approximate stationary points that need not be global maximizers.
