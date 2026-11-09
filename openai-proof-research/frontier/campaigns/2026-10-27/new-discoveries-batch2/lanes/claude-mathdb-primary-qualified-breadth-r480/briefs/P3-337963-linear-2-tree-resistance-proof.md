# P3 — MathDB 337963: proof of Conjecture 49 of arXiv:1712.05883v1 (Barrett–Evans–Francis)

Screening-stage brief. No credit. Needs independent hypothesis review, a definition/scope check, a registry/prior check and formalization.

## Source and literal quantifiers
- Source: arXiv:1712.05883v1, retained. Conjecture 49 (line ~1419): "Let G be a linear 2-tree. If the diameter of the 2-tree tends to infinity, the maximal resistance distance of the linear 2-tree is also unbounded." Unit edge resistances are used throughout the source.
- Precise reading: for every M there is D_0 such that every linear 2-tree with diam ≥ D_0 has max_{x,y} r(x,y) ≥ M. The proof gives the explicit bound max r ≥ (diam − 2)/6.
- **Scope note.** The source defines only *straight* linear 2-trees (Definition 1). It uses "linear 2-tree" and "bent linear 2-tree" without a formal definition. We use the standard definition: a 2-tree with exactly two vertices of degree 2. Equivalently, the triangles can be ordered so that consecutive triangles share an edge and the shared edges are distinct; this is the sequential construction below. That this definition is the source's intended one is an assumption a reviewer must confirm.

## Construction (normal form)
- Start with the triangle t_1 = {a,b,c}, with e_1 = {b,c}.
- For j = 2..m, add a new vertex w_j adjacent to both ends of e_{j−1}, forming t_j = e_{j−1} ∪ {w_j}.
- For j < m, choose e_j = {w_j, κ_j} with κ_j ∈ e_{j−1}.
- The degree-2 vertices are u = a and v = w_m.

(Equivalence lemma, to be supplied in review: in a 2-tree with exactly two degree-2 vertices, the triangle/shared-edge incidence tree is a path, which gives this normal form.)

A **switch** at j (3 ≤ j ≤ m−1) means κ_j ≠ κ_{j−1}, i.e. κ_j = w_{j−1}. Let s be the number of switches.

## Lemma A (diameter): diam(G) ≤ s + 2
- Every triangle contains a hub: t_1 and t_2 contain κ_2, and t_j contains κ_{j−1} for j ≥ 3 (since κ_{j−1} ∈ e_{j−1} ⊂ t_j).
- Consecutive hubs are equal or adjacent: if κ_j ≠ κ_{j−1}, then κ_j = w_{j−1} and e_{j−1} = {w_{j−1}, κ_{j−1}} is an edge.
- So the distinct hubs form a walk with s steps, and every vertex is within distance 1 of some hub (triangles are cliques).

## Lemma B (3-edge cuts)
Let j be a switch, with h := κ_{j−1} (dropped at j) and x the other vertex of e_{j−2}. Here e_1 = {b,c} when j = 3, and in general e_{j−2} = {h, x}. Then t_{j−1} = {h, x, w_{j−1}} and t_j = {h, w_{j−1}, w_j}.

Let R = {w_{j−1}, w_j, ..., w_m} and L = V \ R.
- Every edge lies in a triangle.
- For i ≤ j−2, t_i ⊂ L.
- For i ≥ j+1, t_i ⊂ R, because e_j = {w_j, w_{j−1}} and later shared edges contain only kept or new vertices.
- So the only L–R edges are those inside t_{j−1} and t_j: C_j = {x w_{j−1}, h w_{j−1}, h w_j}.

Since u ∈ L and v ∈ R, C_j is an edge cut of size 3 separating u from v.

## Lemma C (disjointness)
C_j ⊂ E(t_{j−1} ∪ t_j). For switches j' ≥ j+2, every edge of C_{j'} contains w_{j'−1} or w_{j'}, and these are born after step j. So the cuts are disjoint. Taking every other switch gives ⌈s/2⌉ pairwise disjoint 3-edge cuts.

## Theorem
By the Nash-Williams inequality, r(u,v) ≥ Σ_k 1/|C_{j_k}| = ⌈s/2⌉/3 ≥ s/6. With Lemma A:

  max r ≥ r(u,v) ≥ (diam(G) − 2)/6 → ∞.

This proves Conjecture 49. ∎ (A path-length/diameter growth with bounded resistance is impossible.)

## Decisive check (run)
`scripts/l2t_check.py` checks Lemma B (cut separation), Lemma A, and the exact rational bound r(u,v) ≥ ⌈s/2⌉/3.
- All 8,190 linear 2-trees with m ≤ 14 cells (exhaustive over keep choices): 0 failures.
- 300 random instances with m ∈ [10,34]: 0 failures.

Runs: `runs/l2t_check.exh14.r1.txt`, `runs/l2t_check.rand300.r1.txt`. This is numerical sanity only, not proof.

## Certificate / formal dependencies
- Nash-Williams inequality (in Mathlib? likely not; needs electrical-network formalization).
- The normal-form lemma for linear 2-trees.
- An elementary BFS/diameter argument.
- An alternative route avoiding Nash-Williams is the Dirichlet principle r(u,v) = sup_f (f(u)−f(v))²/Σ(f(x)−f(y))², taking f = cut index.

## Objections / limits
- Prior/novelty: HOLD.
  - Later papers by Barrett, Evans, Francis and coauthors on bent linear 2-trees / 2-forests may contain this or stronger results. This was not checked: no registry or successor route was used.
- Definition scope: see the scope note above.
- Routine-adaptation objection: Nash-Williams is a classical tool, but it does not directly yield the statement. The structural cuts at hub switches are the content. A reviewer must judge whether the result is routine.
