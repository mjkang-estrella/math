# MathDB 368807: ordinary proof

DRAFT. AI-assisted (Claude Opus 5.5). Zero accepted credit; root alone accepts.

## Statement

Source: E. Vercesi, J. Barta, L. M. Gambardella, S. Gualandi, M. Mastrolilli, *On the integrality Gap of Small Asymmetric Traveling Salesman Problems: A Polyhedral and Computational Approach*, arXiv:2506.10671v1 (12 June 2025).

- K_n = (V, A) is the complete digraph, A = {(i, j) : i ≠ j}, m = n(n − 1), and δ(S) = {(i, j) : i ∈ S, j ∉ S}.
- P^n_ASEP = {x ∈ R^A : (2), (3), (4), x ≥ 0} (formula (6)), where
  - (2) Σ_i x_ij = 1 for every j;
  - (3) Σ_j x_ij = 1 for every i;
  - (4) x(δ(S)) ≥ 1 for every S ⊂ V with 2 ≤ |S| ≤ n − 2.
- A tour is the incidence vector of a directed Hamiltonian cycle.
- Definition 3: N(x) is the set of vertices adjacent to the vertex x.
- Conjecture 1 (p. 14): "For each x vertex, N(x) contains at least one tour."

The quantifier reading is: for every n ≥ 4, every vertex x of P^n_ASEP and some tour T, T ∈ N(x). The source states no n. Any reading whose range of n contains 8 is refuted below.

**Adjacency.** Two distinct vertices x, y of a polytope P are adjacent when the segment [x, y] is a face of P. Equivalently, [x, y] is an extreme subset of P. Equivalently again, the constraints tight at both x and y have rank m − 1. The last form is how the source's proof of Lemma 7 spells adjacency out ("r(n) − 1 linearly independent and tight constraints"). We refute the weakest of these forms: for every tour T, [x*, T] is not even an extreme subset. Exposed faces are extreme subsets, so the exposed-face reading is refuted as well.

## The vertex

Write x* = X/4, where X is the following matrix (rows i, columns j, nodes 0, …, 7):

```
 0 0 1 2 0 1 0 0
 0 0 1 0 0 0 1 2
 0 2 0 0 0 2 0 0
 2 0 0 0 0 0 0 2
 0 1 0 0 0 0 3 0
 0 1 0 0 3 0 0 0
 0 0 0 2 1 1 0 0
 2 0 2 0 0 0 0 0
```

**Lemma 1.** The following hold.

1. x* ∈ P^8_ASEP.
2. Every positive entry of x* is at least 1/4.
3. Every cut S with 2 ≤ |S| ≤ 6 has x*(δ(S)) = 1 or x*(δ(S)) ≥ 5/4.
4. Exactly 8 cuts are tight: {0,3}, {4,6}, {0,3,7}, {4,5,6}, {0,1,2,3,7}, {1,2,4,5,6}, {0,1,2,3,5,7}, {1,2,4,5,6,7}.
5. The 16 degree equations, the 37 equations x_a = 0 on the zero arcs and the 8 tight cut equations together have rank 56 = m. Hence x* is a vertex.

*Proof.* Every row and column of X sums to 4, and X ≥ 0 with a zero diagonal. This gives (2), (3) and nonnegativity.

The values 4·x*(δ(S)) are integers. Checking all 238 cuts with 2 ≤ |S| ≤ 6 gives the minimum 4, attained exactly at the eight listed sets; every other value is at least 5. This is a finite exact verification. It was done by the Lean kernel (`XN_cut`, `XN_tight`), by two earlier independent exact programs, and again by `tools/check_arith.py`.

The rank statement is an exact rational elimination, also in `tools/check_arith.py`. The tight cuts form four complementary pairs (S, V∖S). This is expected, because x(δ(S)) = x(δ(V∖S)) whenever the degree equations hold.

A vertex of a polytope given by linear constraints is exactly a feasible point whose tight constraints have full rank m. So x* is a vertex. The Lean proof (`xs_extreme`) argues directly instead. If x* lies in the open segment between two points y, w of P, then y and w vanish on the 37 zero arcs and are tight on the 8 tight cuts. The resulting linear equations force y = w = x*. ∎

## No tour is adjacent

**Lemma 2 (perturbation).** Let x ∈ P^8_ASEP satisfy (2) and (3) of Lemma 1, i.e. entries in {0} ∪ [1/4, ∞) and cut values in {1} ∪ [5/4, ∞). Let T be a tour, and let v ∈ R^A satisfy all of the following:

- (a) v_a ≠ 0 only on arcs a with x_a > 0 or T_a = 1;
- (b) every row sum and every column sum of v is 0;
- (c) v(δ(S)) = 0 for every cut S that is tight at x and that T crosses exactly once (T(δ(S)) = 1);
- (d) Σ_a |v_a| ≤ 64;
- (e) v is not a multiple of x − T.

Then [x, T] is not an extreme subset of P^8_ASEP. In particular x and T are not adjacent.

*Proof.* Let z = (x + T)/2 and ε = 1/512. We show that z ± εv lies in P^8_ASEP.

First, every constraint not tight at z has slack at least 1/8 at z:

- *Arcs.* z_a = 0 only if x_a = T_a = 0. Otherwise z_a ≥ min(1/4, 1)/2 = 1/8.
- *Cuts.* T is 0/1-valued, and T(δ(S)) is the number of tour arcs leaving S, which is an integer ≥ 1. So z(δ(S)) = 1 exactly when x(δ(S)) = T(δ(S)) = 1. Otherwise z(δ(S)) ≥ min((5/4 + 1)/2, (1 + 2)/2) = 9/8.

Second, by (d), |ε·v(B)| ≤ 64/512 = 1/8 for every set B of arcs. So no slack constraint becomes violated.

Third, the tight constraints are preserved:

- the degree equations, by (b);
- arcs with z_a = 0, by (a);
- cuts with z(δ(S)) = 1, by (c).

Hence z ± εv ∈ P^8_ASEP.

Now suppose [x, T] were an extreme subset F. Then z ∈ F lies in the open segment between z − εv and z + εv, both in P. So both points lie in F ⊆ x + R(x − T), and v would be parallel to x − T. That contradicts (e). ∎

**Theorem.** x* is a fractional vertex of P^8_ASEP, and no tour is adjacent to x*. Hence Conjecture 1 is false.

*Proof.* Lemma 1 gives the vertex property and the hypotheses of Lemma 2. It is fractional, for example x*_{02} = 1/4.

Every tour on {0, …, 7} is the cyclic order 0 → p1 → … → p7 → 0 for exactly one permutation (p1, …, p7) of {1, …, 7}, so there are 7! = 5040 tours. For each one, the dossier stores an integer vector v satisfying (a)–(e). Condition (e) is witnessed by two arcs a, b with (x − T)_a·v_b ≠ (x − T)_b·v_a.

These 5040 finite checks were performed by the Lean kernel (`decide`, in 48 chunks, for a checker `chk` proved sound in `ASEPBridge`). They were repeated independently in `tools/check_arith.py`, which recomputes the tight cuts from scratch rather than reading the stored list. The largest Σ|v| that occurs is 34.

Lemma 2 then shows that no [x*, T] is a face, so x* has no tour in N(x*). This makes n = 8 a counterexample to Conjecture 1. ∎

**Example certificate.** For the tour 0 → 1 → 2 → … → 7 → 0, take v = e_{01} − e_{03} − e_{21} + e_{23}.

- Support: arcs (0,1) and (2,3) are tour arcs, and x*_{03} = x*_{21} = 1/2.
- Rows 0 and 2 and columns 1 and 3 each sum to 0.
- The cut condition (c) holds; the checker verifies it.
- For the witness arcs a = (0,1) and b = (0,2): (x* − T)_a·v_b − (x* − T)_b·v_a = (−1)·0 − (1/4)·1 = −1/4 ≠ 0.

## Diagnostics (not part of the proof)

- *Rank histogram.* For every tour, the constraints tight at both x* and T have exact rank at most 54 < 55 = m − 1. The histogram of these ranks over the 5040 tours is {44: 213, 45: 590, 46: 913, 47: 958, 48: 846, 49: 626, 50: 430, 51: 232, 52: 123, 53: 82, 54: 27}.
  - It was computed by the author lane in two implementations (Python and a separate Node BigInt program), and independently by the reviewer lane.
  - It was not recomputed in this lane.
- *n = 4 control.* The source's Example 1 vertex is adjacent to exactly 5 of the 6 tours. The common tight rank is 11 for five tours and 7 for 0 → 2 → 1 → 3 → 0. This was recomputed in `tools/check_arith.py`.

## Scope and limits

- n = 4 and n = 5 satisfy the conjecture. This rests on the source's exhaustive data together with the reviewer's recomputation.
- n = 6 and n = 7 are open. The author lane's search at n = 7 (eight annealing walks) reached at best 1 adjacent tour, and was not exhaustive.
- By Lemma 7 of the source, the whole orbit of x* under relabelling is non-adjacent to every tour.
- The vertex graph of P^8_ASEP is connected anyway. What fails is only the one-step strategy of reaching every orbit from a tour's neighbourhood, which the source proposed as the motivation for Conjecture 1.
