# r245 discovery notes: sustained mathematics

Counts unchanged: 9 additional / 39 total / next 40. Root alone accepts. No Lean, no manuscript.

## 1. Strongest fresh mechanism: refutation of Das, Conjecture 5.1 (LAA 653 (2022))

### Source (frozen, read in full around the statement)

S. Das, *Sign patterns that allow algebraic positivity*, arXiv:2112.00442v3 (22 Mar 2022),
journal-ref Linear Algebra Appl. 653 (2022) 151–182. Frozen bytes
`frozen/2112.00442v3.pdf` sha256 `c7ebbffde1cd95c6cf363b9627d3dbd2311d066d0156fffd5a68e6df21198379`.

Definitions (text lines 1041–1057 of the extraction): for a sign pattern A,
`A+` keeps the `+` entries, `A−` keeps the `−` entries, `B_A = A+ − (A−)^T`.
"We say that an irreducible sign pattern matrix A is AP-irreducible if every row and column of A
contains a + and B_A is irreducible. We say that a sign pattern matrix A is minimally
AP-irreducible if it does not remain AP-irreducible after replacement of a nonzero entry with 0."

Conjecture 5.1 (lines 1935–1936): "If A is a minimally AP-irreducible sign pattern matrix of order n
with all diagonal entries equal to 0, then A has at most 2n − 2 nonzero entries."

The paper proves it (Lemma 3.10) only under the extra hypothesis that `A[α,β]` contains no `+`
for distinct irreducible components α, β of `A+`. The conclusion says both conjectures "are valid
for all known algebraically positive matrices".

Graph translation used throughout. Write P = set of cells with `+`, M = cells with `−`
(zero diagonal). D(A) has arc i→j for every nonzero a_ij. D(B_A) has arc i→j iff a_ij = `+`
or a_ji = `−`. Irreducible = digraph strongly connected (n ≥ 2). So A is AP-irreducible iff

* (C1) every row and every column contains a `+`;
* (C2) D(A) = P ∪ M is strongly connected;
* (C3) D(B_A) = P ∪ M^rev is strongly connected.

### Theorem 1 (counterexample family)

For every n ≥ 4 there is a zero-diagonal n×n sign pattern F_n that is minimally AP-irreducible
and has exactly 4n − 10 nonzero entries. Since 4n − 10 > 2n − 2 for n ≥ 5, Conjecture 5.1 fails
for every order n ≥ 5.

Construction. Vertices x, x′, y, y′, s_1, …, s_m with m = n − 4 ≥ 0. Put
p_0 = y′, p_1 = s_m, p_2 = s_{m−1}, …, p_m = s_1, p_{m+1} = x′.

* `+` entries (2m + 4): (x,x′), (x′,x), (y,y′), (y′,y), and (x,s_i), (s_i,y) for 1 ≤ i ≤ m.
* `−` entries (2m + 2): (p_t, p_{t+1}) and (p_{t+1}, p_t) for 0 ≤ t ≤ m.

The `−` pairs join consecutive path vertices, none of which is x or y, and the path never joins
x′ to y′ directly when m ≥ 1 (for m = 0 the only `−` pair is {x′, y′}, which carries no `+`).
So no cell gets two signs, the diagonal is zero, and the count is (2m+4) + (2m+2) = 4m + 6 = 4n − 10.

For n = 5 (order x, x′, y, y′, s_1), F_5 is

```
0+00+
+000-
000+0
00+0-
0-+-0
```

Proof.

*(C1)* Rows: x→x′, x′→x, y→y′, y′→y, s_i→y. Columns: x′←x, x←x′, y′←y, y←y′, s_i←x.

*(C2), (C3)* M is closed under reversal as a set of ordered pairs, so P ∪ M^rev = P ∪ M. Hence
D(A) and D(B_A) have the same arc set, call it D. D contains the bidirected path
x ↔ x′ ↔ s_1 ↔ … ↔ s_m ↔ y′ ↔ y through all n vertices, so it is strongly connected.
In D(A) arc p_t→p_{t+1} comes from entry (p_t,p_{t+1}). In D(B_A) the same arc comes from
entry (p_{t+1},p_t), the reversed `−` entry. Neither cell carries a `+`.

*Minimality.*

(a) Each `+` entry is the only `+` in its row or column:
* column x′ for (x,x′);
* row x′ for (x′,x);
* row y for (y,y′);
* row y′ for (y′,y);
* column s_i for (x,s_i);
* row s_i for (s_i,y).

Every other nonzero in those lines is a `−` from the path. So deleting a `+` violates (C1).

(b) Fix 0 ≤ t ≤ m and let U_t = {y, p_0, …, p_t}. Then x, x′ ∉ U_t, so U_t is a nonempty proper
subset. Walk through every arc of D leaving a vertex of U_t:
* y→y′ stays inside U_t;
* y′→y stays inside;
* s_i→y stays inside;
* p_j→p_{j−1} stays inside;
* p_j→p_{j+1} stays inside for j < t.

So the **only** arc of D leaving U_t is p_t→p_{t+1}.
* Deleting entry (p_t,p_{t+1}) removes that arc from D(A), and nothing else produces it there, so (C2) fails.
* Deleting entry (p_{t+1},p_t) removes that arc from D(B_A). No `+` sits at (p_t,p_{t+1}), so nothing else produces it, and (C3) fails.

Hence every nonzero entry is essential. ∎

Consistency with the source: F_n has `+` entries x→s_i between distinct irreducible components
{x,x′} and {s_i} of A+. So F_n lies outside Lemma 3.10's hypothesis and contradicts no proved
statement of the source.

### Second route (independent finite verification + exact small optimum)

* `diagnostics/apfamily.py verify 30` builds F_n for n = 4..30 and checks (C1)–(C3) and minimality
  by brute force (delete every nonzero, recheck). PASS for all, with exactly 4n−10 nonzeros. This is
  an independent mechanical check of Theorem 1 for those orders, not a substitute for the proof.
* Exhaustive enumeration over all 3^12 zero-diagonal 4×4 patterns (`apirr.py exhaustive 4`):
  the maximum is 6 = 2n−2. So the conjecture is true at n ≤ 4, and n = 5 is the first failure.
* Exact MILP (`apmilp.py`, HiGHS through SciPy, single thread, C locale under the unchanged caps):
  f(3) = 4, f(4) = 6, f(5) = 10, all with gap 0, and the optima re-verified by brute force.
  * The model has one variable per sign/cell, the (C1)–(C3) cut constraints, and an explicit
    witness for each kept entry: a row/column-uniqueness indicator, or a cut U where the entry's
    arc is the only one leaving U, in D(A) or in D(B_A).
  * So F_5 is extremal at n = 5. This is solver evidence, not a proof of optimality.
* Unseeded local search for n = 5..10 reached 10, 14, 16, 18, 20, 22. Search seeded at F_n for
  n = 6..9 (two seeds each, 40000 moves) never exceeded 4n−10. This is weak evidence only.

### Proposition 2 (linear upper bound, proved)

Every minimally AP-irreducible zero-diagonal n×n pattern has at most 6n − 6 nonzero entries.

Proof. Let Q be the `+` entries that are unique `+` in their row or in their column. In the bipartite
graph rows ∪ columns, every edge of Q has an endpoint of degree 1, so Q is a disjoint union of stars.
Because of the zero diagonal, a star covers at most n of the 2n vertices. Hence
|Q| ≤ (covered vertices) − (number of stars) ≤ 2n − 2.

Every other entry is essential for (C2) or (C3). Its arc in D(A), respectively D(B_A), is then a
strong bridge. In D(B_A), the entries (i,j)=`−` and (j,i)=`+` give the same arc, but if both are
present neither is essential there, so the map from entries to bridges is injective.

A strongly connected digraph has at most 2n−2 strong bridges. Fix a root r, an out-arborescence T1
and an in-arborescence T2. T1 ∪ T2 is strongly connected, so every bridge lies in T1 ∪ T2.
The total is therefore ≤ 3(2n−2). ∎

### Exact remaining gaps

* The extremal value f(n) is **not** determined for n ≥ 6. Known: 4n−10 ≤ f(n) ≤ 6n−6 (n ≥ 4).
  * Conjecture (ours, unproved): f(n) = 4n − 10 for n ≥ 4.
  * The n = 6 exact MILP FAILED: HiGHS std::bad_alloc after 157 s (sampled peak RSS 321 MB)
    under the fixed 512 MiB AS cap, see `diagnostics/runs/milp6.err`. Only f(6) ∈ [14, 30] is
    established.
* Das's Conjecture 5.2 (allow-AP iff AP-irreducible) is untouched. We did not decide whether F_n
  allows algebraic positivity. If some F_n were shown not to allow AP, that would also refute 5.2;
  this is the most valuable follow-up calculation.
* Journal body (ScienceDirect) not read (denied route). The ISI repository abstract of the published
  article still says "We also propose two conjectures", so the conjecture section appears to
  survive in print. Wording changes in the journal text cannot be excluded.

## 2. Candidate A (second survivor): integral transposition Cayley graphs vs cographs

Source: Abdollahi–Arezoomand–Ebrahimi, arXiv:2305.00279v1 (29 Apr 2023), Conjecture 1:
"Cay(S_n,T) is integral, if and only if for some positive integer k, the graph G_T is a generalized
complete multipartite graph of type k."

Reading. Allow empty weak-join factors, which is needed for the paper's own Proposition 2: disjoint
unions of complete multipartite graphs are integral, yet 2K_2 is not a join. Then the class is closed
under disjoint union and join and is generated from K_1. It is exactly the class of **cographs**
(P4-free graphs). The literal strict reading (non-null factors) is refuted by 2K_2 ⊂ S_4
(Cay = disjoint 4-cycles). That is only a wording defect and is not counted.

Computation (`diagnostics/intcay.py`, `firstfail.py`, `special9.py`). Exhaustive over all graphs with
n ≤ 9 vertices, up to isomorphism:
* graph counts per level match the known totals: 1044 at n = 7, 12346 at n = 8, 274668 at n = 9
  (complements via M_{G^c} = M_{K_n} − M_G);
* Laplacian-integral non-cographs: 4, 8, 31 and 189 at n = 6, 7, 8, 9;
* none gives an integral Cayley graph.

Spectra were computed in every irreducible representation via Young's orthogonal form, with
tolerance 1e-6. This is a floating-point screen, not a certificate.

Structure found. In 188/189 cases at n = 9 (and in all cases at n ≤ 8) the first failing irrep is
(n−2,2), i.e. the 2-token graph Laplacian is non-integral. The single exception is the rook's graph
K_3□K_3 (Paley(9), Laplacian spectrum 0,3⁴,6⁴): blocks (8,1), (7,2), (7,1,1) are integral and
(6,3) is not.
* Necessary-condition mechanism (proved, elementary): Σ_{e∈E}τ_e acts on the k-subset permutation
  module as |E|·I − L(F_k(G)), where F_k is the k-token graph. So integrality forces every token
  graph to be Laplacian integral.
* Gap: the converse (P4 ⇒ some non-integral eigenvalue) is a global integrality question with no
  local mechanism found. Not proved.

## 3. Failures preserved

* HiGHS initially aborted ("terminate called", then std::bad_alloc). Cause: the bare Python
  VmSize was 243 MB due to the locale archive mapping, and multithreading pushed it over the
  512 MiB AS cap. Fixed with LC_ALL=C, MALLOC_ARENA_MAX=1, threads=1 and taskset; caps unchanged.
* The n=9 graph merge hit MemoryError under the cap; replaced by streaming level files.
* Several unguarded trivial python3 invocations occurred (import checks, one heredoc edit, one no-op).
  They are logged in `administrative/deviations.log`; none touched scientific sources.
