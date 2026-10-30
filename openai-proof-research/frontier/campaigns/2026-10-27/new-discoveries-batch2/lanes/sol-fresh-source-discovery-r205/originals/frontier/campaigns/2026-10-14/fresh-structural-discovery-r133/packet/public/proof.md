# r133 author proof: odd-cycle completeness for the 106 reduction, and the Brakensiek-Guruswami conjecture

Author: Factory Droid / claude-opus-5-5 / high. Written after the freeze recorded in
`frozen-statement.md` (SHA256 72654d283495baa80aba6349b1b5ebb9a4634ba268d7499a6187ecdd1e311256).
This is an author proof only. It assigns no correctness, contribution, acceptance or count verdict.

Source S = pinned preprint
`preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/build/source/`
(main.tex and sections/*.tex; Git blob and SHA256 receipts in `packet/private/source/receipts.json`).
Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true, including its operative proof
operations. Labels below are the LaTeX labels of S.

## 0. Statements (verbatim scope of the freeze)

Graphs are finite, simple, undirected, loopless. `C_N` is the cycle on `Z_N` (`i ~ i +- 1`).

**Theorem A.** For every fixed integer k >= 1 and fixed real delta > 0 there is a deterministic
polynomial-time algorithm R_{k,delta} mapping each explicitly encoded 3-CNF formula phi to a
nonempty finite simple graph G_phi with: phi satisfiable => G_phi -> C_{2k+1}; phi unsatisfiable =>
alpha(G_phi) < delta |V(G_phi)|. Constants and degree may depend on (k, delta), not on phi.

**Corollary B.** If H, G are finite loopless graphs, H non-bipartite and H -> G, then the decision
problem PCSP(H, G) (distinguish X -> H from X -/-> G) is NP-hard, and the search problem is NP-hard
under polynomial-time Turing reductions. Moreover, for every fixed delta > 0 it is NP-hard to
distinguish X -> H from alpha(X) < delta |V(X)|.

Fix k >= 1 and write

    N = 2k + 1,     rho = 1/(2N) = 1/(4k+2),     L_k = 2/rho = 8k + 4.

## 1. The modified construction R_{k,delta}

It suffices to treat rational 0 < delta <= 1/4: for real delta > 0 pick a rational
0 < delta_0 <= min(delta, 1/4) and use R_{k,delta_0}; the soundness conclusion only weakens.

R_{k,delta} is the construction of S, Section `sec:construction`, with all its finite inputs
(r, s, m, P even, D = mP, lambda, mu, q > 1/delta, sigma and the Label Cover reduction of
`thm:label-cover`), its preprocessing, its vertex experiment (`eq:location`) and multiplicity
expansion, with exactly two changes:

    (clique test)  if some x in X satisfies dist(x, Tx) <= rho, output K_q;          [replaces eq:clique-test]
    (edge rule)    distinct vertices with locations x, y are adjacent iff dist(x, Ty) <= rho.   [replaces eq:edge]

and with the constants chosen in Section 4 below from L = L_k instead of L = 64.

Symmetry of the edge rule is as in S: T is an involutive isometry of dist, so
dist(x, Ty) = dist(Tx, y) = dist(y, Tx).

**Encoding (`prop:encoding`).** The proof of `prop:encoding` is unchanged except for the
comparison step: every finite distance is an integer multiple of 1/D, so `dist <= 1/(4k+2)` is
decided exactly by comparing the integer D(4k+2)·dist with D. All other parts (polynomially many
tuples with constant-size grids, integer shortest paths, common denominator C_0, exact multiplicity
expansion, polynomial Label Cover reduction for fixed sigma, constant-size outputs of the trivial
branches) do not involve the threshold. Hence R_{k,delta} is deterministic polynomial time and
outputs a nonempty finite simple unweighted graph.

## 2. Completeness: satisfiable => G_phi -> C_N

Trivial branch: a formula with no remaining clause gives a one-vertex graph, which maps to C_N.

Otherwise the Label Cover instance has value 1 (`thm:label-cover`). Exactly as in the proof of
`lem:completeness`, fix a labelling satisfying every occurrence, evaluate each grid point at its
tuple's product answer, and obtain phi: X -> T = R/Z that is nonexpanding for dist (nonexpanding in
each copy for the sup circle metric; equal across every zero link because the labelling satisfies
that occurrence) and satisfies phi(Tx) = phi(x) + 1/2. These facts use no threshold.

(a) Clique branch does not occur: d_T(phi(x), phi(Tx)) = 1/2, so dist(x, Tx) >= 1/2 > rho.

(b) For a in T let c(a) in Z_N be the unique j (mod N) with a in [j/N, (j+1)/N) modulo 1.

*Claim.* If d_T(b, a + 1/2) <= rho then c(b) - c(a) is congruent to k or k+1 modulo N.

*Proof.* Take the lift a' of a in [i/N, (i+1)/N), where i represents c(a). Since
1/2 = k/N + 1/(2N) and rho = 1/(2N), there is a lift b' of b with
|b' - a' - k/N - 1/(2N)| <= 1/(2N), so a' + k/N <= b' <= a' + (k+1)/N. Hence
(i+k)/N <= b' < (i+1)/N + (k+1)/N = (i+k+2)/N, i.e. floor(N b') is i+k or i+k+1. As
c(b) = floor(N b') mod N, the claim follows. ∎

(c) Colour a vertex with location x by psi(x) = -2 c(phi(x)) in Z_N. If vertices with locations
x, y are adjacent, then dist(x, Ty) <= rho, so d_T(phi(x), phi(y) + 1/2) <= rho because phi is
nonexpanding and phi(Ty) = phi(y) + 1/2. By the Claim (a = phi(y), b = phi(x)),
c(phi(x)) - c(phi(y)) is k or k+1 = -k mod N. Since -2k = 1 - N is congruent to 1 mod N,
psi(x) - psi(y) is congruent to 1 or -1. Thus psi is a homomorphism G_phi -> C_N.
(Vertices sharing a location are non-adjacent since the clique branch did not occur; they receive
the same value, which is irrelevant for a homomorphism.) ∎

For k = 1 this is the three-arc colouring of `lem:completeness` with threshold 1/6 instead of 1/8.

## 3. The soundness interface with threshold rho

Assume phi unsatisfiable, so the Label Cover value is at most sigma. The empty-clause branch and
the clique branch output K_q, whose independence ratio is 1/q < delta. Otherwise fix a nonempty
independent set **A** of the output graph and let A be its set of locations.

(S1) **Separation** (replaces `eq:independent-separation`): dist(A, TA) > rho. For locations of
distinct selected vertices, by the missing edge; for a location compared with itself, by failure of
the clique test; finitely many strict inequalities (including infinite distances).

(S2) **Bumps** (replaces `eq:bumps`): with bump(u) = (1 - u/rho)_+ and bump(infinity) = 0, set

    f(x) = bump(dist(x, A)) - bump(dist(Tx, A)).

Properties, each checked directly:
- f takes values in [-1, 1] (each bump lies in [0,1]);
- f(Tx) = -f(x) since T^2 = id;
- f = 1 on A: the first bump is 1; dist(Tx, A) = dist(x, TA) >= dist(A, TA) > rho by (S1) and
  isometry, so the second bump is 0;
- f is constant across every zero link: x -> dist(x, A) is 1-Lipschitz for the pseudometric dist
  (triangle inequality), and so is x -> dist(Tx, A) because T is a dist-isometry; zero links have
  dist 0;
- f is L_k-Lipschitz within each grid copy for the sup circle metric d_infinity: within a copy,
  dist(x, y) <= d_infinity(x, y) (the direct link); within a copy all points have dist < infinity
  to each other, so either both distances to A are finite or both bumps vanish; each bump is
  (1/rho)-Lipschitz in its argument; hence |f(x) - f(y)| <= (2/rho) d_infinity(x, y) = L_k d_infinity(x, y).

These are exactly the properties of f stated and used in S, Section `sec:lists` (paragraph after
`eq:bumps`), with 64 replaced by L_k. Nothing else about the threshold is used afterwards. The
following table records each later step and the property it consumes.

| S step | consumes | dependence on threshold |
|---|---|---|
| McShane extension g_q, clipping, F_q (lists.tex 42-61) | f L-Lipschitz on each grid copy; f in [-1,1]; T isometry of d_infinity | via L only |
| `eq:compatibility` | f constant across zero links; F_q = f on grid; F_q L-Lipschitz | 2L/D |
| `eq:subchain-functions`, `lem:subchain-lists` | F_b L-Lipschitz, values in [-1,1]; `thm:junta` for sL | J(sL, gamma) |
| `lem:separated-lists` | locality of the list rule; Label Cover value <= sigma | none |
| `lem:alignment` (proof in `sec:alignment-proof`), `lem:good-pairs` | finite combinatorics of lists | none |
| `prop:aligned-bound` | F_b odd (`coeff:mean-zero`), L-Lipschitz (`coeff:one-step`, `coeff:grid-error`), [-1,1]; `lem:influences` for (L, eps); F_b = f on grid and f = 1 on A | via L only |
| proof of `thm:main` (parameters.tex 49-87) | the above; q > 1/delta; 8 eps < delta | none beyond L |

`thm:junta` and `lem:influences` are stated in S for every finite L >= 0, so they apply to L_k
and to s L_k. I re-read the proofs of `lem:subchain-lists`, `lem:separated-lists`,
`lem:good-pairs` and `prop:aligned-bound` line by line (lists.tex 1-224, alignment.tex 1-80,
coefficient.tex 1-287) and found no use of the numerical values 1/8, 1/32 or 64 other than through
the symbol L and the properties in (S2). `alignment-proof.tex` does not mention the graph.

## 4. Constants (S, parameters.tex lines 10-37, with L = L_k)

Fix rational 0 < delta <= 1/4 and rational 0 < eps < delta/8. Set L = L_k = 8k + 4 and take
beta, K from `lem:influences` for (L, eps). Choose a positive integer m with L/m < beta/2, then
rational 0 < lambda < 1 with lambda K < eps; choose s >= 2 with (1 - p_m)^s < eps; then gamma > 0 with
s(2 gamma)^2/beta^2 < eps; then even P with 2L/D < gamma and 2Ls/P < eps (D = mP). This is
`eq:parameter-bounds` for L_k. Put d = max{1, J(sL, gamma)(m+1)^s} (`eq:list-size`). Apply
`lem:alignment` to (s, d, eta = eps) to get r >= s and mu. Choose rational sigma in (0,1) with
4^r d^2 sigma < eps (`eq:source-soundness`) and only then invoke `thm:label-cover` for sigma.
Choose an integer q > 1/delta. All are fixed finite data depending only on (k, delta).

## 5. Proof of Theorem A

Completeness is Section 2. For soundness, in the non-trivial non-clique branch let **A** be any
nonempty independent set. By `lem:good-pairs` and `eq:source-soundness`, an unaligned chain/B pair
has probability at most 4^r d^2 sigma + eps < 2 eps. At an aligned pair, `prop:aligned-bound`
(whose hypotheses are the properties of Section 3 and `eq:parameter-bounds` for L_k) bounds the
conditional probability of sampling a vertex of **A** by 6 eps. The multiplicity expansion makes the
sampling law uniform on vertices (`prop:encoding`). Hence |**A**|/|V| <= 8 eps < delta. The empty set
satisfies the bound since the graph is nonempty. The K_q branches have ratio 1/q < delta.
So alpha(G_phi) < delta |V(G_phi)|. Polynomial time is Section 1. ∎

## 6. Proof of Corollary B

Let H, G be loopless, H non-bipartite, H -> G. A shortest odd closed walk in H is a cycle, so H
contains a cycle of some odd length 2k+1 >= 3 as a subgraph and C_{2k+1} -> H by inclusion. Let
c = |V(G)| (c >= 3 because G is non-bipartite, as H -> G). Apply Theorem A with (k, delta = 1/c).

- phi satisfiable: G_phi -> C_{2k+1} -> H.
- phi unsatisfiable: suppose g: G_phi -> G. Each fibre g^{-1}(v) is independent, because an edge
  uw of G_phi maps to an edge g(u)g(w) of the loopless G, so g(u) != g(w). The c fibres cover
  V(G_phi), so one has size >= |V(G_phi)|/c = delta |V(G_phi)| > alpha(G_phi), a contradiction.

Thus R_{k,1/c} is a polynomial-time many-one reduction from 3SAT to the promise problem PCSP(H, G),
which is therefore NP-hard. For search: given a polynomial-time algorithm for search, run it on X
for its time bound and accept iff it returns a valid homomorphism X -> G (checkable in polynomial
time); this accepts every X -> H and rejects every X -/-> G. The density form uses
R_{k,delta} directly with C_{2k+1} -> H. ∎

This is KOWZ Conjecture 1.2 (Brakensiek-Guruswami), arXiv 2003.11351v3, text lines 281-284, in
exactly their formulation (non-bipartite loopless H, G with H -> G), under the pin stipulation.

## 7. Strongest integrated reduction and what is used

- S `thm:main` as a black box gives K_3-colourable vs alpha < delta n. With the sandwich
  (K_3 -> H, G -> K_c) it yields Corollary B only when H contains a triangle.
- KOWZ Thm 1.3/1.4: G = K_3 (more generally G with a Z_2-map |Hom(K_2, G)| -> S^1);
  Avvakumov et al. (arXiv 2504.07592, abstract read): 4-colourable G. With the sandwich these
  cover chi(G) <= 4. Left open by these: odd girth(H) >= 5 together with chi(G) >= 5.
- Black-box functor reductions do not close the gap from S: Lambda_k/Gamma_k (KOWZ Example 1.1)
  turns PCSP(K_3, Gamma_k K_c) into PCSP(C_{3k}, K_c), but Gamma_k K_c (k >= 3 odd, c >= 3) has
  loops, so the source problem is trivial; KOWZ (lines 1581-1583) state that iterating their delta
  reduction cannot derive PCSP(C_5, K_c) from PCSP(K_3, K_c) for all c.
- Operation used here: open the proof of S; shrink the half-shift threshold to 1/(4k+2) so that
  satisfying phase evaluations separate adjacent vertices by circle distance at least 1/2 - rho,
  which admits a (2k+1)-arc odd-cycle colouring, and verify that the soundness half of S is
  threshold-uniform (only L = 2/rho changes, and every constant is chosen after L).

## 8. Limitations and novelty scope

- Dependence: the proof relies on S's `thm:label-cover`, `thm:junta`, `lem:influences`,
  `lem:subchain-lists`, `lem:separated-lists`, `lem:alignment`, `lem:good-pairs`,
  `prop:aligned-bound` and the parameter order, all stipulated true under the pin. Their proofs were
  re-read to confirm that they consume only the Section 3 properties and the symbol L.
- Mechanically the change is a constant change inside the source construction plus a different
  completeness colouring. Whether this is a substantial contribution or TECHNICAL is for the
  separate contribution review; I make no verdict.
- The constants (and the polynomial degree) depend on k and delta; no uniformity in k is claimed.
- Novelty: new to this project (history search in working-notes Step 5). Literature: arXiv
  2605.09815v2 (18 Oct 2026) describes the Brakensiek-Guruswami conjecture as following from the
  Rich 2-to-1 Conjecture and approximate graph homomorphism as unclassified. FMW's supplementary
  material (their Remark 1.13) was not found and is unread; the S authors or others may have
  observed the same modification. No worldwide-priority claim.
- No formalization, manuscript or release work was done (outside this round's scope).
