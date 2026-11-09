# r112 attempts (details beyond results.json)

## 374241 (candidate)
See PROOF-374241.md and formal/. SAT diagnostics: logs/mindeg-b4.log, mindeg-b5.log, mindeg-b6.log (maximum minimum degree without a clockwise b-path equals n - ceil(n/(b-2)) for b = 4, 5, 6 and n <= 13).

## 374236 (parked)
* The single-cut lemma is false. The lemma said some cut makes all linear blue monotone paths have <= b-2 vertices, or all red ones <= a-2. It fails at (a,b,n) = (3,5,4), (3,6,5), (4,5,6), (4,6,5), (4,6,7), (5,5,8) (logs/cutlemma-*.log; scripts/cut_lemma.py).
* The jump transfer is false. Theorem A needs J(v)+K(v) <= a. Colourings with no red cyclic P_a, no blue cyclic P_b, and red runs of total length a-1 around a vertex exist up to n = (a-1)(b-2), e.g. (5,5,12) (logs/runs-*.log; scripts/runs_test.py).
* Circulant restriction is useless. P5 vs P5 is UNSAT at n = 12 under circulant colourings, although real witnesses exist (scripts/ramsey_circ.py).

## 374246 (routine)
* Upper bound: M_a^nest is a subgraph of K_a with the same vertex order, so R_ord(M_a^nest, P_b^mon) <= R_ord(K_a, P_b^mon) = 1+(a-1)(b-1). This is source Theorem 1.3 with the colours exchanged, which is symmetric.
* Lower bound: on n = (a-1)(b-1) vertices, colour {u,v} with colour 1 iff floor(u/(a-1)) = floor(v/(a-1)).
  * A colour-1 nested matching has outer edge {phi(0), phi(a-1)} inside one block. Since phi is increasing, all a vertices lie in that block of size a-1, a contradiction.
  * A colour-2 monotone path visits strictly increasing blocks, so it has at most b-1 vertices.
* For a = 2 or b <= 2 the claim is trivial.

## 374243 (SAT)
* scripts/ramsey_sat.py encodes the source's Section 3 (ordered/cyclic tuples) and is validated on 7 table cells.
* scripts/ramsey_cells.py runs CaDiCaL with a time limit and stores models.
* f(a,b) = ceil((3ab-5a)/2) - 2b + 5. SAT at f-1 for (3,9), (4,6), (6,4), (5,5), (7,4). UNKNOWN at f after 112 s each.

## 374521 (reduction)
* The roots of the Laplacian matching polynomial interlace under adding an edge (Wan-Wang-Mohammadian), so sorted roots of H = G+F dominate those of G.
* If G (connected) and H both have integral LM roots, sorted matching gives non-negative integer shifts summing to 2|F|. That is a multi-edge LMRIV.
* So the conjecture implies there are no such integral pairs.
* For trees, LM equals the Laplacian characteristic polynomial (Mohammadian). Stars have integral roots, so the search would need H with cycles and integral LM roots. Not run (no graph generator available).

## 375112 (rho clause, corroboration only)
* From the source's Fact 2.9, rho = D_y/(x D_x) at the dominant singularity with D = 1 - x(1+y) + 1/B(1/x,1/y). This gives rho = 1/2 iff sum over borders of (2|b|_1 - |b|) lambda^|b| = 0, where lambda is the largest real root of (z-2) sum_b z^{|b|-1} + 1.
* Checked numerically against rho^{11} and rho^{1001} from the source (scripts/rho_check.py).
* Omega proves this clause in Lean, so this is not new.

## 375370, 374960, 375467
See results.json. The C sources are in csrc/ (crim.c, qzeta.c, xray.c); the binaries were built with leanc into tmp/.
