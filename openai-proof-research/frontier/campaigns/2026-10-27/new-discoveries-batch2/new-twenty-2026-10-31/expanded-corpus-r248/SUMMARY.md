# expanded-corpus-r248: summary (Claude lane, 2026-11-05 to 2026-11-07)

## Outcome: no candidate

None of the 20 reserved records yielded a new, qualifying exact solution.

| Group | Count | IDs |
|---|---|---|
| Excluded: already resolved in print | 3 | 335352, 336226, 336252 |
| Excluded: zero-credit literal or routine | 3 | 335668, 336652, 336567 |
| Parked with substantial new computation | 2 | 335271, 336718 |
| Parked: hard, famous or asymptotic | 12 | the rest |

Lane discipline:
- Lean, lake, SAT/ILP and solver binaries were not run.
- Every computation was a single foreground `python3 -I -B` run under `ulimit -v 2000000; timeout 100`.
- Every file written is inside this lane.
- No HTTP request returned 403 or 429.

## Files

- **Records:** `extracted.json` and `raw/<id>.jsonl` hold the exact corpus lines, with one-based line numbers and chunk, raw and statement SHA-256 hashes.
- **Sources:** `sources/*.body` with immutable `*.receipt.json` files: arXiv abs pages, PDFs and e-print LaTeX. The LaTeX was read in memory and written to `texts/*.tex.txt`.
- **Prior-campaign check:** `history-matches.txt`. No reserved ID had a prior campaign disposition. Sibling records from the same sources were handled in other lanes: 336565/336566 in r163, 336741 in r163, 336735 in r188, 336653/336654 in r215.
- **Registry screen:** `outputs/registry-screen.json`.
  - Lean Pool HEAD 01db1d70 is unchanged; the r215 cache at the same HEAD was reused.
  - Omega HEAD cae7cdbe: the tree was fetched here.
  - OpenAI HEAD 4eaee875 is unchanged; the root preprint cache was reused.
  - Four GitHub repository searches returned 0 hits.
  - Result: no prior Lean proof or refutation of any reserved statement.
- **Literature log:** `outputs/web-searches.json`.
- **Per-ID results:** `outputs/dispositions.json` and `results.json` (20 entries). Scripts are in `scripts/`; search outputs are in `outputs/kinout/`.

## Dispositions

- **335352 (Wu–Li permutation rational function, q = 5^k with k even):** proved by Ma and Ge, arXiv:1703.03158, Theorem 3.1.
- **336252 (shuffle compatibility of (udr, pk) and (udr, pk, des)):** (udr, pk) was proved by Baker-Jarvis and Sagan; (udr, pk, des) by Yang and Yan, arXiv:2201.06784 (EJC 29(3)).
- **336226 (Zvonkine's topological recursion for orbifold r-spin Hurwitz numbers):** proved by Dunin-Barkowski, Kramer, Popolitov and Shadrin, arXiv:1905.04524 (Ann. Sci. ENS 2023).
- **335668 (complements of K_w ∇ mC_n are determined by their spectrum):** false through a classical pair.
  - complement(K_w ∇ 2C_3) = wK_1 ∪ K_{3,3}, which is cospectral with (w−4)K_1 ∪ K_{1,9} for every w ≥ 4.
  - This is the classical pair K_{a,a} ∪ (a−1)²K_1 ~ K_{1,a²}; `scripts/cospectral.py` checks exact characteristic polynomials for w = 4, 5, 6.
  - It also refutes the source's own m C_3 "theorem". Folklore pair: zero credit.
- **336652 (T families are cyclically 5-connected when m/gcd(m,c) > 4):** literally false through the source's own mechanism.
  - When m/gcd(m,a) = 3, the a-arrows group the clusters into triples, and each triple is attached to the rest by only 3 spokes.
  - For example, m = 15, a = 5, c = 1 gives a snark with a cyclic 3-edge-cut.
  - This is the argument of the source's Prop. G_α(3k;k,k,1): zero credit.
- **336567 (even-m design codes):** the conjectured code is the extended dual double-error-correcting BCH code with its Kasami weight distribution. The proof would be the same span argument plus classical theory that excluded sibling 336566: routine by precedent.
- **336651:** the scope is defective. If the snark minus P_3 is itself uncolourable, every lift is uncolourable. The source states no colourability hypothesis on the 5-pole that would exclude this.
- **336742 (four-list FUM edge colouring):** the obvious constant-list obstructions fail.
  - Gluing blocks at a cut vertex or a bridge creates a "good vertex" in each block.
  - The source's Lemma lem:maine then gives outer-face colours in {1, 2, 3}.
  - A counterexample would need genuine list assignments; parked.
- **335382, 335553, 335721, 335976, 336029, 336454, 336558, 336620, 336736, 336747:** famous, asymptotic, structural or constructive problems with no finite exact route. Each has a short source-backed note in `results.json`.

## Strongest route 1: 335271 (Glynn, Haythorpe and Moeini, arXiv:1702.03075, v2 only)

**The printed statement.** The source prints: "Any k-in-out graph of order 2k+1 for odd k has at least 4k−3 edges." The intended order is 2k−1, the order of the construction and of the source's Theorem "edges".
- At k = 1 the intended statement fails trivially: one vertex, 0 = 4k−4 arcs. That is a zero-credit smallest-case defect.
- The real question is odd k ≥ 5.

**Normal form, re-derived from the source's proof of Theorem "edges".** Suppose S has order 2k−1 and exactly 4k−4 arcs.
- Every arc lies on some paired Hamiltonian path. Otherwise deleting it would give a k-in-out graph with 4k−5 arcs, contradicting the theorem.
- The source's segment argument then shows that arcs only run X → I∪B and O∪B → Y, where X = I∪N and Y = O∪N.
- The degree counts force every vertex of X to have out-degree exactly 2 and every vertex of Y to have in-degree exactly 2.
- In this form every incoming-to-outgoing path contains one more B-vertex than N-vertex. Since |N| = |B| − 1, a covering family consists of exactly one path, so the single visit condition holds automatically.

**Lemma (new): two spanning trees.** Write P = I∪B for the starts and Q = O∪B for the ends.
- Join the two in-neighbours of each y ∈ Y by an edge. This gives a multigraph H_in on Q with k−1 edges.
- In a paired Hamiltonian path s → t, every y has a predecessor in Q, and every vertex of Q other than t has its successor in Y.
- So the predecessor map is a bijection Y → Q∖{t} that assigns each edge one of its endpoints. That forces |E(C)| = |C| − [t ∈ C] for every component C of H_in.
- Every vertex of Q is the end of some paired path, so H_in is connected. With k vertices and k−1 edges it is a spanning tree, and the predecessor map is the unique rooting at t.
- The same argument on P, using the out-neighbours of X, gives a spanning tree H_out.

Consequences:
- For each pair (s, t) the successor structure is forced, so there is at most one Hamiltonian path from s to t.
- Write f_{s,t} for the closed successor permutation (with t ↦ s added). For tree-adjacent pairs, f_{s′,t} = (s s′) f_{s,t} and f_{s,t′} = f_{s,t} (t t′).
- Hence the sign of f_{s,t} splits as ε(s)·δ(t) up to a global constant, where ε and δ are the bipartition colourings of the two trees.

**Computation**, with every result written to `outputs/kinout/` and never overwritten:

| Case | Search | Graphs or pairs | Solutions |
|---|---|---|---|
| k = 3, all a | normal form | 33 graphs | 0 (agrees with the source) |
| k = 4, all a | normal form | 5,005 graphs | 12 (control) |
| k = 5, all a = 0..4 (70 type words) | normal form | 1,595,041 graphs | 0 |
| k = 5 | independent backtracking re-check | — | 0 |
| k = 6, a = 0, first-option chunk 0 | backtracking | — | 18 (control) |

**Path trees.** Every even-k solution found (k = 4 with a ∈ {0, 1}, and k = 6 with a = 0) has both trees equal to Hamiltonian paths.

**Path-tree model (a = 0).** In path coordinates the closed successor permutation is F_{S,T} = τ B_S^{-1} μ B_T, with B_T = (1 2 … T) and μ fixing 1. The paired condition says each S has exactly one T for which F_{S,T} is a k-cycle, and S ↦ T is injective. An exhaustive search over all (τ, μ) gives:

| k | (τ, μ) pairs | Solutions |
|---|---|---|
| 4 | 144 | 4 |
| 5 | 2,880 | 0 |
| 6 | 86,400 | 24 |
| 7 | 3,628,800 | 0 |

**Remaining lemmas.**
- **L1:** both trees are always paths. This is empirical so far.
- **L2:** the path-tree model has no solution for odd k. It is verified only for k = 5 and 7 with a = 0; the a ≥ 1 analogue has not been derived.

L1 and L2 would together prove the intended conjecture. The source's construction achieves 4k−3 for odd k, so the conjecture would then be sharp. The Lean cost of a general-k Hamiltonian-path proof is high. A counterexample at k = 7 would have been cheap to certify, but the path model rules out the main case.

## Strongest route 2: 336718 (Lewis and Morales, arXiv:1707.08192, conj:poscompdiag)

**The quantity.** By the source's Cor. fullrankrect and Example qderangements, M_{2n} = q^{2n(n−1)} P_n with P_n = Σ_i (−1)^i C(n,i) [2n−i]!_q. The count depends only on n, the number of forbidden cells, which lie in distinct rows and columns.

**Reduction.** Place the forbidden cells in the top n rows. The bottom n rows can then complete the matrix in a number of ways that does not depend on the top rows. This gives P_n = [n]!_q · Q_n(2n), where Q_j(m) = Σ_i (−1)^i C(j,i) [m−i]_q ⋯ [m−j+1]_q is a q-count of fixed-point-free injections [j] → [m].

**Computation** (`scripts/qdiag*.py`):
- P_n ∈ N[q] for n ≤ 30. The source checked n ≤ 40.
- New observation: for 3 ≤ j ≤ 13 and j ≤ m ≤ j+12, Q_j(m) ∈ N[q] exactly when m ≥ 2j−1.
- Three natural recurrences fail to be positive beyond j = 2.

**Remaining lemma.** A manifestly positive formula or recurrence for Q_j(m) when m ≥ 2j−1. Equivalently, a statistic on fixed-point-free injections such that, on the injections fixing any given set of points, it has the q-falling-factorial distribution.

## Honest limits

- The FJV 2015 body and the Discrete Math. journal versions are behind ScienceDirect, which is denied, and were not read.
- Several dispositions rest on abstracts or search summaries of later papers rather than full proof bodies:
  - Ma–Ge (335352);
  - Dunin-Barkowski et al. (336226);
  - Yang–Yan (336252);
  - Palu–Pilaud–Plamondon (336029).
- The k = 6 run covers one first-option chunk and serves only as a control.
- No coverage claim is made beyond the spaces listed above.
