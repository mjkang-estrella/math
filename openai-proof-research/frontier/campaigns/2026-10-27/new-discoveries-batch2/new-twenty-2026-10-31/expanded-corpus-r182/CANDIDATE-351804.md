# CANDIDATE 351804: a 5-vertex counterexample to the Yang–Wang extremal A_α conjecture for non-strongly connected digraphs

Status: an ordinary proof with an exact certificate, checked by exact rational arithmetic in Python. The Lean sources are an UNCOMPILED draft (`lean/AalphaNonStrongCounterexample.lean`); Lean was not run in this lane. The lane does not self-accept.

Credit risk: HIGH (see section 6). Lean cost: LOW (a finite 5×5 certificate).

## 1. Source and exact statement

- MathDB 351804, "The extremal A_α spectral radius conjecture for non-strongly connected digraphs". The raw line is in `raw/351804.jsonl`; provenance (chunk, line and hashes) is in `extracted.json`.
- Source: X. Yang and L. Wang, arXiv:2109.00409 v1 (the only arXiv version, 1 Sep 2021), Conjecture 2.10 (TeX line 235): "Among all digraphs in G_n^m, for any α∈[0,1), G'' is a digraph which has the maximal A_α spectral radius."
  - Receipt: `sources/351804-abs.html`; e-print `sources/eprint-351804.tgz`.
- Journal version: X. Yang, L. Wang and W. Xi, Oper. Matrices 18 (2024) 319–333, doi 10.7153/oam-2024-18-19.
  - Receipt: `sources/oam-351804/full.pdf`, sha256 1fd6edab52989e3618cd9ad5e9e916810072a7d7f8447c3e8a328259501d7ee6.
  - Conjecture 2.10 was removed from the journal version and replaced by:
    - Theorem 3.7: K_n^m, which is G″ built on the complete strong component K_m, is the unique maximiser over all of G_n^m.
    - Remark 3.8, an explicit open question: "if the strong component G* of G and n_i for i = 1,…,m are fixed, can we get ρ_α(G'') ≥ ρ_α(G') for any α ∈ [0,1)?"

Definitions, from TeX lines 96–110:

- **The class G_n^m.** Non-strongly connected digraphs of order n with a unique strong component G* of order m, plus directed trees T^(i) with n_i vertices hung on each vertex v_i of G*.
- **Ordering.** The vertices of G* are ordered by out-degree in G*: d⁺(v1) ≥ … ≥ d⁺(vm).
- **The digraph G''.** Built from G by deleting all tree arcs and adding the out-star v1 → u for every vertex u outside G*.
- **The matrix.** A_α(G) = α·Diag(d⁺) + (1−α)·A(G), and ρ_α is its spectral radius.

The source's Theorem 2.9 proves ρ_α(G'') ≥ ρ_α(G) for α ∈ [d⁺_{G*}(v1)/(d⁺_{G*}(v1)+n−m−n1+1), 1) and for α = 0. The proof goes through Theorems 2.7 and 2.8, which compare G with the G'' that has the same G*. The conjecture proposes the inequality for every α ∈ [0,1).

## 2. Counterexample

Take n = 5 and m = 4, with vertices 0,…,4.

- **G\*.** Arcs 0→1, 0→2, 1→0, 1→2, 1→3, 2→0, 3→0.
  - It is strongly connected.
  - Its out-degrees are (2, 3, 1, 1), so v1 = vertex 1 is the unique vertex of maximum out-degree.
- **G = G\* + (0→4).** A single pendant out-arc is hung at vertex 0, so T^(0) = {0, 4} and the other trees are trivial.
  - G is non-strong: its strong components are {0,1,2,3} and {4}.
  - Hence G ∈ G_5^4.
- **G'' = G\* + (1→4).** This is the source's construction applied to G. It is also the G' of G, because the tree is already an out-star.

Take α = 1/4. Then 4·A_{1/4} = Diag(d⁺) + 3·A, which gives integer matrices:

```
B(G)   = [[3,3,3,0,3],[3,3,3,3,0],[3,0,1,0,0],[3,0,0,1,0],[0,0,0,0,0]]
B(G'') = [[2,3,3,0,0],[3,4,3,3,3],[3,0,1,0,0],[3,0,0,1,0],[0,0,0,0,0]]
det(sI − B(G))   = s (s^4 − 8 s^3 + 4 s^2 − 24 s + 27)
det(sI − B(G'')) = s (s^4 − 8 s^3 + 3 s^2 − 13 s + 17)
```

**Claim.** ρ_{1/4}(G) > 781/400 > ρ_{1/4}(G''). Numerically, ρ_{1/4}(G) ≈ 1.95611 and ρ_{1/4}(G'') ≈ 1.94829.

**Proof.**

1. *Lower bound for G.* Let p(s) = s(s^4 − 8s^3 + 4s^2 − 24s + 27).
   - p(781/100) = −544178368899/10^10 < 0.
   - p(8) = 8·91 > 0.
   - By the intermediate value theorem, B(G) has a real eigenvalue in (7.81, 8).
   - Hence ρ(B(G)) > 7.81, and ρ_{1/4}(G) = ρ(B(G))/4 > 781/400.
2. *Upper bound for G''.* Let x = (671, 1000, 296, 296, 1) > 0. Then
   - B(G'')x = (5230, 7792, 2309, 2309, 0), so
   - (B(G'')x)_i ≤ (2309/296)·x_i for every i, where 2309/296 = 7.80067… < 7.81.

   For a nonnegative matrix B and a positive vector x with Bx ≤ c·x, every complex eigenvalue μ satisfies |μ| ≤ c. To see this, take an eigenvector v and an index i maximising |v_i|/x_i. Then

   |μ||v_i| = |Σ_j B_ij v_j| ≤ Σ_j B_ij x_j·|v_i|/x_i ≤ c|v_i|.

   Hence ρ(B(G'')) ≤ 2309/296 < 7.81, and ρ_{1/4}(G'') < 781/400.

So at α = 1/4 the digraph G'' does not have the maximal A_α spectral radius among digraphs of G_5^4: G beats it. This holds under any reading in which G'' is compared with digraphs sharing its strong component. α = 1/4 lies outside the source's proven range, whose threshold for this G is 3/(3+5−4−1+1) = 3/4. There is no conflict with Theorem 2.9.

All of the above is checked by `scripts/aalpha_cert2.py`, with output in `logs/aalpha-cert2.log`.

## 3. Mechanism (why the degree heuristic fails)

At α = 0 every placement of the pendant vertices gives the same ρ = ρ(A(G*)). To first order in α, a pendant hung at v_j raises ρ by α·E·x_j y_j/(yᵀx), where x and y are the right and left Perron vectors of A(G*). Out-degree does not control x_j y_j:

| | vertex 0 | vertex 1 | vertex 2 | vertex 3 |
|---|---|---|---|---|
| right Perron x | 0.2999 | 0.3611 | 0.1695 | 0.1695 |
| left Perron y | 0.3611 | 0.2041 | 0.3194 | 0.1154 |
| x_j·y_j | 0.1083 | 0.0737 | 0.0541 | 0.0196 |

(`logs/aalpha-perron.log`.) Vertex 0 has out-degree 2 but the largest product. For large α the leading term α(d⁺_j + E) favours v1, which is why the source's large-α range is correct.

## 4. Coverage of the search

Pendant sets on one vertex were compared against every maximum-out-degree vertex, with α on a grid of 1/20 or 1/40, using Perron roots bracketed by Collatz–Wielandt bounds.

- **m = 3.** All 18 strong digraphs, E ≤ 3: no violation.
- **m = 4.** All 1606 strong labelled digraphs:
  - E = 1: 204 strong digraphs G* admit a violation.
  - E ≤ 3 on the 1/20 grid: 4008 violating (G*, E, α, j) cases, all at α ≤ 0.35.
  - None of them falls inside the source-proved range α ≥ d1/(d1+E). This consistency check is in `logs/aalpha-rangecheck-*.log`.
- The minimum-arc example (7 arcs in G*) is the one above.

So m = 4 and n = 5 is the smallest possible order of a counterexample of this single-out-star type.

## 5. Statement correspondence (for the Lean stage)

MathDB wording: "For every digraph in G_n^m and every α∈[0,1), G'' has maximal A_α spectral radius among all digraphs in G_n^m." G'' is "the specific extremal digraph constructed in the preceding results", which is built from a given G.

There are three readings:

- **R1 (fixed strong component).** For all n, m, all G ∈ G_n^m and all α ∈ [0,1): ρ_α(G) ≤ ρ_α(G''(G)).
  - This matches the structure of the source's Theorem 2.9 and its proof, where both the threshold and the comparison depend on G.
  - It also matches the journal's Remark 3.8, which fixes G* and the n_i.
  - **REFUTED here.** Lean target: ∃ α ∈ [0,1), ρ_α(G''(G)) < ρ_α(G) for the explicit G ∈ G_5^4, plus decidable membership G ∈ G_5^4 and the computation G''(G) = G2.
- **R2 (literal global, with G'' built from an arbitrary G).** This is false already at α = 0 and inside the range of the source's own theorem: take G* a directed cycle versus a complete G*.
  - It contradicts the source's Theorem 2.9, so it cannot be the intended reading.
  - A literal refutation under R2 would be a zero-credit wording correction.
- **R3 (global maximiser, G'' built on K_m).** Proved by the journal version's Theorem 3.7.
  - Under R3 the item is resolved in the authors' favour, which is prior art.

The Lean endpoint should be stated for R1 with fully literal definitions: the digraph, the out-degree, A_α, the spectral radius as the supremum of moduli of complex eigenvalues, the class G_n^m, and the G'' construction. The draft fixes everything except the general G_n^m predicate (to be written as a Bool checker with a soundness lemma) and two elementary sorries:

- the weighted-norm eigenvalue bound;
- the sSup bookkeeping.

## 6. Credit risk (honest)

- **Reading risk.** The journal version replaced the conjecture by Theorem 3.7, which proves R3, and turned R1 into the open question of Remark 3.8. A reviewer may decide that the MathDB item, "among all digraphs in G_n^m", is resolved by Theorem 3.7, and that our example answers only the adjacent question in Remark 3.8. If R1 is accepted as the MathDB scope, the example is a genuine refutation.
- **Generic-mechanism risk (lesson 373367).** The failure is the standard first-order Perron perturbation fact: diagonal sensitivity is proportional to x_j y_j, not to degree. It could be judged a known generic failure of the degree heuristic.
- **Size and significance risk.** It is a single 5-vertex example found by a small exhaustive search, in a niche spectral paper.
- **Prior art screened (2026-11-05 UTC).**
  - Lean Pool HEAD 01db1d70: no hit.
  - Omega HEAD 63ebfbfb, complete D5 and Library trees: no hit.
  - OpenAI/math HEAD 4eaee875 preprint listing: no hit.
  - 8 GitHub repository searches: no hit.
  - 3 web searches: no counterexample, refutation or later citing resolution found.
  - Not checked: Google Scholar citing works of the OaM paper (no access).
