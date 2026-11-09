# CANDIDATE 381292: counterexample to the Aharoni–Howard stronger rainbow degree-sequence conjecture

Lane: expanded-corpus-r199 (Claude). **No credit is claimed.** Status: complete ordinary proof plus an UNCOMPILED Lean draft. **Credit risk: HIGH** (see §5).

## 1. Record and source

- MathDB 381292, "A stronger rainbow degree-sequence conjecture for bipartite graphs". The exact raw line and hashes are in `raw/381292.jsonl`, `extracted.json` and `results.json`.
- Source: R. Aharoni, D. Howard, "A rainbow r-partite version of the Erdős–Ko–Rado theorem", arXiv:1605.06752 (v1 is the only arXiv version; TeX read in `sources/tex/1605.06752/`). It is the final conjecture of §"Further conjectures", after the matrix reformulation of the main Theorem (Theorem \ref{maintheorem}).
- Source setting: F_1, …, F_k ⊆ E(K_{n,n}). Order one side v_1, …, v_n and let a_ij = deg_{F_i}(v_j), so the row sum r_i is |F_i|. For a sequence a, the arrow notation sorts it into non-decreasing order.
- The source's reformulated Theorem: if Σ_{i≤j} r⃗_i > j(j−1)n for all j ≤ k, then some π ∈ S_k has the sorted values of (a_{iπ(i)}) dominating (1, 2, …, k).
- **Conjecture (source and MathDB):** under the same hypothesis there is a permutation π: [k] → [k] with Σ_{i≤j} (sorted (a_{iπ(i)}))_i > j(j−1) for every j ≤ k.
- The proof in the source assumes the F_i are bipartitely shifted ("As before, we assume that F_i are all shifted"), so each row of A is non-increasing.
- **Literal defect:** the MathDB paraphrase fixes no ordering or shifting. Taken literally it already fails trivially, for example with all edges at vertices v_{k+1}, …. That is a zero-credit formulation defect. The counterexample below uses **shifted** graphs in the natural ordering, so it refutes the source's intended statement **and** the literal MathDB record.

## 2. Result

**Theorem.** Let k ≥ 3 and n > (k−1)². Put x_2 = 2 and x_i = 2i − 3 for 3 ≤ i ≤ k. Let sides M = {m_1, …, m_n} and W = {v_1, …, v_n}, and define

- F_1 = {m_1 v_1};
- F_i = {m_a v_1 : a ≤ n} ∪ {m_a v_j : j ≥ 2, a ≤ x_i} for 2 ≤ i ≤ k.

Every F_i is bipartitely shifted. The degree rows are (1, 0, …, 0) and (n, x_i, …, x_i), so r_1 = 1 and r_i = n + (n−1)x_i.

1. **The hypothesis holds.** The r_i increase with i. For j = 1, 1 > 0. For j ≥ 2, Σ_{i≤j} r_i = 1 + (j−1)n + (n−1)((j−1)² + 1), because x_2 + … + x_j = 2 + Σ_{i=3}^{j}(2i−3) = (j−1)² + 1. This exceeds j(j−1)n exactly when n − (j−1)² − 1 + 1 > 0, that is, when n > (j−1)². That holds for all j ≤ k.
2. **The conclusion fails for every π ∈ S_k.**
   - If π(1) ≠ 1, row 1 contributes a_{1π(1)} = 0. The sorted sequence then starts with 0, so the j = 1 inequality 0 > 0 fails.
   - If π(1) = 1, the selected values are {1} ∪ {x_i : i ≥ 2}, because rows i ≥ 2 are constant equal to x_i off column 1. Sorted, this is (1, 2, 3, 5, …, 2k−3), with total 1 + (k−1)² + 1 = (k−1)² + 2. The conjecture needs the total to exceed k(k−1), but k(k−1) − (k−1)² − 2 = k − 3 ≥ 0. So j = k fails, and it fails by k − 3 + 1.
3. The source's proved Theorem is consistent with this: (1, 2, 3, 5, …) dominates (1, 2, …, k). A rainbow matching exists, namely m_1v_1, m_2v_2, …, m_kv_k.

**Smallest instances.**

- k = 3, n = 5: rows (1,0,0,0,0), (5,2,2,2,2), (5,3,3,3,3); sums 1, 13, 17; hypothesis 1 > 0, 14 > 10, 31 > 30. The best π gives (1,2,3), with 6 > 6 false.
- k = 4, n = 10: rows (1,0,…), (10,2,…), (10,3,…), (10,5,…); sums 1, 28, 37, 55. Every π with all selected entries positive gives (1,2,3,5), with 11 > 12 false.

Robustness: for k = 4 the instance also refutes the relaxed reading "all selected entries ≥ 1 and Σ_{i≤j} ≥ j(j−1) for j ≥ 2" (`relaxed_nonstrict_conclusion_holds = false`). The k = 3 instance fails only by strict equality.

## 3. Computation (diagnostics)

- `scripts/rainbow_search.py k n`: exhaustive over shifted row multisets. Only the first k columns enter the conclusion, and the hypothesis is monotone in row sums, so the maximal sum c_1 + … + c_k + (n−k)c_k may be used for given first-k entries.
  - k = 2, n ≤ 20: no failure.
  - k = 3: no failure for n = 3, 4. At n = 5 there is exactly one failing multiset (the family above). For n = 6 and n = 12 the minimum margin is exactly 0; that is, for k = 3 every failure is a strict-boundary failure.
- `scripts/rainbow_certificate.py k n`: independent edge-level check, building the actual edge sets, testing shiftedness, the hypothesis for all subsets I ⊆ [k], every π ∈ S_k and every injection [k] → [n]. Checked for (k, n) = (3, 5) and (4, 10).

## 4. Prior-art screen

- arXiv 1605.06752 has a single version. The CPC version of record (Combin. Probab. Comput. 26 (2017) 321–337, DOI 10.1017/S0963548316000353) is **paywalled and not read**. Whether the "Further conjectures" section survives in print is **unknown** (349435 lesson).
- Web searches (standard and extended) found no refutation or later treatment of this conjecture.
- GitHub (8 queries), Lean Pool HEAD 01db1d70, Omega 7089bc5f and OpenAI/math 4eaee875: no relevant hits. LeanPool/AharoniKorman concerns a different poset conjecture.

## 5. Credit risk: HIGH

- The conjecture is a speculative "stronger" variant at the very end of an arXiv preprint, possibly not in the version of record.
- The mechanism is short. Row sums can be dominated by a single full column v_1, which only one row can use, while a single-edge F_1 must also take column 1. Root may consider this a generic failure of a row-sum-only hypothesis.
- For k = 3 the failure is only at the strict inequality; the robust failure needs k ≥ 4.
- Lean cost is very low: explicit Finsets on Fin 10 × Fin 10, a Fintype permutation search over S_4, and `decide`.

## 6. Statement-correspondence plan and Lean draft

The literal record quantifies over all k, n and F_1, …, F_k ⊆ E(K_{n,n}) and refers to the degrees of v_1, …, v_n. Model:

- F_i : Finset (Fin n × Fin n) (pairs (left, right)), with a_ij = |{e ∈ F_i : e.2 = j}|.
- Sorted rearrangement via `List.insertionSort (· ≤ ·)`.
- Prefix sums via `List.take` and `List.sum`.
- π : Equiv.Perm (Fin k), with columns embedded by `Fin.castLE` (k ≤ n).

The negation is ∃ k n F with hypothesis ∧ ∀ π, ∃ j ≤ k with prefix-sum failure. Draft: `lean/RainbowDegree381292.lean` (**UNCOMPILED**), proving the negation at k = 4, n = 10 (robust) and at k = 3, n = 5, by `decide`.
