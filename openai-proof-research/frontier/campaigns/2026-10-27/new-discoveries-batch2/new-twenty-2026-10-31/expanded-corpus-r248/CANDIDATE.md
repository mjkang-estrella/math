# CANDIDATE: none

This lane proposes no candidate for acceptance. Each of the 20 reserved records ended in one of three ways:
- already resolved in print;
- a zero-credit literal, folklore or routine failure;
- parked without a finished proof or certificate.

See `SUMMARY.md` and `results.json`.

## Nearest leads and their uncompiled Lean plans

Neither plan has been compiled. A plan is only worth executing if the open lemmas get proved.

### 335271: odd-k edge bound for k-in-out graphs (intended order 2k−1, k odd, k ≥ 5)

**Statement plan:**
- A `Digraph` on `Fin (2*k-1)` (an irreflexive relation) with labelled incoming and outgoing vertices.
- `IsHamPath` defined as a `List.Nodup` path covering every vertex.
- The paired vertices and single visit conditions written literally from Definition 1 of the source.
- The theorem: `Odd k → 5 ≤ k → IsInOut S → 4*k-3 ≤ S.arcCount`.

**Proof plan:**
1. Normal form (the source's argument): with exactly 4k−4 arcs, every arc is used, the types split into I, O, B, N, and the degrees are exactly 2.
2. Two-spanning-trees lemma (`SUMMARY.md`).
3. L1, trees are paths: **open**.
4. L2, no odd-k path-tree solution: **open**.

**Cost:** high, because of Hamiltonian paths for general k. A finite instance alone, such as the k = 5 exhaustive search, is a bounded diagnostic and does not give a full-scope endpoint.

### 336718: P_n = Σ_i (−1)^i C(n,i) [2n−i]!_q ∈ N[q]

**Statement plan:**
- Define `qfact : ℕ → Polynomial ℤ`.
- The theorem: `∀ n i, 0 ≤ (P n).coeff i`, plus a semantic bridge to the matrix count from the source (Cor. fullrankrect) if the literal endpoint must mention matrices over F_q.

**Proof plan:** needs a positive recurrence for Q_j(m) when m ≥ 2j−1. **Open.**

**Cost:** moderate once such a recurrence exists, since it would be pure polynomial algebra. The matrix-count bridge would be the expensive part.
