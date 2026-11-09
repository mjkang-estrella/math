# 351504: the (k,H)-kernel conjecture for r-quasi-transitive digraphs is true (a short bridge, zero credit expected)

## Source

- Galeana-Sánchez and Tecpa-Galván, arXiv:2108.01168 v1, Conjecture in Section 3 (TeX line 356): "If D is an H-colored r-quasi-transitive digraph (r ≥ 2), then D has a (k,H)-kernel for every k ≥ r+2."
- Definitions (TeX lines 85–96):
  - **H-length.** The H-length of an open path is |O_H|+1, where O_H is the set of internal obstructions. Hence the H-length of an open path is at most its length.
  - **(k,H)-independent.** Every path between two distinct vertices of S has H-length ≥ k.
  - **(k−1,H)-absorbent.** Every v ∉ S has a vS-path of H-length ≤ k−1.
- The source proves the cases r = 2 (k ≥ 4) and r = 3 (k ≥ 5) by Duchet's theorem on the closure C_H^{k−1}(D).

## Ingredients (both published before the source)

- **(K)** Galeana-Sánchez, Hernández-Cruz and Juárez-Camacho, Discrete Math. 313 (2013) 2582–2591, arXiv:1206.1897 (abstract read; receipt `sources/351504-kings-abs.html`). A k-quasi-transitive digraph has a (k+1)-king if and only if it has a unique initial strong component.
- **(L)** The same paper, Lemma `k-1-dom-comp` (TeX `sources/tex-351504-kings/main.tex` line 217). If S1 and S2 are distinct strong components of a k-quasi-transitive digraph and S1 reaches S2, then every vertex of S1 reaches every vertex of S2 by a path of length ≤ k−1. A direct two-line proof also works:
  - Let x_0…x_L be a geodesic with L ≥ r.
  - Each x_{i+r} → x_i must be an arc, since the forward chord would shorten the geodesic.
  - So x_L reaches x_0, and the endpoints lie in one strong component.

## Proof

Let D be r-quasi-transitive with r ≥ 2, let k ≥ r+2, and let ρ be any H-colouring.

1. Reversing all arcs preserves r-quasi-transitivity. Take a terminal strong component T of D. Then D[T] is r-quasi-transitive (induced subdigraphs inherit the property) and strong.
2. By (K) applied to the reverse of D[T], there is a vertex v_T ∈ T such that every u ∈ T has a u v_T-path in D of length ≤ r+1.
3. Let S = {v_T : T a terminal strong component of D}.
4. *Independence.* Distinct terminal components are mutually unreachable, so there is no path between two distinct vertices of S, and (k,H)-independence holds vacuously.
5. *Absorbance.* Let u ∉ S.
   - If u lies in a terminal component T, then u reaches v_T by a path of length ≤ r+1 ≤ k−1.
   - Otherwise u reaches some terminal component T and hence reaches v_T, which lies in a different strong component. By (L), u reaches v_T by a path of length ≤ r−1.
   - In both cases the H-length of that path is at most its length, which is at most k−1.
6. Hence S is a (k,H)-kernel. ∎

## Disposition

The conjecture holds in full scope, with the exact threshold k ≥ r+2. The new part, however, is a one-paragraph combination of two results from a 2013 paper by the same first author plus the trivial bound H-length ≤ length. By the brief's precedents (369221, 374241, 357849), this is a routine bridge, so we expect zero credit and do not file a candidate. No exhaustive search was run, because the proof makes it moot.
