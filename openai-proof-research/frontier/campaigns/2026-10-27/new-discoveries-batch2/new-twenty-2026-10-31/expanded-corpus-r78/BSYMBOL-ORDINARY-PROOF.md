# MathDB 334207: proof of the Ding–Zhang–Ge existence conjecture for linear MDS (n, 2b)_q b-symbol codes

Status: candidate only. Ordinary proof written in this lane on 2026-11-01. The Lean status is recorded in `SUMMARY.md` and `results.json`. Zero credit unless root accepts.

## Source statement and definitions

MathDB 334207 (raw line: corpus chunk `mathdb-normalized-chunk-*.jsonl`; exact provenance in `extracted.json`) states:

> Let q be a prime power, let b ≥ 2, and let n ≥ 2b. A linear MDS (n, 2b)_q b-symbol code should exist.

Primary source: B. Ding, T. Zhang, G. Ge, *Maximum distance separable codes for b-symbol read channels*, arXiv:1609.09236v1 (only version), published in Finite Fields Appl. 49 (2018) 180–197. Conjecture 2 (arXiv text, page 15) reads: "There exist linear MDS (n, 2b)_q b-symbol codes for q being a prime power, b ≥ 2 and n ≥ 2b." The published version's outline still lists Conjectures 1 and 2; the journal body was not accessed.

Definitions (source, Section 2). Let F = F_q. Indices are taken modulo n.

* For x ∈ F^n, wt_b(x) = |{0 ≤ i ≤ n−1 : (x_i, …, x_{i+b−1}) ≠ 0}|.
* D_b(x, y) = |{0 ≤ i ≤ n−1 : (x_i, …, x_{i+b−1}) ≠ (y_i, …, y_{i+b−1})}| = wt_b(x − y) (source Proposition 2.1).
* A code C ⊆ F^n with |C| = M and minimum b-distance d_b = min{D_b(x, y) : x ≠ y in C} is an (n, M, d_b)_q b-symbol code. It is linear if C is a subspace.
* Singleton bound (source Theorem 2.4): if b ≤ d_b ≤ n then M ≤ q^{n − d_b + b}. An (n, M, d_b)_q code with M = q^{n − d_b + b} is an MDS (n, d_b)_q b-symbol code.

So a linear MDS (n, 2b)_q b-symbol code is a subspace C ⊆ F_q^n with |C| = q^{n−b} and minimum b-distance exactly 2b.

## Theorem

For every finite field F = F_q, every b ≥ 2 and every n ≥ 2b, there is a linear MDS (n, 2b)_q b-symbol code. This is exactly Conjecture 2.

(In fact the construction works for b ≥ 1. The window construction below works over every field.)

## Part 1: cyclic window sequences

Call a sequence v_0, …, v_{n−1} ∈ F^b (n ≥ b) *b-good* if, for every s, the b vectors v_s, v_{s+1}, …, v_{s+b−1} (indices mod n) are linearly independent, hence a basis of F^b. Write e_0, …, e_{b−1} for the standard basis.

**Lemma 1 (blocks).** If b | n, the sequence v_j = e_{j mod b} is b-good. *Proof:* every window lists e_0, …, e_{b−1} in cyclic order.

**Lemma 2 (standard vectors plus a remainder).** Let J ⊔ K = {0, …, m−1}. Let u_1, …, u_{|K|} ∈ F^m. The family {e_j : j ∈ J} ∪ {u_i} is linearly independent iff the restrictions u_i|_K are linearly independent in F^K. *Proof:* a relation Σ λ_j e_j + Σ μ_i u_i = 0 restricted to K gives Σ μ_i u_i|_K = 0. Conversely, if μ is a relation among the restrictions, then Σ μ_i u_i is supported on J and is cancelled by a combination of the e_j.

**Lemma 3 (bridge).** Let 1 ≤ r < b, M ≥ 1 and n = Mb + r. Let T_0, …, T_{b+r−1} ∈ F^r be an r-good sequence with T_j = e_j for 0 ≤ j < r. Put p_k := T_{r+k} ∈ F^r for 0 ≤ k ≤ b−1. Define w_c ∈ F^b for 0 ≤ c ≤ r−1 by w_c[k] := p_k[c]. Define

  v_j = e_{j mod b} for 0 ≤ j < Mb,  v_{Mb+c} = w_c for 0 ≤ c < r.

Then v_0, …, v_{n−1} is b-good.

*Proof.* Fix a window of b cyclically consecutive positions. If it contains no bridge position Mb + c, it consists of b consecutive positions in [0, Mb), so it is e_i, …, e_{i+b−1} (indices mod b): a basis. Otherwise it contains a contiguous range of bridge indices c ∈ [α, β) with 0 ≤ α < β ≤ r. It also contains a ≥ 0 block positions Mb − a, …, Mb − 1 just before the bridge, with coordinates b−a, …, b−1. It contains z ≥ 0 positions 0, …, z−1 just after the bridge (cyclically), with coordinates 0, …, z−1. Here a + (β − α) + z = b. These two coordinate sets are disjoint because a + z ≤ b. Let K := {z, …, b−a−1}, with |K| = β − α. By Lemma 2 the window is a basis iff the vectors w_c|_K (α ≤ c < β) are independent. Equivalently, the square matrix (p_k[c])_{k∈K, α≤c<β} is invertible. Equivalently (by transposition), the restrictions p_k|_{[α,β)} (k ∈ K) are independent in F^{[α,β)}. There are three cases.

* (A) α = 0, β < r. The window ends inside the bridge, so z = 0, a = b − β ≥ 1 and K = {0, …, β−1}. The r-window of T starting at position β is e_β, …, e_{r−1}, p_0, …, p_{β−1}. It is a basis because T is r-good. By Lemma 2 in F^r, the vectors p_0|_{[0,β)}, …, p_{β−1}|_{[0,β)} are independent.
* (B) α = 0, β = r. The window contains the whole bridge, K = {z, …, z+r−1} ⊆ [0, b−1]. The r-window of T starting at r + z is p_z, …, p_{z+r−1}. It does not wrap because z + r − 1 ≤ b − 1. It is a basis, which is what is needed.
* (C) α ≥ 1. The window starts at Mb + α inside the bridge, so a = 0, β = r, z = b − (r − α) and K = {z, …, b−1}. The r-window of T starting at r + z is p_z, …, p_{b−1}, followed cyclically by T_0, …, T_{α−1} = e_0, …, e_{α−1}. It is a basis. By Lemma 2 in F^r, the vectors p_k|_{[α,r)} (z ≤ k ≤ b−1) are independent.

These cases are exhaustive. If α ≥ 1 the window starts inside the bridge; since r − α < b it runs to the end of the bridge, which is case (C). If α = 0, then either β = r, which is (B), or β < r. In the last case the window must end inside the bridge, which is (A). ∎

Remark on transposition. Instead of transposing, one can argue directly. Suppose λ ∈ F^{[α,β)} satisfies Σ_c λ_c p_k[c] = 0 for all k ∈ K. The linear functional x ↦ Σ_c λ_c x_c vanishes on every vector of the relevant T-window: on the e's, because their coordinates lie outside [α, β), and on the p_k by hypothesis. That window spans F^r, so the functional is zero and λ = 0. This is the form planned for formalization.

**Theorem A.** For every field F, every b ≥ 1 and every n ≥ b there is a b-good sequence v_0, …, v_{n−1} ∈ F^b with v_j = e_j for 0 ≤ j < b and all entries in {0, 1}.

*Proof by strong induction on b.* For b = 1 take v_j = 1. For b ≥ 2: if b | n use Lemma 1. Otherwise write n = Mb + r with M ≥ 1 and 1 ≤ r < b. Since r < b, the induction hypothesis gives an r-good T of length b + r ≥ r with T_j = e_j (j < r) and 0/1 entries. Lemma 3 gives v. Since M ≥ 1, v_j = e_j for j < b. ∎

The recursion is Euclid-like: (b, n) → (n mod b, b + n mod b). Every window determinant of the constructed 0/1 matrix is ±1 over ℤ, because each reduction step is a signed minor extraction. So the construction is the same matrix over every field. Checked computationally for 228 pairs (b ≤ 12, b ≤ n ≤ 3b+5), 4,106 windows (`scripts/bsym/recursive.py`, `logs/bsym-recursive-B12.log`).

## Part 2: from a b-good sequence to an MDS b-symbol code

Let F = F_q, b ≥ 1, n ≥ 2b. Let v_0, …, v_{n−1} be b-good with v_j = e_j (j < b), as produced by Theorem A. Let H be the b × n matrix with columns v_j and C := ker H ⊆ F^n.

**(a) Size.** H has rank b (its first b columns are the identity), so dim C = n − b and |C| = q^{n−b} = q^{n − 2b + b}.

**(b) d_b ≥ 2b.** Let c ∈ C be nonzero and suppose wt_b(c) ≤ 2b − 1. Since n ≥ 2b, some window is zero. Rotating indices, assume c_{n−b} = … = c_{n−1} = 0, so supp(c) ⊆ [0, n−b−1]. Let m = min supp(c) and m' = max supp(c). The windows starting at m−b+1, …, m (mod n) and at m'−b+1, …, m' are all nonzero. If m' − m ≥ b, these are 2b distinct residues mod n, because they lie in the integer range [m−b+1, m'] of length m' − m + b ≤ n − 1. That contradicts wt_b(c) ≤ 2b − 1. Hence supp(c) ⊆ [m, m+b−1], a window of b consecutive positions. Then Σ_{i} c_i v_i = Hc = 0 is a nontrivial relation among the independent vectors v_m, …, v_{m+b−1}, a contradiction. So every nonzero codeword has wt_b ≥ 2b. Since D_b(x, y) = wt_b(x − y) and C is linear, d_b(C) ≥ 2b.

Rotation remark: rotation of coordinates preserves wt_b and maps the sequence (v_j) to a rotated sequence that is still b-good. So the argument can be run directly with indices relative to the zero window.

**(c) d_b ≤ 2b.** Either use the Singleton bound: q^{n−b} = |C| ≤ q^{n − d_b + b} gives d_b ≤ 2b. Or argue explicitly. In the construction n = Mb + r with M ≥ 2 (because n ≥ 2b), so v_0 = v_b = e_0. Then x := δ_0 − δ_b ∈ C. Its nonzero windows are those containing position 0 or b, namely the starts −b+1, …, 0 and 1, …, b. These are 2b distinct residues since n ≥ 2b, so D_b(x, 0) = 2b.

Hence C is a linear (n, q^{n−b}, 2b)_q b-symbol code with q^{n−b} = q^{n−2b+b}: a linear MDS (n, 2b)_q b-symbol code. ∎

## Independent diagnostics (not proof)

* `scripts/bsym/codecheck.py`: for q ∈ {2, 3, 5}, b ∈ {2, …, 5}, n ∈ [2b, 3b+2] (code size ≤ 300000), enumerating all codewords of ker H confirms rank b, |C| = q^{n−b} and minimum b-weight exactly 2b in all 68 cases. These include the cases q = 2, b = 5, n ∉ 5ℤ, which the source's Theorems 3.13–3.15 do not cover (`logs/bsym-codecheck.log`).
* `scripts/bsym/cyc.py`: independent exhaustive DFS existence search for binary b-good cyclic sequences (b ≤ 7, 2b ≤ n ≤ 3b−1). All exist (`logs/bsym-b7.log` and console records in `SEARCH-COVERAGE.md`).

## Prior-art and novelty limits (bounded)

* Source: Conjecture 2 is stated as open in arXiv:1609.09236v1 (single version). Its known cases are Theorem 3.13 (q ≥ b−1 with b ≥ 3, or q = 2, b = 4), Theorem 3.14 (b = 5, q ≥ 3) and Theorem 3.15 (b | n). The published outline (ScienceDirect listing) still contains Conjectures 1 and 2.
* Liu–Pan, arXiv:2103.16299 (Theorem 5.6) gives a parity-check characterisation of b-symbol MDS codes; our Part 2 is a special case. Their Corollary 5.5 gives n ≤ (q^k − 1)/(q − 1) for b ≤ k − 1. This is vacuous here since k = n − b. They do not construct codes for all n.
* Read (bounded greps of full text): Ma–Luo b-weight distribution arXiv:2107.01717; covering b-symbol codes arXiv:2206.12668; Griesmer bound arXiv:2401.04941; Griesmer-attaining codes arXiv:2507.07728; function-correcting codes arXiv:2503.12894. None claims Conjecture 2.
* Web searches (2026-11-01, standard and extended modes) found no proof of Conjecture 2.
* Registries: Omega HEAD e307ede5b6d5d591f8bc44a4ec150d302e7f31a6 (D5 and Problems trees fetched in full): no b-symbol / MDS path. OpenAI/math HEAD 4eaee87548250b2682affda7d05d947c05554bae unchanged; the cached preprint listing has no b-symbol / MDS entries. These are path screens only.
* Limits: MathSciNet/zbMATH/Google Scholar citation indices were not accessed, and the Chinese-language coding literature was not searched. A classical Hamming-MDS [n, n−b, b+1] code is automatically b-symbol MDS with d_b = 2b. Such codes exist only for short lengths (n ≤ q + 1 in the usual range), so they do not cover the conjecture's content. The construction here is elementary, so independent prior discovery cannot be excluded without a full citation-index search.
