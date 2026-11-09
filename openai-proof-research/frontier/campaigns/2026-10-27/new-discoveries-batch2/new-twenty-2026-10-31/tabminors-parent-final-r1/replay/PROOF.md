# Ordinary proof: MathDB 359279 is false

Status: DRAFT, prepared with AI assistance (Claude Opus 5.5). Zero accepted campaign credit; root performs the final replay and paper review.

## 1. Source definitions

Source: W. Q. Erickson, D. Herden, J. Meddaugh, M. R. Sepanski, C. Hammon, J. Mohn and I. Ruiz-Bolanos, *Young tableau reconstruction via minors*, arXiv:2307.13161 v1 (read from the e-print `main.tex`); journal version J. Combin. Theory Ser. A 209 (2025) 105950 (body not read).

* **Tableaux.** YT(n) is the set of standard Young tableaux of size n over [1, n], in English convention: rows are left-justified and weakly decrease in length from the top, and entries strictly increase along rows and down columns.
* **Deletion T − m.** Delete the cell with entry m, leaving an empty space. While a cell lies directly to the right of or directly below the empty space, slide the cell with the smaller entry into the empty space. The process terminates at an outer corner, which is removed. Finally subtract 1 from each entry larger than m. The result lies in YT(n − 1).
* **Minors.** A k-minor of T is a tableau obtained by iteratively deleting k cells. M_k(T) is the set and mM_k(T) the multiset of all k-minors. The multiset is taken over deletion sequences: the proof of the source's Theorem `thm: exp lower bound` says "there are n(n−1)⋯(n−k+1) minors in total". Equivalently, mM_0(T) = {T} and mM_{k+1}(T) = Σ_{m=1}^{n} mM_k(T − m).
* **Conjecture `conj:k+4`.** "Let k ≥ 1. Let T ∈ YT(n), where n ≥ k + 4. Then mM_k(T) determines T." The source says it was verified by computer for k ≤ 5. "Determines" means T ↦ mM_k(T) is injective on YT(n).

## 2. Main theorem

**Theorem.** Let T₁ be the hook of shape (5, 1⁷) with first row 1 5 7 8 12 and first column 1 2 3 4 6 9 10 11, and T₂ the hook of shape (6, 1⁶) with first row 1 2 3 7 10 11 and first column 1 4 5 6 8 9 12. Then T₁ ≠ T₂ are in YT(12) and mM₈(T₁) = mM₈(T₂). Hence Conjecture `conj:k+4` fails at k = 8, n = 12 = k + 4.

*Proof.* Both fillings are standard, and the shapes differ. Write a weighted list as L = [(U₁, c₁), …, (U_r, c_r)] and its denotation den_k(L) = Σ c_i · mM_k(U_i). Define step(L) as follows: replace each (U, c) by the |U| pairs (U − m, c) for m = 1, …, |U|, then merge equal tableaux by adding their weights.

* By the recursion for mM_{k+1}, den_{k+1}(L) = den_k(flatten(L)).
* Merging preserves the weighted sum.
* Hence den_{k+1}(L) = den_k(step(L)), and mM_k(T) = den_k([(T, 1)]).

Iterating eight times from [(T₁, 1)] gives lists A₁, …, A₈, and from [(T₂, 1)] gives B₁, …, B₈. So mM₈(T₁) = den₀(A₈) and mM₈(T₂) = den₀(B₈), where den₀ is the literal weighted multiset. The lists A₈ and B₈ are permutations of each other. Both consist of the eight hook tableaux of size 4, each with weight between 725,760 and 3,709,440, and the weights sum to 12!/4! = 19,958,400 in each case.

The sixteen lists are explicit (`formal/TabMinors.lean`). Each step identity step(A_i) = A_{i+1} is a finite computation. All of them are kernel-checked in Lean, and they were reproduced independently in Python (`scripts/check_pair.py`, `evidence/review-r1/check_pair.py`). ∎

## 3. Hook shapes: no constant c works (ordinary mathematics, NOT Lean-verified)

Encode a hook H of size n = N + 1 by the word w ∈ {A, L}^N. Letter t records whether entry t + 1 lies in the arm (first row) or the leg (first column).

**Lemma 1.** For N ≥ 1, deleting entry 1 or entry 2 from H(w) gives H(w with letter 1 removed). Deleting m ≥ 3 gives H(w with letter m − 1 removed).

*Proof.*
* If m ≥ 3, the cell m has at most one neighbour to its right or below, inside its own line. The line slides back by one, and relabelling removes the letter m − 1.
* If m = 2, the cell 2 is adjacent to the corner, and its line slides back. Letter 1 is removed.
* If m = 1, the smaller neighbour of the corner is 2, which slides into the corner. The gap then runs along the line of 2 to its end. After relabelling, the result coincides with deleting 2.

**Lemma 2.** For 1 ≤ k ≤ N − 1,

mM_k(H(w)) = k! · Σ_{P ⊆ [N], |P| = N − k} min(P) · {H(w|_P)}.

*Proof.* By Lemma 1, a deletion sequence of length k from H(w) deletes the letters of some Q = [N] \ P, one at a time, in some order. At each step the current word is nonempty, of length at least N − k + 1 ≥ 2. A step that removes the current first letter arises from two entries (1 and 2). Any other step arises from exactly one entry. So the multiplicity of an ordering of Q is 2^(number of steps that remove the current first letter).

* A letter q > min P is never first, because min P is never deleted.
* Put j = min P − 1, so the letters below min P are 1, …, j, all in Q. Such a letter q is first when deleted exactly when all of 1, …, q − 1 were deleted before it. That happens exactly when q comes last among {1, …, q} in the relative order.
* For a uniformly random relative order σ of {1, …, j}, these j events are independent, with probabilities 1/q. Hence Σ_σ 2^{#events} = j! · Π_{q=1}^{j} (1 + 1/q) = (j + 1)!.
* Interleaving with the other k − j letters of Q gives total weight C(k, j) · (k − j)! · (j + 1)! = k! · (j + 1) = k! · min P.

**Theorem 3.** For every integer c ≥ 2 and every sufficiently large k, mM_k is not injective on YT(k + c). Consequently, for no constant c does "n ≥ k + c implies mM_k(T) determines T" hold for all k ≥ 1. Let f(k) be the least n₀ such that mM_k is injective on YT(n) for all n ≥ n₀; it exists by the source's cubic bound (Theorem `thm: exp lower bound`). Then f(k) − k → ∞.

*Proof.*
* For a constant c ≤ 4, the main theorem already refutes the bound, since 12 ≥ 8 + c.
* For c ≥ 2, put r = c − 1, take N large, and set n = N + 1 and k = N − r ≥ 1, so that n = k + c. As N ranges over all large integers, k ranges over all large integers. By Lemma 2, mM_k(H(w)) = k! Σ_{τ ∈ {A,L}^r} V_τ(w) · {H(τ)}, where V_τ(w) = Σ_{|P| = r, w|_P = τ} min P. The tableaux H(τ) are pairwise distinct, so mM_k(H(w)) determines and is determined by the vector V(w).
* Each coordinate lies in [0, N · C(N, r)]. So V takes at most (N · C(N, r) + 1)^{2^r} values, which is polynomial in N. This is smaller than the 2^N words for large N.
* By pigeonhole, there are words w ≠ w′ with V(w) = V(w′). Then H(w) ≠ H(w′) are tableaux in YT(n) with equal mM_k, and n = k + c. ∎

Explicit instances:
* c = 4: the main theorem.
* c = 5: n = 16, k = 11. One hook has first row 1 2 3 4 5 9 10 11 12 13 16 and first column 1 6 7 8 14 15. The other has first row 1 4 5 6 7 8 12 13 14 15 and first column 1 2 3 9 10 11 16. This pair was confirmed exactly three times: by the lane (`evidence/lane-r118/logs/verify-c5.log`), by the independent reviewer, and here by `scripts/check_pair.py --c5`, which also checks Lemma 2 on both hooks.

## 4. Diagnostic computations (not part of the proof)

* The lane's exhaustive C sweep (two 64-bit hashes) and the reviewer's exact Python sweep (n ≤ 12) agree: at n = k + 4, mM_k is injective on YT(k + 4) for k ≤ 7 and fails at k = 8.
* At n = 12 there are exactly 4 colliding pairs (8 tableaux) out of 140,152: the pair above, the hook pair with first rows {1, 5, 6, 8, 12} and {1, 2, 3, 6, 10, 11}, and the transposes of both. The lane note's "4 colliding rows" is corrected here to 4 pairs.
* The lane reports further failures at n = k + 4 for k = 9, 10, 11. These counts were not rechecked independently.
