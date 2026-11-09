# Statement correspondence: MathDB 359279 and `TabMinors.not_conjecture`

| Source (arXiv:2307.13161 v1, Section 2 and Concluding Remarks) | Lean (`formal/TabMinors.lean`) |
|---|---|
| YT(n): standard Young tableaux of size n over [1, n], English convention | `Tab := List (List ℕ)` (rows, top to bottom) and `IsSYT n T` (nonempty rows; weakly decreasing row lengths; strictly increasing rows; strictly increasing columns; `T.flatten.Perm (List.range' 1 n)`) |
| T − m: delete m; while a cell is right of or below the gap, slide the smaller one in; remove the final outer corner; subtract 1 from entries > m | `slide` (reads only (i, j+1) and (i+1, j); fuel `size T` suffices because each move raises i + j) and `del T m` (locate m, slide, relabel) |
| k-minor: k iterated deletions; mM_k(T): multiset over all deletion sequences ("n(n−1)⋯(n−k+1) minors in total") | `minors 0 T = {T}`, `minors (k+1) T = Σ_{i < size T} minors k (del T (i+1))` (a `Multiset Tab`) |
| conj:k+4: k ≥ 1, T ∈ YT(n), n ≥ k + 4 ⇒ mM_k(T) determines T | `Conjecture : ∀ k n, 1 ≤ k → k + 4 ≤ n → ∀ T U, IsSYT n T → IsSYT n U → minors k T = minors k U → T = U` |
| Refutation | `not_conjecture : ¬ Conjecture` (instance k = 8, n = 12, T₁, T₂) |

Proof infrastructure, all proved in general without hypotheses:
* `den`, `ins`, `norm`, `step`;
* `sum_ins`, `sum_norm`, `nsmul_list_sum`, `den_succ`;
* `minors_eq_den`, `chain`, `den_perm`.

Finite certificates, each checked by `decide +kernel`:
* `T₁_syt`, `T₂_syt`, `T₁_ne_T₂`;
* `hA1`–`hA8` and `hB1`–`hB8`;
* `A1_ok`–`B8_ok` (every listed minor at level i is an SYT of size 12 − i);
* `hAB : A8.Perm B8`.

Controls:
* `Controls.lean` reproduces the source figure (T − 8) and the source's n = 7 pair, which has equal sets of 2-minors and different multisets.
* `negative/NegControl1.lean` (A8 = B8 as lists) and `negative/NegControl2.lean` (a wrong chain step) must fail.

Annotation: `noncomputable` on `slide`, `del`, `minors`, `den`, `ins`, `norm` and `step` (root fix, annotation-only). It prevents the compiler-generated `_unsafe_rec` partial companions that the full flag audit rejects. Kernel reduction is unaffected.

Fidelity review: `evidence/review-r1/REVIEW.md` (gate A PASS). Root adjudication: `evidence/tabminors-root-adjudication-r1.json`.

Not formalised: Lemmas 2–3 and Theorem 4 of the paper (hooks, no constant c), and the diagnostic sweeps.
