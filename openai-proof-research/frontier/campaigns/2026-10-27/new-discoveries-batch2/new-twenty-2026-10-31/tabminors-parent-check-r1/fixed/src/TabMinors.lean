import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Abel

/-!
# Refutation of the linear-bound multiset reconstruction conjecture for tableau minors

Source: W. Q. Erickson, D. Herden, J. Meddaugh, M. R. Sepanski, C. Hammon,
*Young tableau reconstruction via minors*, arXiv:2307.13161, Conjecture `conj:k+4`:

> Let `k ≥ 1`. Let `T ∈ YT(n)`, where `n ≥ k + 4`. Then `mM_k(T)` determines `T`.

Definitions follow Section 2 of the source.

* A standard Young tableau of size `n` (English convention) is stored as its list of rows,
  top to bottom: rows are nonempty, row lengths weakly decrease, entries increase strictly
  along rows and down columns, and the entries are exactly `1, …, n`.
* `T - m` (jeu de taquin deletion): delete the cell containing `m`; while the empty space
  has a cell directly to its right or directly below it, slide the cell with the smaller
  entry into the empty space; the process ends at an outer corner, which is removed;
  finally subtract `1` from every entry larger than `m`.
* A `k`-minor of `T` is a tableau obtained by iteratively deleting `k` cells; `mM_k(T)` is
  the multiset of all `k`-minors, counted over all sequences of deletions (the source counts
  `n (n-1) ⋯ (n-k+1)` minors in total, proof of Theorem `thm: exp lower bound`).

We prove the negation of the conjecture: for `k = 8`, `n = 12 = k + 4`, the hook tableaux
`T₁` of shape `(5,1⁷)` and `T₂` of shape `(6,1⁶)` below are distinct and have the same
multiset of `8`-minors.
-/

namespace TabMinors

/-- A tableau, as its list of rows from top to bottom. -/
abbrev Tab := List (List ℕ)

/-- Number of cells. -/
def size (T : Tab) : ℕ := (T.map List.length).sum

/-- `T` is a standard Young tableau with entries `1, …, n` (English convention). -/
def IsSYT (n : ℕ) (T : Tab) : Prop :=
  (∀ r ∈ T, r ≠ []) ∧
  T.IsChain (fun r r' => r'.length ≤ r.length) ∧
  (∀ r ∈ T, r.IsChain (· < ·)) ∧
  T.IsChain (fun r r' => ∀ j < r'.length, r.getD j 0 < r'.getD j 0) ∧
  T.flatten.Perm (List.range' 1 n)

instance (n : ℕ) (T : Tab) : Decidable (IsSYT n T) := by
  unfold IsSYT; infer_instance

/-- Entry in row `i`, column `j` (0-based), if that cell exists. -/
def cell (T : Tab) (i j : ℕ) : Option ℕ := T[i]?.bind (·[j]?)

/-- Overwrite the entry of the existing cell `(i, j)`. -/
def setCell (T : Tab) (i j v : ℕ) : Tab := T.set i ((T.getD i []).set j v)

/-- Remove the cell `(i, j)` (an outer corner) and drop a row that becomes empty. -/
def removeCell (T : Tab) (i j : ℕ) : Tab :=
  (T.set i ((T.getD i []).eraseIdx j)).filter (fun r => !r.isEmpty)

/-- Jeu de taquin slides of the empty space at `(i, j)`; the stale value stored in the
empty cell is never read.  Each slide increases `i + j`, so at most `size T - 1` slides
occur and the fuel `size T` used in `del` always suffices for tableaux. -/
noncomputable def slide : ℕ → Tab → ℕ → ℕ → Tab
  | 0, T, _, _ => T
  | fuel + 1, T, i, j =>
    match cell T i (j + 1), cell T (i + 1) j with
    | none, none => removeCell T i j
    | some r, none => slide fuel (setCell T i j r) i (j + 1)
    | none, some b => slide fuel (setCell T i j b) (i + 1) j
    | some r, some b =>
      if r < b then slide fuel (setCell T i j r) i (j + 1)
      else slide fuel (setCell T i j b) (i + 1) j

/-- `T - m`: jeu de taquin deletion of the cell with entry `m`, then relabelling. -/
def del (T : Tab) (m : ℕ) : Tab :=
  let i := T.findIdx (fun r => r.contains m)
  let j := (T.getD i []).idxOf m
  (slide (size T) T i j).map (fun r => r.map (fun x => if m < x then x - 1 else x))

/-- `mM_k(T)`: the multiset of all `k`-minors, over all sequences of `k` deletions
(choose the first deleted entry `m ∈ {1, …, size T}`, then continue in `T - m`). -/
noncomputable def minors : ℕ → Tab → Multiset Tab
  | 0, T => {T}
  | k + 1, T => ((List.range (size T)).map (fun i => minors k (del T (i + 1)))).sum

/-- The source conjecture `conj:k+4` (MathDB 359279), literally. -/
def Conjecture : Prop :=
  ∀ k n : ℕ, 1 ≤ k → k + 4 ≤ n → ∀ T U : Tab, IsSYT n T → IsSYT n U →
    minors k T = minors k U → T = U

/-! ## A sound weighted dynamic program for `minors` -/

/-- Weighted list denotation. -/
def den (k : ℕ) (L : List (Tab × ℕ)) : Multiset Tab := (L.map (fun p => p.2 • minors k p.1)).sum

/-- Insert with merging of equal tableaux. -/
noncomputable def ins (p : Tab × ℕ) : List (Tab × ℕ) → List (Tab × ℕ)
  | [] => [p]
  | q :: L => if q.1 = p.1 then (q.1, q.2 + p.2) :: L else q :: ins p L

def norm (L : List (Tab × ℕ)) : List (Tab × ℕ) := L.foldr ins []

/-- One deletion step on a weighted list. -/
def step (L : List (Tab × ℕ)) : List (Tab × ℕ) :=
  norm (L.flatMap (fun p => (List.range (size p.1)).map (fun i => (del p.1 (i + 1), p.2))))

theorem sum_ins (f : Tab → Multiset Tab) (p : Tab × ℕ) (L : List (Tab × ℕ)) :
    ((ins p L).map (fun q => q.2 • f q.1)).sum = p.2 • f p.1 + (L.map (fun q => q.2 • f q.1)).sum := by
  induction L with
  | nil => simp [ins]
  | cons q L ih =>
    by_cases h : q.1 = p.1
    · simp only [ins, h, ↓reduceIte, List.map_cons, List.sum_cons, add_nsmul]
      rw [← h]; abel
    · simp only [ins, h, ↓reduceIte, List.map_cons, List.sum_cons, ih]; abel

theorem sum_norm (f : Tab → Multiset Tab) (L : List (Tab × ℕ)) :
    ((norm L).map (fun q => q.2 • f q.1)).sum = (L.map (fun q => q.2 • f q.1)).sum := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [norm, List.foldr_cons] at ih ⊢
    rw [sum_ins, ih, List.map_cons, List.sum_cons]

theorem nsmul_list_sum (c : ℕ) (l : List (Multiset Tab)) : c • l.sum = (l.map (c • ·)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [nsmul_add, ih]

theorem den_succ (k : ℕ) (L : List (Tab × ℕ)) : den (k + 1) L = den k (step L) := by
  unfold den step
  rw [sum_norm (minors k)]
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.map_append, List.sum_append]
    congr 1
    rw [minors, nsmul_list_sum, List.map_map, List.map_map]
    rfl

theorem minors_eq_den (k : ℕ) (T : Tab) : minors k T = den k [(T, 1)] := by
  simp only [den, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_nsmul]

theorem chain {k : ℕ} {L L' : List (Tab × ℕ)} (h : step L = L') : den (k + 1) L = den k L' := by
  rw [den_succ, h]

theorem den_perm (k : ℕ) {A B : List (Tab × ℕ)} (h : A.Perm B) : den k A = den k B := by
  unfold den; exact (h.map _).sum_eq

/-! ## The counterexample -/

/-- Shape `(5,1⁷)`: first row `1 5 7 8 12`, first column `1 2 3 4 6 9 10 11`. -/
def T₁ : Tab := [[1, 5, 7, 8, 12], [2], [3], [4], [6], [9], [10], [11]]
/-- Shape `(6,1⁶)`: first row `1 2 3 7 10 11`, first column `1 4 5 6 8 9 12`. -/
def T₂ : Tab := [[1, 2, 3, 7, 10, 11], [4], [5], [6], [8], [9], [12]]

theorem T₁_syt : IsSYT 12 T₁ := by decide +kernel
theorem T₂_syt : IsSYT 12 T₂ := by decide +kernel
theorem T₁_ne_T₂ : T₁ ≠ T₂ := by decide +kernel

/-! Weighted lists after each deletion level (certified below by kernel evaluation). -/

def A1 : List (Tab × ℕ) := [([[1, 5, 7, 8], [2], [3], [4], [6], [9], [10], [11]], 1), ([[1, 5, 7, 8, 11], [2], [3], [4], [6], [9], [10]], 3), ([[1, 5, 7, 11], [2], [3], [4], [6], [8], [9], [10]], 2), ([[1, 5, 6, 7, 11], [2], [3], [4], [8], [9], [10]], 1), ([[1, 6, 7, 11], [2], [3], [4], [5], [8], [9], [10]], 1), ([[1, 4, 6, 7, 11], [2], [3], [5], [8], [9], [10]], 4)]
def A2 : List (Tab × ℕ) := [([[1, 4, 6, 7], [2], [3], [5], [8], [9], [10]], 8), ([[1, 4, 6, 7, 10], [2], [3], [5], [8], [9]], 24), ([[1, 4, 6, 10], [2], [3], [5], [7], [8], [9]], 16), ([[1, 4, 5, 6, 10], [2], [3], [7], [8], [9]], 8), ([[1, 5, 6, 10], [2], [3], [4], [7], [8], [9]], 14), ([[1, 3, 5, 6, 10], [2], [4], [7], [8], [9]], 12), ([[1, 6, 7], [2], [3], [4], [5], [8], [9], [10]], 2), ([[1, 6, 7, 10], [2], [3], [4], [5], [8], [9]], 6), ([[1, 6, 10], [2], [3], [4], [5], [7], [8], [9]], 4), ([[1, 5, 6, 7], [2], [3], [4], [8], [9], [10]], 2), ([[1, 5, 6, 7, 10], [2], [3], [4], [8], [9]], 6), ([[1, 5, 7], [2], [3], [4], [6], [8], [9], [10]], 4), ([[1, 5, 7, 10], [2], [3], [4], [6], [8], [9]], 12), ([[1, 5, 10], [2], [3], [4], [6], [7], [8], [9]], 2), ([[1, 5, 7, 8], [2], [3], [4], [6], [9], [10]], 6), ([[1, 5, 7, 8, 10], [2], [3], [4], [6], [9]], 6)]
def A3 : List (Tab × ℕ) := [([[1, 5, 7, 8], [2], [3], [4], [6], [9]], 18), ([[1, 5, 7, 8, 9], [2], [3], [4], [6]], 6), ([[1, 5, 7, 9], [2], [3], [4], [6], [8]], 36), ([[1, 5, 6, 7, 9], [2], [3], [4], [8]], 18), ([[1, 6, 7, 9], [2], [3], [4], [5], [8]], 18), ([[1, 4, 6, 7, 9], [2], [3], [5], [8]], 72), ([[1, 5, 7], [2], [3], [4], [6], [8], [9]], 36), ([[1, 5, 6, 7], [2], [3], [4], [8], [9]], 18), ([[1, 6, 7], [2], [3], [4], [5], [8], [9]], 18), ([[1, 4, 6, 7], [2], [3], [5], [8], [9]], 72), ([[1, 5], [2], [3], [4], [6], [7], [8], [9]], 6), ([[1, 5, 9], [2], [3], [4], [6], [7], [8]], 84), ([[1, 9], [2], [3], [4], [5], [6], [7], [8]], 6), ([[1, 4, 9], [2], [3], [5], [6], [7], [8]], 24), ([[1, 5, 6, 9], [2], [3], [4], [7], [8]], 126), ([[1, 6, 9], [2], [3], [4], [5], [7], [8]], 36), ([[1, 4, 6, 9], [2], [3], [5], [7], [8]], 144), ([[1, 5, 6], [2], [3], [4], [7], [8], [9]], 42), ([[1, 6], [2], [3], [4], [5], [7], [8], [9]], 12), ([[1, 4, 6], [2], [3], [5], [7], [8], [9]], 48), ([[1, 4, 5, 6, 9], [2], [3], [7], [8]], 72), ([[1, 4, 5, 6], [2], [3], [7], [8], [9]], 24), ([[1, 3, 5, 6], [2], [4], [7], [8], [9]], 36), ([[1, 3, 5, 6, 9], [2], [4], [7], [8]], 108), ([[1, 3, 5, 9], [2], [4], [6], [7], [8]], 72), ([[1, 3, 4, 5, 9], [2], [6], [7], [8]], 36), ([[1, 4, 5, 9], [2], [3], [6], [7], [8]], 108), ([[1, 2, 4, 5, 9], [3], [6], [7], [8]], 24)]
def A4 : List (Tab × ℕ) := [([[1, 2, 4, 5], [3], [6], [7], [8]], 96), ([[1, 2, 4, 5, 8], [3], [6], [7]], 288), ([[1, 2, 4, 8], [3], [5], [6], [7]], 192), ([[1, 2, 3, 4, 8], [5], [6], [7]], 96), ([[1, 3, 4, 8], [2], [5], [6], [7]], 552), ([[1, 4, 5], [2], [3], [6], [7], [8]], 432), ([[1, 4, 5, 8], [2], [3], [6], [7]], 1296), ([[1, 4, 8], [2], [3], [5], [6], [7]], 864), ([[1, 3, 4, 5], [2], [6], [7], [8]], 144), ([[1, 3, 4, 5, 8], [2], [6], [7]], 432), ([[1, 3, 5], [2], [4], [6], [7], [8]], 288), ([[1, 3, 5, 8], [2], [4], [6], [7]], 864), ([[1, 3, 8], [2], [4], [5], [6], [7]], 144), ([[1, 3, 5, 6], [2], [4], [7], [8]], 432), ([[1, 3, 5, 6, 8], [2], [4], [7]], 432), ([[1, 4, 5, 6], [2], [3], [7], [8]], 288), ([[1, 4, 5, 6, 8], [2], [3], [7]], 288), ([[1, 4, 6], [2], [3], [5], [7], [8]], 576), ([[1, 4], [2], [3], [5], [6], [7], [8]], 96), ([[1, 5], [2], [3], [4], [6], [7], [8]], 336), ([[1, 6], [2], [3], [4], [5], [7], [8]], 144), ([[1], [2], [3], [4], [5], [6], [7], [8]], 24), ([[1, 5, 6], [2], [3], [4], [7], [8]], 504), ([[1, 4, 6, 8], [2], [3], [5], [7]], 576), ([[1, 5, 8], [2], [3], [4], [6], [7]], 864), ([[1, 6, 8], [2], [3], [4], [5], [7]], 144), ([[1, 8], [2], [3], [4], [5], [6], [7]], 192), ([[1, 5, 6, 8], [2], [3], [4], [7]], 504), ([[1, 4, 6, 7], [2], [3], [5], [8]], 288), ([[1, 6, 7], [2], [3], [4], [5], [8]], 72), ([[1, 5, 6, 7], [2], [3], [4], [8]], 72), ([[1, 5, 7], [2], [3], [4], [6], [8]], 144), ([[1, 4, 6, 7, 8], [2], [3], [5]], 96), ([[1, 6, 7, 8], [2], [3], [4], [5]], 24), ([[1, 5, 6, 7, 8], [2], [3], [4]], 24), ([[1, 5, 7, 8], [2], [3], [4], [6]], 72)]
def A5 : List (Tab × ℕ) := [([[1, 5, 7], [2], [3], [4], [6]], 4320), ([[1, 5, 6, 7], [2], [3], [4]], 960), ([[1, 6, 7], [2], [3], [4], [5]], 360), ([[1, 4, 6, 7], [2], [3], [5]], 1440), ([[1, 4, 5, 6, 7], [2], [3]], 480), ([[1, 3, 5, 6, 7], [2], [4]], 720), ([[1, 5], [2], [3], [4], [6], [7]], 4320), ([[1, 5, 6], [2], [3], [4], [7]], 2520), ([[1, 6], [2], [3], [4], [5], [7]], 720), ([[1, 4, 6], [2], [3], [5], [7]], 2880), ([[1, 4, 5, 6], [2], [3], [7]], 1440), ([[1, 3, 5, 6], [2], [4], [7]], 2160), ([[1, 4, 5, 7], [2], [3], [6]], 6480), ([[1], [2], [3], [4], [5], [6], [7]], 960), ([[1, 7], [2], [3], [4], [5], [6]], 3360), ([[1, 4, 7], [2], [3], [5], [6]], 10080), ([[1, 3, 5, 7], [2], [4], [6]], 4320), ([[1, 4, 5], [2], [3], [6], [7]], 6480), ([[1, 4], [2], [3], [5], [6], [7]], 4320), ([[1, 3], [2], [4], [5], [6], [7]], 720), ([[1, 3, 5], [2], [4], [6], [7]], 4320), ([[1, 3, 4, 5, 7], [2], [6]], 2160), ([[1, 3, 4, 5], [2], [6], [7]], 2160), ([[1, 2, 4, 5, 7], [3], [6]], 1440), ([[1, 2, 4, 5], [3], [6], [7]], 1440), ([[1, 3, 7], [2], [4], [5], [6]], 5520), ([[1, 2, 7], [3], [4], [5], [6]], 480), ([[1, 3, 4, 7], [2], [5], [6]], 8280), ([[1, 2, 4, 7], [3], [5], [6]], 2880), ([[1, 3, 4], [2], [5], [6], [7]], 2760), ([[1, 2, 4], [3], [5], [6], [7]], 960), ([[1, 2, 3, 4, 7], [5], [6]], 1440), ([[1, 2, 3, 4], [5], [6], [7]], 480), ([[1, 2, 3, 7], [4], [5], [6]], 1680)]
def A6 : List (Tab × ℕ) := [([[1, 2, 3], [4], [5], [6]], 10080), ([[1, 2, 3, 6], [4], [5]], 30240), ([[1, 2, 6], [3], [4], [5]], 20880), ([[1, 2, 3, 4], [5], [6]], 8640), ([[1, 2, 3, 4, 6], [5]], 8640), ([[1, 2, 4], [3], [5], [6]], 17280), ([[1, 2], [3], [4], [5], [6]], 2880), ([[1, 3], [2], [4], [5], [6]], 33120), ([[1, 3, 4], [2], [5], [6]], 49680), ([[1, 2, 4, 6], [3], [5]], 17280), ([[1, 3, 6], [2], [4], [5]], 73440), ([[1, 3, 4, 6], [2], [5]], 49680), ([[1, 6], [2], [3], [4], [5]], 42480), ([[1, 2, 4, 5], [3], [6]], 8640), ([[1, 2, 4, 5, 6], [3]], 2880), ([[1, 3, 4, 5], [2], [6]], 12960), ([[1, 3, 4, 5, 6], [2]], 4320), ([[1, 3, 5], [2], [4], [6]], 25920), ([[1, 4], [2], [3], [5], [6]], 60480), ([[1], [2], [3], [4], [5], [6]], 20160), ([[1, 4, 5], [2], [3], [6]], 38880), ([[1, 3, 5, 6], [2], [4]], 12960), ([[1, 4, 6], [2], [3], [5]], 60480), ([[1, 4, 5, 6], [2], [3]], 15840), ([[1, 5], [2], [3], [4], [6]], 24480), ([[1, 5, 6], [2], [3], [4]], 12960)]
def A7 : List (Tab × ℕ) := [([[1, 5], [2], [3], [4]], 438480), ([[1, 4, 5], [2], [3]], 211680), ([[1], [2], [3], [4], [5]], 287280), ([[1, 4], [2], [3], [5]], 383040), ([[1, 3, 4, 5], [2]], 146160), ([[1, 3, 5], [2], [4]], 514080), ([[1, 2, 4, 5], [3]], 60480), ([[1, 3, 4], [2], [5]], 347760), ([[1, 3], [2], [4], [5]], 514080), ([[1, 2, 4], [3], [5]], 120960), ([[1, 2, 3, 4, 5]], 20160), ([[1, 2, 3, 4], [5]], 60480), ([[1, 2, 3, 5], [4]], 211680), ([[1, 2, 5], [3], [4]], 317520), ([[1, 2, 3], [4], [5]], 211680), ([[1, 2], [3], [4], [5]], 146160)]
def A8 : List (Tab × ℕ) := [([[1, 2], [3], [4]], 2540160), ([[1], [2], [3], [4]], 3064320), ([[1, 2, 3], [4]], 1693440), ([[1, 2, 4], [3]], 2540160), ([[1, 4], [2], [3]], 3709440), ([[1, 2, 3, 4]], 725760), ([[1, 3], [2], [4]], 3628800), ([[1, 3, 4], [2]], 2056320)]
def B1 : List (Tab × ℕ) := [([[1, 2, 3, 7, 10, 11], [4], [5], [6], [8], [9]], 1), ([[1, 2, 3, 7, 10], [4], [5], [6], [8], [9], [11]], 2), ([[1, 2, 3, 7, 9, 10], [4], [5], [6], [8], [11]], 2), ([[1, 2, 3, 9, 10], [4], [5], [6], [7], [8], [11]], 1), ([[1, 2, 3, 6, 9, 10], [4], [5], [7], [8], [11]], 3), ([[1, 2, 6, 9, 10], [3], [4], [5], [7], [8], [11]], 3)]
def B2 : List (Tab × ℕ) := [([[1, 2, 6, 9, 10], [3], [4], [5], [7], [8]], 6), ([[1, 2, 6, 9], [3], [4], [5], [7], [8], [10]], 12), ([[1, 2, 6, 8, 9], [3], [4], [5], [7], [10]], 12), ([[1, 2, 8, 9], [3], [4], [5], [6], [7], [10]], 6), ([[1, 2, 5, 8, 9], [3], [4], [6], [7], [10]], 18), ([[1, 5, 8, 9], [2], [3], [4], [6], [7], [10]], 6), ([[1, 2, 3, 6, 9, 10], [4], [5], [7], [8]], 6), ([[1, 2, 3, 6, 9], [4], [5], [7], [8], [10]], 12), ([[1, 2, 3, 6, 8, 9], [4], [5], [7], [10]], 12), ([[1, 2, 3, 8, 9], [4], [5], [6], [7], [10]], 10), ([[1, 2, 3, 5, 8, 9], [4], [6], [7], [10]], 6), ([[1, 2, 3, 9, 10], [4], [5], [6], [7], [8]], 2), ([[1, 2, 3, 9], [4], [5], [6], [7], [8], [10]], 4), ([[1, 2, 3, 7, 9, 10], [4], [5], [6], [8]], 4), ([[1, 2, 3, 7, 9], [4], [5], [6], [8], [10]], 8), ([[1, 2, 3, 7, 8, 9], [4], [5], [6], [10]], 2), ([[1, 2, 3, 7, 10], [4], [5], [6], [8], [9]], 4), ([[1, 2, 3, 7], [4], [5], [6], [8], [9], [10]], 2)]
def B3 : List (Tab × ℕ) := [([[1, 2, 3, 7], [4], [5], [6], [8], [9]], 18), ([[1, 2, 3], [4], [5], [6], [7], [8], [9]], 6), ([[1, 2, 3, 6], [4], [5], [7], [8], [9]], 18), ([[1, 2, 6], [3], [4], [5], [7], [8], [9]], 18), ([[1, 2, 3, 7, 9], [4], [5], [6], [8]], 24), ([[1, 2, 3, 9], [4], [5], [6], [7], [8]], 12), ([[1, 2, 3, 6, 9], [4], [5], [7], [8]], 36), ([[1, 2, 6, 9], [3], [4], [5], [7], [8]], 36), ([[1, 2, 3, 7, 8, 9], [4], [5], [6]], 6), ([[1, 2, 3, 7, 8], [4], [5], [6], [9]], 72), ([[1, 2, 3, 6, 7, 8], [4], [5], [9]], 18), ([[1, 2, 6, 7, 8], [3], [4], [5], [9]], 18), ([[1, 2, 3, 8], [4], [5], [6], [7], [9]], 60), ([[1, 2, 3, 6, 8], [4], [5], [7], [9]], 72), ([[1, 2, 6, 8], [3], [4], [5], [7], [9]], 72), ([[1, 2, 3, 8, 9], [4], [5], [6], [7]], 30), ([[1, 2, 3, 6, 8, 9], [4], [5], [7]], 36), ([[1, 2, 6, 8, 9], [3], [4], [5], [7]], 36), ([[1, 2, 8], [3], [4], [5], [6], [7], [9]], 36), ([[1, 2, 8, 9], [3], [4], [5], [6], [7]], 18), ([[1, 2, 3, 5, 8, 9], [4], [6], [7]], 18), ([[1, 2, 3, 5, 8], [4], [6], [7], [9]], 36), ([[1, 2, 3, 5, 7, 8], [4], [6], [9]], 36), ([[1, 2, 3, 4, 7, 8], [5], [6], [9]], 6), ([[1, 2, 4, 7, 8], [3], [5], [6], [9]], 54), ([[1, 2, 7, 8], [3], [4], [5], [6], [9]], 90), ([[1, 2, 5, 7, 8], [3], [4], [6], [9]], 108), ([[1, 2, 5, 8], [3], [4], [6], [7], [9]], 108), ([[1, 2, 5, 8, 9], [3], [4], [6], [7]], 54), ([[1, 5, 8, 9], [2], [3], [4], [6], [7]], 18), ([[1, 5, 8], [2], [3], [4], [6], [7], [9]], 36), ([[1, 5, 7, 8], [2], [3], [4], [6], [9]], 36), ([[1, 7, 8], [2], [3], [4], [5], [6], [9]], 18), ([[1, 4, 7, 8], [2], [3], [5], [6], [9]], 60)]
def B4 : List (Tab × ℕ) := [([[1, 4, 7, 8], [2], [3], [5], [6]], 240), ([[1, 4, 7], [2], [3], [5], [6], [8]], 480), ([[1, 4, 6, 7], [2], [3], [5], [8]], 480), ([[1, 6, 7], [2], [3], [4], [5], [8]], 384), ([[1, 3, 6, 7], [2], [4], [5], [8]], 288), ([[1, 7, 8], [2], [3], [4], [5], [6]], 72), ([[1, 7], [2], [3], [4], [5], [6], [8]], 144), ([[1, 5, 7, 8], [2], [3], [4], [6]], 144), ([[1, 5, 7], [2], [3], [4], [6], [8]], 288), ([[1, 5, 6, 7], [2], [3], [4], [8]], 72), ([[1, 5, 8], [2], [3], [4], [6], [7]], 144), ([[1, 5], [2], [3], [4], [6], [7], [8]], 72), ([[1, 2, 5, 8], [3], [4], [6], [7]], 432), ([[1, 2, 5, 7, 8], [3], [4], [6]], 432), ([[1, 2, 7, 8], [3], [4], [5], [6]], 360), ([[1, 2, 4, 7, 8], [3], [5], [6]], 216), ([[1, 2, 5], [3], [4], [6], [7], [8]], 216), ([[1, 2, 5, 7], [3], [4], [6], [8]], 864), ([[1, 2, 7], [3], [4], [5], [6], [8]], 720), ([[1, 2, 4, 7], [3], [5], [6], [8]], 432), ([[1, 2, 5, 6, 7], [3], [4], [8]], 216), ([[1, 2, 6, 7], [3], [4], [5], [8]], 864), ([[1, 2, 4, 6, 7], [3], [5], [8]], 432), ([[1, 2, 3, 6, 7], [4], [5], [8]], 456), ([[1, 2, 3, 4, 7, 8], [5], [6]], 24), ([[1, 2, 3, 4, 7], [5], [6], [8]], 48), ([[1, 2, 3, 4, 6, 7], [5], [8]], 48), ([[1, 2, 3, 5, 7, 8], [4], [6]], 144), ([[1, 2, 3, 5, 7], [4], [6], [8]], 288), ([[1, 2, 3, 5, 6, 7], [4], [8]], 72), ([[1, 2, 3, 5, 8], [4], [6], [7]], 144), ([[1, 2, 3, 5], [4], [6], [7], [8]], 72), ([[1, 2, 3, 7], [4], [5], [6], [8]], 552), ([[1, 2, 3, 7, 8], [4], [5], [6]], 288), ([[1, 2, 8], [3], [4], [5], [6], [7]], 144), ([[1, 2], [3], [4], [5], [6], [7], [8]], 72), ([[1, 2, 6, 8], [3], [4], [5], [7]], 288), ([[1, 2, 6, 7, 8], [3], [4], [5]], 72), ([[1, 2, 3, 6, 8], [4], [5], [7]], 288), ([[1, 2, 3, 6, 7, 8], [4], [5]], 72), ([[1, 2, 3, 8], [4], [5], [6], [7]], 240), ([[1, 2, 6], [3], [4], [5], [7], [8]], 216), ([[1, 2, 3, 6], [4], [5], [7], [8]], 216), ([[1, 2, 3], [4], [5], [6], [7], [8]], 144)]
def B5 : List (Tab × ℕ) := [([[1, 2, 3], [4], [5], [6], [7]], 1800), ([[1, 2], [3], [4], [5], [6], [7]], 2160), ([[1, 2, 3, 6], [4], [5], [7]], 4200), ([[1, 2, 3, 5], [4], [6], [7]], 1080), ([[1, 2, 5], [3], [4], [6], [7]], 3240), ([[1, 2, 6], [3], [4], [5], [7]], 8280), ([[1, 5], [2], [3], [4], [6], [7]], 1080), ([[1, 2, 3, 7], [4], [5], [6]], 2520), ([[1, 2, 7], [3], [4], [5], [6]], 3600), ([[1, 2, 3, 6, 7], [4], [5]], 2280), ([[1, 2, 3, 5, 6, 7], [4]], 360), ([[1, 2, 5, 6, 7], [3], [4]], 1080), ([[1, 2, 3, 5, 7], [4], [6]], 1440), ([[1, 2, 5, 7], [3], [4], [6]], 4320), ([[1, 2, 6, 7], [3], [4], [5]], 4320), ([[1, 5, 6, 7], [2], [3], [4]], 360), ([[1, 5, 7], [2], [3], [4], [6]], 1440), ([[1], [2], [3], [4], [5], [6], [7]], 360), ([[1, 7], [2], [3], [4], [5], [6]], 720), ([[1, 2, 3, 4], [5], [6], [7]], 120), ([[1, 2, 4], [3], [5], [6], [7]], 1080), ([[1, 2, 3, 4, 7], [5], [6]], 240), ([[1, 2, 4, 7], [3], [5], [6]], 2160), ([[1, 2, 3, 5, 6], [4], [7]], 2040), ([[1, 2, 3, 4, 5, 6], [7]], 120), ([[1, 2, 4, 5, 6], [3], [7]], 1080), ([[1, 2, 3, 4, 6], [5], [7]], 480), ([[1, 2, 4, 6], [3], [5], [7]], 4320), ([[1, 2, 3, 4, 6, 7], [5]], 240), ([[1, 2, 4, 6, 7], [3], [5]], 2160), ([[1, 2, 5, 6], [3], [4], [7]], 6480), ([[1, 3, 5, 6], [2], [4], [7]], 2880), ([[1, 5, 6], [2], [3], [4], [7]], 4920), ([[1, 4, 5, 6], [2], [3], [7]], 1200), ([[1, 3, 6], [2], [4], [5], [7]], 2880), ([[1, 6], [2], [3], [4], [5], [7]], 3840), ([[1, 4, 6], [2], [3], [5], [7]], 4800), ([[1, 4], [2], [3], [5], [6], [7]], 1200), ([[1, 3, 6, 7], [2], [4], [5]], 1440), ([[1, 6, 7], [2], [3], [4], [5]], 1920), ([[1, 4, 6, 7], [2], [3], [5]], 2400), ([[1, 4, 7], [2], [3], [5], [6]], 2400)]
def B6 : List (Tab × ℕ) := [([[1, 4], [2], [3], [5], [6]], 21600), ([[1, 4, 6], [2], [3], [5]], 28800), ([[1, 6], [2], [3], [4], [5]], 23040), ([[1, 3, 6], [2], [4], [5]], 17280), ([[1, 4, 5, 6], [2], [3]], 7200), ([[1, 5, 6], [2], [3], [4]], 29520), ([[1, 3, 5, 6], [2], [4]], 17280), ([[1, 2, 5, 6], [3], [4]], 38880), ([[1], [2], [3], [4], [5], [6]], 13680), ([[1, 3], [2], [4], [5], [6]], 8640), ([[1, 4, 5], [2], [3], [6]], 43920), ([[1, 5], [2], [3], [4], [6]], 56880), ([[1, 3, 5], [2], [4], [6]], 34560), ([[1, 2, 5], [3], [4], [6]], 71280), ([[1, 3, 4, 5], [2], [6]], 8640), ([[1, 2, 4, 5], [3], [6]], 32400), ([[1, 2, 4, 6], [3], [5]], 25920), ([[1, 2, 4, 5, 6], [3]], 6480), ([[1, 2, 3, 5, 6], [4]], 12240), ([[1, 2, 3, 4, 6], [5]], 2880), ([[1, 2, 3, 4, 5, 6]], 720), ([[1, 2, 4], [3], [5], [6]], 19440), ([[1, 2, 3, 5], [4], [6]], 22320), ([[1, 2, 3, 4], [5], [6]], 2160), ([[1, 2, 3, 4, 5], [6]], 4320), ([[1, 2, 6], [3], [4], [5]], 45360), ([[1, 2, 3, 6], [4], [5]], 20880), ([[1, 2], [3], [4], [5], [6]], 32400), ([[1, 2, 3], [4], [5], [6]], 16560)]
def B7 : List (Tab × ℕ) := [([[1, 2, 3], [4], [5]], 120960), ([[1, 2], [3], [4], [5]], 332640), ([[1], [2], [3], [4], [5]], 257040), ([[1, 2, 3, 5], [4]], 126000), ([[1, 2, 5], [3], [4]], 408240), ([[1, 5], [2], [3], [4]], 367920), ([[1, 2, 3, 4, 5]], 30240), ([[1, 2, 3, 4], [5]], 100800), ([[1, 2, 4], [3], [5]], 408240), ([[1, 3], [2], [4], [5]], 181440), ([[1, 2, 4, 5], [3]], 226800), ([[1, 3, 4, 5], [2]], 60480), ([[1, 3, 5], [2], [4]], 241920), ([[1, 3, 4], [2], [5]], 257040), ([[1, 4], [2], [3], [5]], 564480), ([[1, 4, 5], [2], [3]], 307440)]
def B8 : List (Tab × ℕ) := [([[1, 4], [2], [3]], 3709440), ([[1, 3, 4], [2]], 2056320), ([[1], [2], [3], [4]], 3064320), ([[1, 3], [2], [4]], 3628800), ([[1, 2, 3], [4]], 1693440), ([[1, 2, 4], [3]], 2540160), ([[1, 2, 3, 4]], 725760), ([[1, 2], [3], [4]], 2540160)]

theorem hA1 : step [(T₁, 1)] = A1 := by decide +kernel
theorem hA2 : step A1 = A2 := by decide +kernel
theorem hA3 : step A2 = A3 := by decide +kernel
theorem hA4 : step A3 = A4 := by decide +kernel
theorem hA5 : step A4 = A5 := by decide +kernel
theorem hA6 : step A5 = A6 := by decide +kernel
theorem hA7 : step A6 = A7 := by decide +kernel
theorem hA8 : step A7 = A8 := by decide +kernel
theorem hB1 : step [(T₂, 1)] = B1 := by decide +kernel
theorem hB2 : step B1 = B2 := by decide +kernel
theorem hB3 : step B2 = B3 := by decide +kernel
theorem hB4 : step B3 = B4 := by decide +kernel
theorem hB5 : step B4 = B5 := by decide +kernel
theorem hB6 : step B5 = B6 := by decide +kernel
theorem hB7 : step B6 = B7 := by decide +kernel
theorem hB8 : step B7 = B8 := by decide +kernel


/-! ### Semantic sanity certificates
Every deletion performed in the certificate removed exactly one cell (an exhausted fuel
budget would leave the size unchanged), and every intermediate minor is a standard Young
tableau of the expected size.  Hence `del` agreed with the jeu de taquin process on every
tableau reached from `T₁` and `T₂`. -/
theorem A1_ok : A1.all (fun p => decide (IsSYT 11 p.1) && size p.1 == 11) = true := by decide +kernel
theorem A2_ok : A2.all (fun p => decide (IsSYT 10 p.1) && size p.1 == 10) = true := by decide +kernel
theorem A3_ok : A3.all (fun p => decide (IsSYT 9 p.1) && size p.1 == 9) = true := by decide +kernel
theorem A4_ok : A4.all (fun p => decide (IsSYT 8 p.1) && size p.1 == 8) = true := by decide +kernel
theorem A5_ok : A5.all (fun p => decide (IsSYT 7 p.1) && size p.1 == 7) = true := by decide +kernel
theorem A6_ok : A6.all (fun p => decide (IsSYT 6 p.1) && size p.1 == 6) = true := by decide +kernel
theorem A7_ok : A7.all (fun p => decide (IsSYT 5 p.1) && size p.1 == 5) = true := by decide +kernel
theorem A8_ok : A8.all (fun p => decide (IsSYT 4 p.1) && size p.1 == 4) = true := by decide +kernel
theorem B1_ok : B1.all (fun p => decide (IsSYT 11 p.1) && size p.1 == 11) = true := by decide +kernel
theorem B2_ok : B2.all (fun p => decide (IsSYT 10 p.1) && size p.1 == 10) = true := by decide +kernel
theorem B3_ok : B3.all (fun p => decide (IsSYT 9 p.1) && size p.1 == 9) = true := by decide +kernel
theorem B4_ok : B4.all (fun p => decide (IsSYT 8 p.1) && size p.1 == 8) = true := by decide +kernel
theorem B5_ok : B5.all (fun p => decide (IsSYT 7 p.1) && size p.1 == 7) = true := by decide +kernel
theorem B6_ok : B6.all (fun p => decide (IsSYT 6 p.1) && size p.1 == 6) = true := by decide +kernel
theorem B7_ok : B7.all (fun p => decide (IsSYT 5 p.1) && size p.1 == 5) = true := by decide +kernel
theorem B8_ok : B8.all (fun p => decide (IsSYT 4 p.1) && size p.1 == 4) = true := by decide +kernel

theorem hAB : A8.Perm B8 := by decide +kernel

theorem minors_eq : minors 8 T₁ = minors 8 T₂ := by
  have e₁ : minors 8 T₁ = den 0 A8 := by
    calc minors 8 T₁ = den 8 [(T₁, 1)] := minors_eq_den 8 T₁
    _ = den 7 A1 := chain hA1
    _ = den 6 A2 := chain hA2
    _ = den 5 A3 := chain hA3
    _ = den 4 A4 := chain hA4
    _ = den 3 A5 := chain hA5
    _ = den 2 A6 := chain hA6
    _ = den 1 A7 := chain hA7
    _ = den 0 A8 := chain hA8
  have e₂ : minors 8 T₂ = den 0 B8 := by
    calc minors 8 T₂ = den 8 [(T₂, 1)] := minors_eq_den 8 T₂
    _ = den 7 B1 := chain hB1
    _ = den 6 B2 := chain hB2
    _ = den 5 B3 := chain hB3
    _ = den 4 B4 := chain hB4
    _ = den 3 B5 := chain hB5
    _ = den 2 B6 := chain hB6
    _ = den 1 B7 := chain hB7
    _ = den 0 B8 := chain hB8
  rw [e₁, e₂]; exact den_perm 0 hAB

/-- **MathDB 359279 is false**: the multiset of `8`-minors does not determine a standard
Young tableau of size `12 = 8 + 4`. -/
theorem not_conjecture : ¬ Conjecture := fun h =>
  T₁_ne_T₂ (h 8 12 (by norm_num) (by norm_num) T₁ T₂ T₁_syt T₂_syt minors_eq)

end TabMinors

#print axioms TabMinors.not_conjecture
