import SSA5.Checks

/-!
# Transfer recursion for `C_n(S)` with `m = 5`

For `n ≥ 5`, a sequence of length `n + 1` lies in `C_{n+1}(S)` iff its initial segment lies in
`C_n(S)` and its last window lies in `S`; the last window is the shift of the previous last
window by the new letter.  Summing a weight of the last window over `C_{n+1}(S)` therefore
equals the transfer-matrix image of the corresponding sum over `C_n(S)`.
-/

namespace SSA

/-- The last length-five window of a sequence of length `n ≥ 5`. -/
def lw {n : ℕ} (x : Fin n → Base) (h : 5 ≤ n) : Word 5 :=
  window 5 x (n - 5) (by omega)

/-- Shift a length-five word left by one letter and append `c`. -/
def shift (w : Word 5) (c : Base) : Word 5 := ![w 1, w 2, w 3, w 4, c]

theorem window_init {n : ℕ} (x : Fin (n + 1) → Base) (i : ℕ) (h : i + 5 ≤ n) :
    window 5 x i (by omega) = window 5 (Fin.init x) i h := by
  funext j
  simp only [window, Fin.init]
  rfl

theorem lw_succ {n : ℕ} (x : Fin (n + 1) → Base) (h : 5 ≤ n) :
    lw x (by omega) = shift (lw (Fin.init x) h) (x (Fin.last n)) := by
  funext j
  fin_cases j <;>
  · simp only [lw, window, shift, Fin.init]
    simp
    congr 1
    ext
    simp
    omega

theorem mem_code_succ {n : ℕ} (S : Set (Word 5)) (h : 5 ≤ n) (x : Fin (n + 1) → Base) :
    x ∈ code 5 (n + 1) S ↔ Fin.init x ∈ code 5 n S ∧ lw x (by omega) ∈ S := by
  classical
  simp only [code, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    refine ⟨fun i hi => ?_, hx _ _⟩
    rw [← window_init x i hi]
    exact hx i _
  · rintro ⟨hinit, hlast⟩ i hi
    by_cases hi' : i + 5 ≤ n
    · rw [window_init x i hi']
      exact hinit i hi'
    · have : i = n + 1 - 5 := by omega
      subst this
      exact hlast

theorem lw_snoc {n : ℕ} (y : Fin n → Base) (c : Base) (h : 5 ≤ n) :
    lw (Fin.snoc (α := fun _ => Base) y c) (by omega) = shift (lw y h) c := by
  rw [lw_succ _ h, Fin.init_snoc, Fin.snoc_last]

open Classical in
/-- The transfer identity for last-window weights. -/
theorem sum_code_succ {n : ℕ} (S : Set (Word 5)) (h : 5 ≤ n) (g : Word 5 → ℕ) :
    ∑ x ∈ code 5 (n + 1) S, g (lw x (by omega)) =
      ∑ y ∈ code 5 n S, ∑ c : Base,
        (if shift (lw y h) c ∈ S then g (shift (lw y h) c) else 0) := by
  classical
  have hL : ∑ x ∈ code 5 (n + 1) S, g (lw x (by omega)) =
      ∑ x : Fin (n + 1) → Base, (if x ∈ code 5 (n + 1) S then g (lw x (by omega)) else 0) := by
    rw [Finset.sum_ite_mem]; simp
  have hR : ∑ y ∈ code 5 n S, ∑ c : Base,
        (if shift (lw y h) c ∈ S then g (shift (lw y h) c) else 0) =
      ∑ y : Fin n → Base, (if y ∈ code 5 n S then ∑ c : Base,
        (if shift (lw y h) c ∈ S then g (shift (lw y h) c) else 0) else 0) := by
    rw [Finset.sum_ite_mem]; simp
  rw [hL, hR, ← (Fin.snocEquiv (fun _ => Base)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ code 5 n S
  · simp only [hy, ↓reduceIte]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hm : Fin.snoc (α := fun _ => Base) y c ∈ code 5 (n + 1) S ↔ shift (lw y h) c ∈ S := by
      rw [mem_code_succ S h, Fin.init_snoc, lw_snoc y c h]; simp [hy]
    split_ifs with h1 h2 h2
    · exact congrArg g (lw_snoc y c h)
    · exact absurd (hm.1 h1) h2
    · exact absurd (hm.2 h2) h1
    · rfl
  · simp only [hy, ↓reduceIte]
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with hh
    · have := ((mem_code_succ S h _).1 hh).1
      exact absurd (Fin.init_snoc (α := fun _ => Base) (p := y) (x := c) ▸ this) hy
    · rfl

end SSA
