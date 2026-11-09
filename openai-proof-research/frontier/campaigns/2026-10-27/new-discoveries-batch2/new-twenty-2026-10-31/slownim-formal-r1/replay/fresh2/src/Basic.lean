import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
namespace SlowNim360653
abbrev Pos (n : ℕ) := Fin n → ℕ
def mass {n} (x : Pos n) : ℕ := ∑ i, x i
def Terminal {n} (x : Pos n) : Prop := ∃ i j, i ≠ j ∧ x i = 0 ∧ x j = 0
instance {n} (x : Pos n) : Decidable (Terminal x) := inferInstanceAs (Decidable (∃ i j, i ≠ j ∧ x i = 0 ∧ x j = 0))
def Legal {n} (x : Pos n) (i : Fin n) := ∀ j, j ≠ i → 0 < x j
def move {n} (x : Pos n) (i : Fin n) : Pos n := fun j => if j = i then x j else x j - 1
structure Strategy (n : ℕ) where
  choose : Pos n → Fin n
  valid : ∀ x, ¬ Terminal x → Legal x (choose x)
abbrev Profile (n l : ℕ) := Fin l → Strategy n

theorem mass_move {n} (x : Pos n) (i : Fin n) (h : Legal x i) :
    mass (move x i) + (n-1) = mass x := by
  have point : ∀ j, move x i j + (if j = i then 0 else 1) = x j := by
    intro j
    by_cases e : j = i
    · simp [move, e]
    · have := h j e; simp [move, e]; omega
  have count : (∑ j : Fin n, if j = i then 0 else 1 : ℕ) = n-1 := by
    simp [Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem]
  rw [← count, mass, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => point j)

def values {n} (x : Pos n) : Finset ℕ := Finset.univ.image x
lemma values_nonempty {n} (hn : 2 ≤ n) (x : Pos n) : (values x).Nonempty :=
  ⟨x ⟨0, by omega⟩, Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩⟩
def multiples {n} (l : ℕ) (x : Pos n) := (values x).filter (fun v => v % l = 0)
def pivotValue {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n) : ℕ :=
  if h : (multiples l x).Nonempty then (multiples l x).min' h
  else (values x).max' (values_nonempty hn x)
lemma pivot_mem {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n) : pivotValue hn l x ∈ values x := by
  unfold pivotValue
  split
  · exact (Finset.mem_filter.mp (Finset.min'_mem (multiples l x) _)).1
  · exact Finset.max'_mem _ _
def pivots {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n) :=
  Finset.univ.filter (fun i => x i = pivotValue hn l x)
lemma pivots_nonempty {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n) : (pivots hn l x).Nonempty := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (pivot_mem hn l x)
  exact ⟨i, by simp [pivots, hi]⟩
def gm {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n) : Fin n :=
  (pivots hn l x).max' (pivots_nonempty hn l x)
lemma gm_value {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n) :
    x (gm hn l x) = pivotValue hn l x :=
  (Finset.mem_filter.mp (Finset.max'_mem (pivots hn l x) _)).2
lemma gm_rightmost {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n) (i : Fin n)
    (hi : x i = pivotValue hn l x) : i ≤ gm hn l x :=
  Finset.le_max' _ _ (by simp [pivots, hi])
lemma gm_zero {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n) (j : Fin n) (hj : x j = 0) :
    x (gm hn l x) = 0 := by
  have hz : 0 ∈ multiples l x := by simp [multiples, values]; exact ⟨j, hj⟩
  rw [gm_value hn l x, pivotValue, dite_eq_left ⟨0, hz⟩]
  exact Nat.eq_zero_of_le_zero (Finset.min'_le _ _ hz)
theorem gm_legal {n} (hn : 2 ≤ n) (l : ℕ) (x : Pos n) (h : ¬ Terminal x) : Legal x (gm hn l x) := by
  intro j hj
  by_contra hz
  have hjz : x j = 0 := by omega
  exact h ⟨j, gm hn l x, hj, hjz, gm_zero hn l x j hjz⟩
def GM {n} (hn : 2 ≤ n) (l : ℕ) : Strategy n := ⟨gm hn l, gm_legal hn l⟩
def GMProfile {n} (hn : 2 ≤ n) (l : ℕ) : Profile n l := fun _ => GM hn l
end SlowNim360653
