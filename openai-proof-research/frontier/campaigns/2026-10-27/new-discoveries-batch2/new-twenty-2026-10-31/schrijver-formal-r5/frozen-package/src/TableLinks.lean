import MaskSemantics
import Enumeration
import Mathlib.Order.Fin.Basic
namespace Schrijver
set_option autoImplicit false

def tableLinkCheck (a : Array ℕ) (f : ℕ → ℕ) (start count : ℕ) : Bool :=
  ((List.range count).map (start + ·)).all fun i =>
    decide (f i = a[i]!) && decide (i+1 < a.size → f i < f (i+1))

theorem tableLinkCheck_sound {a : Array ℕ} {f : ℕ → ℕ} {start count i : ℕ}
    (h : tableLinkCheck a f start count = true) (hi : start ≤ i ∧ i < start+count) :
    f i = a[i]! ∧ (i+1 < a.size → f i < f (i+1)) := by
  have hm : i ∈ (List.range count).map (start + ·) := by
    apply List.mem_map.mpr
    exact ⟨i-start, List.mem_range.mpr (by omega), by omega⟩
  have hh := List.all_eq_true.mp h i hm
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using hh

theorem bounded_strictMono {N : ℕ} (f : ℕ → ℕ)
    (h : ∀ i, i+1 < N → f i < f (i+1)) :
    StrictMono (fun i : Fin N => f i.val) := by
  intro a b hab
  have chain : ∀ j, a.val < j → j < N → f a.val < f j := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hj hn
      by_cases he : a.val = j
      · subst j; exact h a.val hn
      · exact (ih (by omega) (by omega)).trans (h j hn)
  exact chain b.val hab b.isLt

theorem table_coverage_from_links {n k N : ℕ} {a : Array ℕ} {f : ℕ → ℕ}
    (hs : a.size = N) (hl : ∀ i : Fin N, f i.val = a[i.val]!)
    (hc : StoredEnumerationComplete n k a.toList) :
    ∀ v : Vertex n k, ∃ i : Fin N, f i.val = encode v.val := by
  intro v
  have hm := stored_table_covers hc v
  have hm' : encode v.val ∈ a := by simpa using hm
  obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hm'
  exact ⟨⟨i, by omega⟩, (hl ⟨i, by omega⟩).trans (by simpa [hi] using he)⟩
theorem table_valid_from_links {n k N : ℕ} {a : Array ℕ} {f : ℕ → ℕ}
    (hs : a.size = N) (hl : ∀ i : Fin N, f i.val = a[i.val]!)
    (hv : a.toList.all (validMask n k) = true) :
    ∀ i : Fin N, validMask n k (f i.val) = true := by
  intro i
  rw [hl i]
  have hi : i.val < a.size := by rw [hs]; exact i.isLt
  apply List.all_eq_true.mp hv
  simpa only [getElem!_pos a i.val hi] using (Array.getElem_mem_toList hi)
end Schrijver
