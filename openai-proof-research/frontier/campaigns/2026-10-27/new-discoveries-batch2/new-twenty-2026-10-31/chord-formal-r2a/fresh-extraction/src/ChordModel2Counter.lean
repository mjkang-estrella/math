import ChordModel2Orbit
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
namespace Chord.Model2
open Equiv Function

def rawPerm {size} (f : Fin size ≃ Fin size) (i : Nat) : Nat :=
  if h : i < size then (f ⟨i,h⟩).val else i

theorem rawPerm_lt {size} (f : Fin size ≃ Fin size) (i : Nat) (hi : i < size) :
    rawPerm f i < size := by
  simp only [rawPerm, dite_eq_left hi]
  exact (f ⟨i,hi⟩).isLt

theorem rawPerm_iterate {size} (f : Fin size ≃ Fin size) (i : Fin size) (k : Nat) :
    ((rawPerm f)^[k]) i.val = ((f : Fin size → Fin size)^[k] i).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih]
    simp only [rawPerm, dite_eq_left ((f : Fin size → Fin size)^[k] i).isLt]

theorem sameCycle_iterate_iff {size} (f : Fin size ≃ Fin size) (i j : Fin size) :
    Equiv.Perm.SameCycle f i j ↔ ∃ k, ((f : Fin size → Fin size)^[k]) i = j := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, by simpa only [Equiv.Perm.coe_pow] using hk⟩
  · rintro ⟨k,rfl⟩
    rw [← Equiv.Perm.coe_pow]
    exact (Equiv.Perm.SameCycle.refl f i).pow_right

/-- The bounded minimum in the frozen specification is the genuine orbit minimum. -/
theorem bounded_minimum_iff {size} (f : Fin size ≃ Fin size) (i : Fin size) :
    (∀ k : Fin (size+1), i ≤ Nat.rec i (fun _ x => f x) k.val) ↔
      ∀ j, Equiv.Perm.SameCycle f i j → i ≤ j := by
  have hr (k : Nat) : Nat.rec i (fun _ x => f x) k = (f^[k]) i := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [iterate_succ_apply', ih]
  constructor
  · intro h j hj
    obtain ⟨k,rfl⟩ := (sameCycle_iterate_iff f i j).mp hj
    have hper : i ∈ periodicPts (f : Fin size → Fin size) :=
      (injective_iff_periodicPts_eq_univ.mp f.injective) ▸ Set.mem_univ i
    let p := minimalPeriod (f : Fin size → Fin size) i
    have hp : 0 < p := minimalPeriod_pos_of_mem_periodicPts hper
    have hpbound : p ≤ size := by simpa only [Fintype.card_fin] using (minimalPeriod_le_card (f := (f : Fin size → Fin size)) (x := i))
    have hk : k % p < size+1 := by have := Nat.mod_lt k hp; omega
    have hh := h ⟨k%p,hk⟩
    rw [hr, iterate_mod_minimalPeriod_eq] at hh
    exact hh
  · intro h k
    rw [hr]
    apply h
    exact (sameCycle_iterate_iff f i _).mpr ⟨k.val,rfl⟩
end Chord.Model2
