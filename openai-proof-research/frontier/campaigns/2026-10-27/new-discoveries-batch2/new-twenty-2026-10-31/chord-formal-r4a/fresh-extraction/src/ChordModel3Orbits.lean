import ChordModel2Final
import Mathlib.Data.Fintype.Quotient
namespace Chord.Model3
open Equiv
attribute [local instance] Classical.propDecidable

/-- All permutation orbits, including singleton orbits. -/
noncomputable def orbitCount {α : Type*} [Fintype α] (f : Perm α) : Nat :=
  Nat.card (Quotient (Perm.SameCycle.setoid f))

private theorem minimum_exists {size} (f : Perm (Fin size)) (x : Fin size) :
    ∃ i, Perm.SameCycle f x i ∧ ∀ j, Perm.SameCycle f i j → i ≤ j := by
  classical
  let s := Finset.univ.filter (Perm.SameCycle f x)
  have hs : s.Nonempty := ⟨x, by simp [s, Perm.SameCycle.refl]⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (s.min'_mem hs)).2, ?_⟩
  intro j hj
  apply Finset.min'_le
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, ((Finset.mem_filter.mp (s.min'_mem hs)).2).trans hj⟩

/-- The frozen minimum predicate chooses exactly one representative of every orbit. -/
theorem minima_card {size} (f : Perm (Fin size)) :
    (Finset.univ.filter (fun i => ∀ j, Perm.SameCycle f i j → i ≤ j)).card =
      orbitCount f := by
  classical
  let s := Finset.univ.filter (fun i => ∀ j, Perm.SameCycle f i j → i ≤ j)
  let q : s → Quotient (Perm.SameCycle.setoid f) := fun i => Quotient.mk'' i.val
  have hi : Function.Injective q := by
    intro i j h
    have hij : Perm.SameCycle f i.val j.val := Quotient.exact h
    apply Subtype.ext
    apply le_antisymm
    · exact (Finset.mem_filter.mp i.property).2 _ hij
    · exact (Finset.mem_filter.mp j.property).2 _ hij.symm
  have hsur : Function.Surjective q := by
    intro z
    induction z using Quotient.inductionOn with
    | _ x =>
      obtain ⟨i, hxi, hmin⟩ := minimum_exists f x
      exact ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmin⟩⟩,
        Quotient.sound hxi.symm⟩
  have hc := Nat.card_congr (Equiv.ofBijective q ⟨hi,hsur⟩)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, orbitCount] using hc

/-- Certified evaluator equals the cardinality of the genuine orbit quotient. -/
theorem cycles_eq_orbitCount {size} (f : Perm (Fin size)) :
    cycles size (Model2.rawPerm f) = orbitCount f := by
  classical
  change cycles size (fun i => if h : i < size then (f ⟨i,h⟩).val else i) = _
  rw [Model2.orbitCounterCorrect size f]
  convert minima_card f using 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Model2.bounded_minimum_iff f i

theorem trace_congr (size : Nat) (f g : Nat → Nat)
    (hf : ∀ i, i < size → f i < size)
    (he : ∀ i, i < size → f i = g i) (fuel i : Nat) (s : List Nat)
    (hi : i < size) : trace f fuel i s = trace g fuel i s := by
  induction fuel generalizing i s with
  | zero => rfl
  | succ fuel ih =>
    change (if i ∈ s then s else trace f fuel (f i) (i :: s)) =
      (if i ∈ s then s else trace g fuel (g i) (i :: s))
    split
    · rfl
    · rw [← he i hi]
      exact ih _ _ (hf i hi)

theorem cycles_congr (size : Nat) (f g : Nat → Nat)
    (hf : ∀ i, i < size → f i < size)
    (he : ∀ i, i < size → f i = g i) : cycles size f = cycles size g := by
  unfold cycles
  congr 1
  have aux (l : List Nat) (hl : ∀ i ∈ l, i < size) (s : Nat × List Nat) :
      l.foldl (fun s i => if i ∈ s.2 then s else
        (s.1+1, trace f size i s.2)) s =
      l.foldl (fun s i => if i ∈ s.2 then s else
        (s.1+1, trace g size i s.2)) s := by
    induction l generalizing s with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldl_cons]
      have hi := hl i (List.mem_cons_self)
      have hs : (if i ∈ s.2 then s else (s.1+1, trace f size i s.2)) =
          (if i ∈ s.2 then s else (s.1+1, trace g size i s.2)) := by
        split
        · rfl
        · rw [trace_congr size f g hf he size i s.2 hi]
      rw [hs]
      exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _
  exact aux _ (fun i hi => List.mem_range.mp hi) _

/-- For positive diagrams the actual boundary is the orbit cardinality of the face map. -/
theorem boundary_eq_orbitCount {n} (hn : n ≠ 0) (D : Diagram n) (c : Sides n) :
    boundary D c = orbitCount (Model2.faceEquiv D c) := by
  rw [boundary, ite_eq_right hn, ← cycles_eq_orbitCount]
  apply cycles_congr
  · intro i hi; exact Model2.rho_lt c _ (Model2.theta_lt D _ hi)
  · intro i hi
    simp only [Model2.rawPerm, dite_eq_left hi]
    rfl
end Chord.Model3
