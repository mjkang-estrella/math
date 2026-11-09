import CountR5Top
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace ChanLevine.Round5
set_option linter.unusedSimpArgs false

variable {n : ℕ} [NeZero n]

def emptyFacing (c : Config n) (k : ZMod n) : Prop :=
  c.q k = true ∧ c.q (k+1) = false ∧ c.x k = 0 ∧ c.x (k+1) = 0

theorem positive_cycleTest (c : Config n) (hm : 0 < chipLevel c) :
    CycleTest c ↔ ∀ k, ¬ emptyFacing c k := by
  have hx : ∃ k, c.x k ≠ 0 := by
    by_contra h
    push Not at h
    have hz : chipLevel c = 0 := by simp [chipLevel, h]
    omega
  constructor
  · intro h k hk
    rcases h.1 k hk.1 hk.2.1 with h | h
    · exact h hk.2.2.1
    · exact h hk.2.2.2
  · intro h
    refine ⟨?_, fun _ => hx, fun _ => hx⟩
    intro k hq hr
    by_contra hh
    push Not at hh
    exact h k ⟨hq, hr, hh⟩

/-- At positive level the exact frozen cycle test is a finite product of local indicators. -/
theorem cycle_indicator {R : Type*} [CommRing R] (c : Config n)
    (hm : 0 < chipLevel c) :
    (if CycleTest c then (1 : R) else 0) =
      ∏ k : ZMod n, (1 - if emptyFacing c k then 1 else 0) := by
  classical
  by_cases h : CycleTest c
  · rw [ite_eq_left h]
    have hk := (positive_cycleTest c hm).mp h
    simp [hk]
  · rw [ite_eq_right h]
    have hk : ∃ k, emptyFacing c k := by
      by_contra hh
      push Not at hh
      exact h ((positive_cycleTest c hm).mpr hh)
    obtain ⟨k, hk⟩ := hk
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [hk]

/-- Finite weighted inclusion-exclusion for one literal configuration. The weight
is retained as an arbitrary scalar, so in particular the rotor factor is retained. -/
theorem weighted_inclusion_exclusion {R : Type*} [CommRing R]
    (c : Config n) (hm : 0 < chipLevel c) (w : R) :
    w * (if CycleTest c then 1 else 0) =
      ∑ s ∈ (Finset.univ : Finset (ZMod n)).powerset,
        (-1 : R)^s.card * w * ∏ k ∈ s, (if emptyFacing c k then 1 else 0) := by
  classical
  rw [cycle_indicator c hm]
  have h := Finset.prod_sub (fun _ : ZMod n => (1 : R))
    (fun k => if emptyFacing c k then (1 : R) else 0) Finset.univ
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.prod_const_one, one_mul]
  ring

omit [NeZero n] in
/-- Facing pairs never share their next endpoint, independently of chip counts. -/
theorem facing_not_adjacent (c : Config n) (k : ZMod n)
    (hk : emptyFacing c k) : ¬ emptyFacing c (k+1) := by
  intro h
  have := hk.2.1.symm.trans h.1
  cases this
end ChanLevine.Round5
