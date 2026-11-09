import CountR6Bridge
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace ChanLevine.Round7C
open Round6 Round3
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

theorem char_sum {R : Type*} [CommMonoid R] (χ : AddChar (ZMod n) R)
    {V : Type*} (s : Finset V) (f : V → ZMod n) :
    χ (∑ v ∈ s, f v) = ∏ v ∈ s, χ (f v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

/-- Character factor from each vertex, with the frozen Fourier sign. -/
theorem char_vertex (k v : ZMod n) (a : ℕ) :
    (countingChar n).char (-(v * (a : ZMod n) * k)) =
      (frequencyRoot n k ^ v.val) ^ a := by
  have h (b : ℕ) : (countingChar n).char (-(b : ZMod n)*k) =
      frequencyRoot n k ^ b := by
    rw [frequencyRoot, ← AddChar.map_nsmul_eq_pow]
    congr 1
    simp [nsmul_eq_mul]
  rw [← pow_mul, ← h]
  congr 1
  simp [mul_assoc]

/-- The character of chipWeight includes one factor z for every false rotor. -/
theorem char_chipWeight (c : Config n) (k : ZMod n) :
    (countingChar n).char (-(chipWeight c*k)) =
      (∏ v, (frequencyRoot n k ^ v.val) ^ c.x v) *
        (∏ v, if c.q v then 1 else frequencyRoot n k) := by
  have hw : -(chipWeight c*k) =
      (∑ v, -(v * (c.x v : ZMod n) * k)) +
        ∑ v, if c.q v then 0 else -k := by
    simp only [chipWeight, weight, Config.lift, Int.cast_natCast, add_mul,
      Finset.sum_mul, neg_add, Finset.sum_neg_distrib]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hq : c.q v = true <;> simp [hq]
  rw [hw, AddChar.map_add_eq_mul, char_sum, char_sum]
  simp_rw [char_vertex]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  by_cases hq : c.q v = true <;> simp [hq, frequencyRoot]

/-- Empty selected edges split into independent chip and rotor constraints. -/
theorem selected_empty_iff (c : Config n) (s : Finset (ZMod n)) :
    (∀ v ∈ s, Round5.emptyFacing c v) ↔
      (∀ v ∈ s ∪ rightEnds s, c.x v = 0) ∧
      (∀ v ∈ s, c.q v = true ∧ c.q (v+1) = false) := by
  constructor
  · intro h
    constructor
    · intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (h v hv).2.2.1
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
        exact (h u hu).2.2.2
    · intro v hv; exact ⟨(h v hv).1, (h v hv).2.1⟩
  · rintro ⟨hx,hq⟩ v hv
    exact ⟨(hq v hv).1, (hq v hv).2, hx v (Finset.mem_union_left _ hv),
      hx (v+1) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩))⟩

theorem selected_indicator {R : Type*} [CommRing R]
    (c : Config n) (s : Finset (ZMod n)) :
    (∏ v ∈ s, if Round5.emptyFacing c v then (1 : R) else 0) =
      (if ∀ v ∈ s ∪ rightEnds s, c.x v = 0 then 1 else 0) *
        (if ∀ v ∈ s, c.q v = true ∧ c.q (v+1) = false then 1 else 0) := by
  classical
  have hp : (∏ v ∈ s, if Round5.emptyFacing c v then (1 : R) else 0) =
      if ∀ v ∈ s, Round5.emptyFacing c v then 1 else 0 := by
    split_ifs with h
    · exact Finset.prod_eq_one (fun v hv => ite_eq_left (h v hv))
    · push Not at h
      obtain ⟨v,hv,he⟩ := h
      exact Finset.prod_eq_zero hv (ite_eq_right he)
  rw [hp]
  simp only [selected_empty_iff]
  split_ifs <;> simp_all
end ChanLevine.Round7C
