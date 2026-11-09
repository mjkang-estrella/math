import Coset
import Mathlib.Algebra.Group.Subgroup.Defs
noncomputable section
namespace UnitCoset

def identity : A ≃ A := Equiv.refl A

theorem identity_unit : UnitSequence identity := by
  apply (unit_iff_injective _).mpr
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · have h := congrArg Prod.fst hab
    change (a : Ambient).1 + (a : Ambient).1 = (b : Ambient).1 + (b : Ambient).1 at h
    rw [← two_mul, ← two_mul] at h
    have hh := congrArg (fun z : K => 2 * z) h
    have hinv : (2 : K) * 2 = 1 := by decide
    simpa only [← mul_assoc, hinv, one_mul] using hh
  · exact (second a).trans (second b).symm

theorem identity_collision : translate identity ≠ identity ∧
    multiplicity (translate identity) = multiplicity identity :=
  ⟨translate_ne _, translate_multiplicity _ identity_unit⟩

def constantSum (c : K) : A ≃ A where
  toFun a := coord (c - (a : Ambient).1)
  invFun a := coord (c - (a : Ambient).1)
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · exact sub_sub_cancel c _
    · exact (second a).symm
  right_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · exact sub_sub_cancel c _
    · exact (second a).symm

@[simp] theorem constant_sum (c : K) (a : A) :
    sumMap (constantSum c) a = (c,0) := by
  apply Prod.ext
  · change (a : Ambient).1 + (c - (a : Ambient).1) = c
    simp [sub_eq_add_neg, add_left_comm]
  · exact sum_second (constantSum c) a

theorem constant_multiplicity (c : K) (x : Ambient) :
    multiplicity (constantSum c) x = if x = (c,0) then 3 else 0 := by
  by_cases hx : x = (c,0)
  · subst x
    simp [multiplicity, constant_sum]
  · apply Eq.trans (multiplicity_zero _ _ (fun a he => hx (he.symm.trans (constant_sum c a))))
    simp [hx]

theorem constant_acyclic (c : K) : Acyclic (constantSum c) := by
  intro g _ hm
  apply Equiv.ext
  intro a
  have hp : 0 < multiplicity g (sumMap g a) := Finset.card_pos.mpr ⟨a, by simp⟩
  rw [hm, constant_multiplicity] at hp
  have he : sumMap g a = (c,0) := by
    by_contra hn
    simp [hn] at hp
  apply Subtype.ext
  have hh := constant_sum c a
  exact add_left_cancel (he.trans hh.symm)

theorem constant_support (c : K) : support (constantSum c) = {(c,0)} := by
  ext x
  rw [← positive_iff, constant_multiplicity]
  by_cases hx : x = (c,0) <;> simp [hx]

theorem constant_sequence (c : K) : sequence (constantSum c) = [3] := by
  simp [sequence, constant_support, constant_multiplicity]

theorem constant_not_unit (c : K) : ¬ UnitSequence (constantSum c) := by
  intro h
  have he := h 3 (by simp [constant_sequence])
  exact (by decide : (3 : ℕ) ≠ 1) he

theorem weak_existence : ∃ f : A ≃ A, Admissible A A f ∧ Acyclic f :=
  ⟨constantSum 0, admissible_all _, constant_acyclic _⟩

theorem union_zero_not_subgroup :
    ¬ ∃ S : AddSubgroup Ambient, (S : Set Ambient) = (↑A : Set Ambient) ∪ {0} := by
  rintro ⟨S, hs⟩
  have h0 : (0,1) ∈ S := by change _ ∈ (S : Set Ambient); rw [hs]; left; simp
  have h1 : (1,1) ∈ S := by change _ ∈ (S : Set Ambient); rw [hs]; left; simp
  have hadd := S.add_mem h0 h1
  change _ ∈ (S : Set Ambient) at hadd
  rw [hs] at hadd
  have he : ((0,1) : Ambient) + (1,1) = (1,0) := by decide
  rw [he] at hadd
  simp at hadd

-- Exact sumset equality, expressed without imposing a finite ambient group generically.
theorem sumset_eq :
    {x : Ambient | ∃ a ∈ A, ∃ b ∈ A, a + b = x} = (↑H0 : Set Ambient) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [Finset.mem_coe, mem_H0, Prod.snd_add]
    rw [(mem_A a).mp ha, (mem_A b).mp hb]
    decide
  · intro hx
    have hx0 := (mem_H0 x).mp hx
    refine ⟨(x.1,1), by simp, (0,1), by simp, ?_⟩
    apply Prod.ext
    · simp
    · exact (by decide : (1 : ZMod 2) + 1 = 0).trans hx0.symm
end UnitCoset
