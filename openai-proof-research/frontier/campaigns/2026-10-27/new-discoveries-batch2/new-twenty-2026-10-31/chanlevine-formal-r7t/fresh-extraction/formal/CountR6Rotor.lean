import CountR6Encoding
noncomputable section
open scoped BigOperators
namespace ChanLevine.Round6
attribute [local instance] Classical.propDecidable
variable {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]

/-- The rotor character with fixed clockwise and counterclockwise endpoints. -/
def rotorLocal (z : R) (A B : Finset V) (v : V) (b : Bool) : R :=
  if v ∈ A then (if b then 1 else 0)
  else if v ∈ B then (if b then 0 else z)
  else (if b then 1 else z)

theorem rotor_local_sum (z : R) (A B : Finset V) (h : Disjoint A B) :
    (∑ q : V → Bool, ∏ v, rotorLocal z A B v (q v)) =
      z^B.card * (1+z)^(Fintype.card V - (A.card+B.card)) := by
  classical
  rw [← Fintype.prod_sum]
  let f := fun v => ∑ b : Bool, rotorLocal z A B v b
  change (∏ v, f v) = _
  have ha : ∀ v ∈ A, f v = 1 := by intro v hv; simp [f, rotorLocal, hv]
  have hb : ∀ v ∈ B, f v = z := by
    intro v hv
    have hn : v ∉ A := fun hh => Finset.disjoint_left.mp h hh hv
    simp [f, rotorLocal, hv, hn]
  have hc : ∀ v ∈ (A ∪ B)ᶜ, f v = 1+z := by
    intro v hv
    have hh : v ∉ A ∧ v ∉ B := by simpa using hv
    simp [f, rotorLocal, hh.1, hh.2, add_comm]
  have hu : (Finset.univ : Finset V) = (A ∪ B) ∪ (A ∪ B)ᶜ := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_compl]
    tauto
  rw [hu, Finset.prod_union (disjoint_compl_right), Finset.prod_union h]
  rw [Finset.prod_congr rfl ha, Finset.prod_congr rfl hb, Finset.prod_congr rfl hc]
  simp only [Finset.prod_const_one, Finset.prod_const, one_mul,
    Finset.card_compl, Finset.card_union_of_disjoint h]

variable {n : ℕ} [NeZero n]
/-- Each forced pair contributes exactly one counterclockwise rotor, including wrap pairs. -/
theorem matching_rotor_sum (z : R) (s : Finset (ZMod n)) (hs : Matching s) :
    (∑ q : ZMod n → Bool, ∏ v, rotorLocal z s (rightEnds s) v (q v)) =
      z^s.card * (1+z)^(n-2*s.card) := by
  rw [rotor_local_sum z s (rightEnds s) (matching_disjoint s hs), rightEnds_card]
  simp only [ZMod.card]
  congr 2
  omega
end ChanLevine.Round6

namespace ChanLevine.Round6
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]

theorem rotorLocal_product (z : R) (A B : Finset V) (h : Disjoint A B)
    (q : V → Bool) :
    (∏ v, rotorLocal z A B v (q v)) =
      (∏ v, if q v then 1 else z) *
        (if (∀ v ∈ A, q v = true) ∧ (∀ v ∈ B, q v = false) then 1 else 0) := by
  classical
  by_cases hh : (∀ v ∈ A, q v = true) ∧ (∀ v ∈ B, q v = false)
  · rw [ite_eq_left hh, mul_one]
    apply Finset.prod_congr rfl
    intro v _
    by_cases ha : v ∈ A
    · simp [rotorLocal, ha, hh.1 v ha]
    · by_cases hb : v ∈ B
      · simp [rotorLocal, ha, hb, hh.2 v hb]
      · simp [rotorLocal, ha, hb]
  · rw [ite_eq_right hh, mul_zero]
    have hx : (∃ v ∈ A, q v ≠ true) ∨ (∃ v ∈ B, q v ≠ false) := by
      simpa only [not_and_or, not_forall, exists_prop] using hh
    rcases hx with ⟨v,hv,hq⟩ | ⟨v,hv,hq⟩
    · apply Finset.prod_eq_zero (Finset.mem_univ v)
      cases he : q v <;> simp_all [rotorLocal]
    · apply Finset.prod_eq_zero (Finset.mem_univ v)
      have ha : v ∉ A := fun hh => Finset.disjoint_left.mp h hh hv
      cases he : q v <;> simp_all [rotorLocal]

variable {n : ℕ} [NeZero n]
/-- The forced endpoint sum is the full rotor weight, not a rotor-free count. -/
theorem forced_rotor_sum (z : R) (s : Finset (ZMod n)) (hs : Matching s) :
    (∑ q : ZMod n → Bool, (∏ v, if q v then 1 else z) *
      (if ∀ k ∈ s, q k = true ∧ q (k+1) = false then 1 else 0)) =
      z^s.card * (1+z)^(n-2*s.card) := by
  classical
  have he (q : ZMod n → Bool) :
      ((∀ v ∈ s, q v = true) ∧ (∀ v ∈ rightEnds s, q v = false)) ↔
        (∀ k ∈ s, q k = true ∧ q (k+1) = false) := by
    constructor
    · intro h k hk
      exact ⟨h.1 k hk, h.2 (k+1) (Finset.mem_image.mpr ⟨k,hk,rfl⟩)⟩
    · intro h
      refine ⟨fun k hk => (h k hk).1, ?_⟩
      intro v hv
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
      exact (h k hk).2
  have hp := matching_rotor_sum z s hs
  simp_rw [rotorLocal_product z s (rightEnds s) (matching_disjoint s hs), he] at hp
  exact hp
end ChanLevine.Round6
