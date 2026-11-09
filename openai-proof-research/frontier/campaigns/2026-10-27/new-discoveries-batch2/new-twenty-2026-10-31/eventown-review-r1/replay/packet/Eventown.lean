import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

namespace Eventown372630
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- A permutation has a cycle of positive even length: the orbit of i has exact length k. -/
def BoundedEvenCycle {n : ℕ} (g : Equiv.Perm (Fin n)) : Prop :=
  ∃ i : Fin n, ∃ k ∈ Finset.Icc 1 n, Even k ∧ (g ^ k) i = i ∧
    ∀ j ∈ Finset.Icc 1 (k - 1), (g ^ j) i ≠ i

/-- Literal even cycle: the exact positive orbit length is even, without a search bound. -/
def EvenCycle {n : ℕ} (g : Equiv.Perm (Fin n)) : Prop :=
  ∃ i : Fin n, ∃ k : ℕ, 0 < k ∧ Even k ∧ (g ^ k) i = i ∧
    ∀ j : ℕ, 0 < j → j < k → (g ^ j) i ≠ i

theorem bounded_cycle_sound {n : ℕ} {g : Equiv.Perm (Fin n)}
    (h : BoundedEvenCycle g) : EvenCycle g := by
  obtain ⟨i, k, hk, he, hp, hm⟩ := h
  exact ⟨i, k, (Finset.mem_Icc.mp hk).1, he, hp, fun j hj hjk =>
    hm j (Finset.mem_Icc.mpr ⟨hj, by omega⟩)⟩

/-- Pairwise quotients, with distinctness required as in the source Cayley graph. -/
def Intersecting {n : ℕ} (S : Finset (Equiv.Perm (Fin n))) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → EvenCycle (a * b⁻¹)

def Maximum {n : ℕ} (S : Finset (Equiv.Perm (Fin n))) : Prop :=
  Intersecting S ∧ ∀ T : Finset (Equiv.Perm (Fin n)), Intersecting T → T.card ≤ S.card

/-- Literal double-translate of a Sylow 2-subgroup. -/
def SylowTranslate {n : ℕ} (S : Finset (Equiv.Perm (Fin n))) : Prop :=
  ∃ P : Sylow 2 (Equiv.Perm (Fin n)), ∃ a b,
    ∀ x, x ∈ S ↔ ∃ h : P, x = a * (h : Equiv.Perm (Fin n)) * b

/-- Source Conjecture 16, both extremality and uniqueness, for all n ≥ 2. -/
def SourceConjecture : Prop :=
  ∀ n, 2 ≤ n → ∀ S : Finset (Equiv.Perm (Fin n)), Maximum S ↔ SylowTranslate S

def w0 : Equiv.Perm (Fin 5) := ⟨![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], by decide, by decide⟩
def w1 : Equiv.Perm (Fin 5) := ⟨![0, 2, 1, 4, 3], ![0, 2, 1, 4, 3], by decide, by decide⟩
def w2 : Equiv.Perm (Fin 5) := ⟨![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2], by decide, by decide⟩
def w3 : Equiv.Perm (Fin 5) := ⟨![0, 4, 3, 2, 1], ![0, 4, 3, 2, 1], by decide, by decide⟩
def w4 : Equiv.Perm (Fin 5) := ⟨![0, 1, 2, 4, 3], ![0, 1, 2, 4, 3], by decide, by decide⟩
def w5 : Equiv.Perm (Fin 5) := ⟨![1, 0, 2, 3, 4], ![1, 0, 2, 3, 4], by decide, by decide⟩
def w6 : Equiv.Perm (Fin 5) := ⟨![3, 4, 2, 1, 0], ![4, 3, 2, 0, 1], by decide, by decide⟩
def w7 : Equiv.Perm (Fin 5) := ⟨![4, 3, 2, 0, 1], ![3, 4, 2, 1, 0], by decide, by decide⟩

def witness : Finset (Equiv.Perm (Fin 5)) := {w0, w1, w2, w3, w4, w5, w6, w7}

theorem witness_card : witness.card = 8 := by decide

theorem witness_one : (1 : Equiv.Perm (Fin 5)) ∈ witness := by decide

theorem witness_intersecting : Intersecting witness := by
  have hc : ∀ a ∈ witness, ∀ b ∈ witness, a ≠ b → BoundedEvenCycle (a * b⁻¹) := by
    unfold BoundedEvenCycle witness
    decide
  intro a ha b hb hab
  exact bounded_cycle_sound (hc a ha b hb hab)

theorem witness_not_closed : ¬ (∀ a ∈ witness, ∀ b ∈ witness, a * b ∈ witness) := by
  decide

/-- A double-translate containing the identity is a conjugate subgroup. -/
theorem translate_closed {G : Type*} [Group G] (P : Subgroup G) (a b : G)
    (S : Set G) (hS : ∀ x, x ∈ S ↔ ∃ h : P, x = a * (h : G) * b)
    (hone : 1 ∈ S) : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
  obtain ⟨h0, h0eq⟩ := (hS 1).mp hone
  intro x hx y hy
  obtain ⟨h1, rfl⟩ := (hS x).mp hx
  obtain ⟨h2, rfl⟩ := (hS y).mp hy
  apply (hS _).mpr
  refine ⟨h1 * h0⁻¹ * h2, ?_⟩
  have hb : b = (a * (h0 : G))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact h0eq.symm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hb]
  group

theorem witness_not_translate : ¬ SylowTranslate witness := by
  rintro ⟨P, a, b, h⟩
  exact witness_not_closed (translate_closed P.toSubgroup a b (↑witness) h witness_one)

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem sylow_card_five (P : Sylow 2 (Equiv.Perm (Fin 5))) : Nat.card P = 8 := by
  rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num only [Fintype.card_fin, Nat.factorial]
  have hf : (Nat.factorization 120) 2 = 3 := by
    rw [show 120 = 2 ^ 3 * 15 by decide, Nat.factorization_mul (by decide) (by decide)]
    simp only [Finsupp.add_apply, Nat.factorization_pow_self (by decide : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15), add_zero]
  rw [hf]
  decide

/-- The cardinality of a double-translate is exactly the subgroup cardinality. -/
theorem translate_card_five (S : Finset (Equiv.Perm (Fin 5))) (h : SylowTranslate S) : S.card = 8 := by
  classical
  obtain ⟨P, a, b, h⟩ := h
  let f : P → Equiv.Perm (Fin 5) := fun x => a * (x : Equiv.Perm (Fin 5)) * b
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact mul_left_cancel (mul_right_cancel hxy)
  have hs : (S : Set (Equiv.Perm (Fin 5))) = f '' Set.univ := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, Finset.mem_coe]
    exact (h x).trans (by simp only [eq_comm, f])
  have hc := congrArg Set.ncard hs
  rw [Set.ncard_coe_finset, Set.ncard_image_of_injective _ hf, Set.ncard_univ] at hc
  exact hc.trans (sylow_card_five P)

/-- Exact source negation; no claim about changing the size bound alone. -/
theorem literal_source_refutation : ¬ SourceConjecture := by
  classical
  intro hc
  let P : Sylow 2 (Equiv.Perm (Fin 5)) := Sylow.nonempty.some
  let S : Finset (Equiv.Perm (Fin 5)) := (P : Set (Equiv.Perm (Fin 5))).toFinset
  have ht : SylowTranslate S := by
    refine ⟨P, 1, 1, ?_⟩
    intro x
    simp only [S, Set.mem_toFinset, one_mul, mul_one]
    exact ⟨fun hx => ⟨⟨x,hx⟩, rfl⟩, fun ⟨h, hh⟩ => hh ▸ h.property⟩
  have hm : Maximum S := (hc 5 (by decide) S).mpr ht
  have hcard : S.card = 8 := translate_card_five S ht
  have hwmax : Maximum witness := ⟨witness_intersecting, fun T hT => by
    have h := hm.2 T hT
    simpa only [hcard, witness_card] using h⟩
  exact witness_not_translate ((hc 5 (by decide) witness).mp hwmax)

#print axioms literal_source_refutation
end Eventown372630
