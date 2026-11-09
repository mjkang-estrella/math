module
public import ParkingScalar
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Finset.Prod

public noncomputable section
namespace ParkingCount
open ParkingScalar Polynomial
variable {K : Type*} [Field K] [CharZero K]

def roots (n : ℕ) (a : K) : Finset K := nthRootsFinset n a

def candidates (K : Type*) [Field K] : Finset (K × K) := by
  classical
  exact (({(0,0)} ∪ (roots 9 (4:K)).image (fun t => (t,0))) ∪
    (roots 9 (4:K)).image (fun t => (0,t))) ∪
    ((roots 3 (1:K) ×ˢ roots 9 (1:K))).image (fun p => (p.1*p.2,p.2))

omit [CharZero K] in
theorem root_card (n : ℕ) (a : K) : (roots n a).card ≤ n := by
  classical
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots n a)

theorem axis_ninth (x : K) (hx0 : x ≠ 0) (hx : theta1 x 0 = x) : x^9 = 4 := by
  have h : x^10 = x*4 := by
    unfold theta1 at hx
    have hh := (div_eq_iff (show (4:K) ≠ 0 from OfNat.ofNat_ne_zero 4)).mp hx
    simpa only [zero_pow (by decide : 6 ≠ 0), mul_zero, add_zero] using hh
  have hh : x*(x^9-4) = 0 := by
    calc _ = x^10-x*4 := by ring
         _ = 0 := sub_eq_zero.mpr h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hx0)

theorem fixed_mem (x y : K) (hx : theta1 x y = x) (hy : theta2 x y = y) :
    (x,y) ∈ candidates K := by
  classical
  unfold candidates
  simp only [Finset.mem_union]
  by_cases hxo : x = 0
  · subst x
    by_cases hyo : y = 0
    · subst y; exact Or.inl (Or.inl (Or.inl (Finset.mem_singleton_self _)))
    · apply Or.inl ∘ Or.inr
      apply Finset.mem_image.mpr
      refine ⟨y, ?_, rfl⟩
      apply (mem_nthRootsFinset (by decide : 0 < 9) (4:K)).mpr
      apply axis_ninth y hyo
      simpa only [theta1, theta2, zero_pow (by decide : 6 ≠ 0),
        mul_zero, zero_mul, add_zero] using hy
  by_cases hyo : y = 0
  · subst y
    apply Or.inl ∘ Or.inl ∘ Or.inr
    exact Finset.mem_image.mpr ⟨x, (mem_nthRootsFinset (by decide : 0 < 9) (4:K)).mpr
      (axis_ninth x hxo hx), rfl⟩
  · apply Or.inr
    have h : x^3 = y^3 := ((fixed_directions x y hx hy).resolve_left hxo).resolve_left hyo
    apply Finset.mem_image.mpr
    refine ⟨(x/y,y), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · apply (mem_nthRootsFinset (by decide : 0 < 3) (1:K)).mpr
      rw [div_pow, h, div_self (pow_ne_zero _ hyo)]
    · exact (mem_nthRootsFinset (by decide : 0 < 9) (1:K)).mpr
        (off_axes_ninth x y hyo h hy)
    · simp only [div_mul_cancel₀ _ hyo]

omit [CharZero K] in
theorem candidates_card : (candidates K).card ≤ 46 := by
  classical
  have a := root_card 9 (4:K)
  have b := root_card 3 (1:K)
  have c := root_card 9 (1:K)
  have d := Nat.mul_le_mul b c
  unfold candidates
  have i1 := Finset.card_image_le (s := roots 9 (4:K)) (f := fun t => (t,(0:K)))
  have i2 := Finset.card_image_le (s := roots 9 (4:K)) (f := fun t => ((0:K),t))
  have i3 := Finset.card_image_le (s := (roots 3 (1:K) ×ˢ roots 9 (1:K)))
    (f := fun p => (p.1*p.2,p.2))
  rw [Finset.card_product] at i3
  calc _ ≤ (({(0,0)} ∪ (roots 9 (4:K)).image (fun t => (t,0))) ∪
      (roots 9 (4:K)).image (fun t => (0,t))).card +
      (((roots 3 (1:K) ×ˢ roots 9 (1:K))).image (fun p => (p.1*p.2,p.2))).card :=
        Finset.card_union_le _ _
       _ ≤ 46 := by
         have u := Finset.card_union_le (s := ({(0,0)} ∪ (roots 9 (4:K)).image (fun t => (t,0))))
           (t := (roots 9 (4:K)).image (fun t => (0,t)))
         have v := Finset.card_union_le (s := ({((0:K),(0:K))} : Finset (K × K)))
           (t := (roots 9 (4:K)).image (fun t => (t,0)))
         simp only [Finset.card_singleton] at v
         omega

/-- Coordinate-level fixed set. This is not yet bound to a reflection representation. -/
def fixedSet (K : Type*) [Field K] : Set (K × K) :=
  {p | theta1 p.1 p.2 = p.1 ∧ theta2 p.1 p.2 = p.2}

theorem no_hundred : ¬ Nonempty ({p // p ∈ fixedSet K} ≃ Fin 100) := by
  classical
  intro ⟨e⟩
  let f : {p // p ∈ fixedSet K} → {p // p ∈ candidates K} :=
    fun p => ⟨p.1, fixed_mem p.1.1 p.1.2 p.2.1 p.2.2⟩
  have hf : Function.Injective f := by
    intro p q h
    exact Subtype.ext (congrArg (fun z : {p // p ∈ candidates K} => z.val) h)
  have hh := Fintype.card_le_of_injective (f ∘ e.symm) (hf.comp e.symm.injective)
  have hn : (100:ℕ) ≤ (candidates K).card := by simpa using hh
  have hc := candidates_card (K := K)
  omega

/-- Parking predicates here are arbitrary. This is a coordinate checkpoint only. -/
theorem coordinate_polymorphic_failure (B C : (K → K → K) → (K → K → K) → Prop) :
    ¬ (∀ f g : K → K → K,
      Nonempty ({p : K × K // f p.1 p.2 = p.1 ∧ g p.1 p.2 = p.2} ≃ Fin 100) ∧
      B f g ∧ C f g) := by
  intro h
  exact no_hundred (h theta1 theta2).1

#print axioms fixedSet
#print axioms no_hundred
#print axioms coordinate_polymorphic_failure
#print axioms roots
#print axioms candidates
#print axioms root_card
#print axioms axis_ninth
#print axioms fixed_mem
#print axioms candidates_card
end ParkingCount
