import Matching
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace WheelFormal

def gridPair {V : Type} [DecidableEq V] (p q : V → V) (z : V × V) : V × V :=
  if q z.2 = z.2 then (p z.1,z.2) else (z.1,q z.2)

theorem gridPair_involutive {V : Type} [DecidableEq V]
    (p q : V → V) (hp : Function.Involutive p) (hq : Function.Involutive q) :
    Function.Involutive (gridPair p q) := by
  rintro ⟨x,y⟩
  by_cases h : q y = y
  · simp only [gridPair, h, ite_true, hp x]
  · have hh : q (q y) ≠ q y := by rw [hq y]; exact Ne.symm h
    simp only [gridPair, h, ite_false, hh, hq y, Ne.symm h]

theorem deletion_grid_bound (t : ℕ)
    (A B : Finset (ZMod (2*t+1))) (hA : A.Nonempty) (hB : B.Nonempty)
    (I : Finset (ZMod (2*t+1) × ZMod (2*t+1)))
    (hI : I ⊆ Aᶜ ×ˢ Bᶜ)
    (hInd : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      ¬ ((x.1 = y.1 ∧ rimAdj (2*t+1) x.2 y.2) ∨
         (rimAdj (2*t+1) x.1 y.1 ∧ x.2 = y.2))) :
    2*I.card ≤ (2*t+1-A.card)*(2*t+1-B.card)+(A.card-1)*(B.card-1) := by
  classical
  obtain ⟨p,hp,hpS,hpE,hpF⟩ := cycle_deletion_pairing t A hA
  obtain ⟨q,hq,hqS,hqE,hqF⟩ := cycle_deletion_pairing t B hB
  have hS : ∀ z ∈ Aᶜ ×ˢ Bᶜ, gridPair p q z ∈ Aᶜ ×ˢ Bᶜ := by
    rintro ⟨x,y⟩ hz
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hz
    by_cases hh : q y = y
    · simp only [gridPair, hh, ite_true]; exact Finset.mem_product.mpr ⟨hpS x hx,hy⟩
    · simp only [gridPair, hh, ite_false]; exact Finset.mem_product.mpr ⟨hx,hqS y hy⟩
  have hi : ∀ z ∈ I, gridPair p q z ∈ I → gridPair p q z = z := by
    rintro ⟨x,y⟩ hz hz'
    by_contra hn
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp (hI hz)
    apply hInd (x,y) hz (gridPair p q (x,y)) hz' (Ne.symm hn)
    by_cases hh : q y = y
    · have hpx : p x ≠ x := by intro h; apply hn; simp [gridPair,hh,h]
      right
      simp only [gridPair,hh,ite_true]; exact ⟨hpE x hx hpx,True.intro⟩
    · left
      simp only [gridPair,hh,ite_false]; exact ⟨True.intro,hqE y hy hh⟩
  have hf : ((Aᶜ ×ˢ Bᶜ).filter (fun z => gridPair p q z = z)) =
      (Aᶜ.filter (fun x => p x = x)) ×ˢ (Bᶜ.filter (fun y => q y = y)) := by
    ext ⟨x,y⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    by_cases hh : q y = y <;> simp [gridPair,hh, and_assoc, and_left_comm, and_comm]
  have hb := pairing_bound (Aᶜ ×ˢ Bᶜ) I (gridPair p q)
    (gridPair_involutive p q hp hq) hS hI hi
  rw [hf, Finset.card_product, Finset.card_product] at hb
  have hc : (Aᶜ.filter (fun x => p x = x)).card * (Bᶜ.filter (fun y => q y = y)).card ≤
      (A.card-1)*(B.card-1) := Nat.mul_le_mul hpF hqF
  have ca : Aᶜ.card = 2*t+1-A.card := by simp [Finset.card_compl, ZMod.card]
  have cb : Bᶜ.card = 2*t+1-B.card := by simp [Finset.card_compl, ZMod.card]
  rw [ca, cb] at hb
  omega
end WheelFormal
