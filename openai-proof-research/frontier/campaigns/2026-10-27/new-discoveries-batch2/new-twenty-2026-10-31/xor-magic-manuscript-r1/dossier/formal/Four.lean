import Literal
namespace XorMagic
abbrev Four := ZMod 2 × ZMod 2

def omegaMap (x : Four) : Four := (x.2, x.1 + x.2)
def omegaSq (x : Four) : Four := omegaMap (omegaMap x)

theorem omega_cube : ∀ x : Four, omegaMap (omegaSq x) = x := by decide
theorem omega_sum : ∀ x : Four, x + omegaMap x + omegaSq x = 0 := by decide
theorem omega_add : ∀ x y : Four, omegaMap (x + y) = omegaMap x + omegaMap y := by decide
theorem omega_fixed : ∀ x : Four, omegaMap x = x ↔ x = 0 := by decide
theorem omegaSq_fixed : ∀ x : Four, omegaSq x = x ↔ x = 0 := by decide
theorem four_sum : (∑ x : Four, x) = 0 := by decide

def affine (s : Bool) (c x : Four) : Four :=
  (if s then omegaMap x else omegaSq x) + c

theorem affine_bijective : ∀ s c, Function.Bijective (affine s c) := by decide
theorem affine_unique_fixed : ∀ s c, ∃! x, affine s c x = x := by
  simp only [ExistsUnique]
  decide

theorem invariant_fibre_sizes : ∀ s c (S : Finset Four),
    (∀ x, x ∈ S ↔ affine s c x ∈ S) →
    S.card = 0 ∨ S.card = 1 ∨ S.card = 3 ∨ S.card = 4 := by decide

theorem invariant_singleton : ∀ s c x,
    (∀ y, y ∈ ({x} : Finset Four) ↔ affine s c y ∈ ({x} : Finset Four)) →
    affine s c x = x := by decide

theorem invariant_three_complement : ∀ s c (S : Finset Four),
    S.card = 3 → (∀ x, x ∈ S ↔ affine s c x ∈ S) →
    ∃ x : Four, (∀ y : Four, y ∉ S ↔ y = x) ∧ affine s c x = x := by
  intro s c S hcard hinv
  classical
  have hc : Sᶜ.card = 1 := by
    rw [Finset.card_compl, hcard]
    decide
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
  have only : ∀ y : Four, y ∉ S ↔ y = x := by
    intro y
    simp only [← Finset.mem_compl, hx, Finset.mem_singleton]
  refine ⟨x, only, ?_⟩
  apply (only _).mp
  exact fun ha => ((only x).mpr rfl) ((hinv x).mpr ha)
def bitsFourEquiv (n : ℕ) : Bits n × Four ≃ Bits (n+2) :=
  (Equiv.prodCongr (Equiv.refl (Bits n)) (finTwoArrowEquiv (ZMod 2)).symm).trans
    (Fin.appendEquiv n 2)

theorem bitsFourEquiv_add (n : ℕ) (x y : Bits n × Four) :
    bitsFourEquiv n (x+y) = bitsFourEquiv n x + bitsFourEquiv n y := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [bitsFourEquiv, Fin.appendEquiv]
  · fin_cases j <;> simp [bitsFourEquiv, Fin.appendEquiv, finTwoArrowEquiv]

end XorMagic
