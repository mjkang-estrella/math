/- Copyright 2026 Myeongjin Kang. Released under the MIT license. -/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate
open RCLike

namespace CM275

section Sampling
variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I]

noncomputable def sample (χ : I → AddChar G ℂ) (c : I → ℂ) : G → ℂ :=
  ∑ i, c i • (χ i : G → ℂ)

omit [AddCommGroup G] in
theorem weighted_sum_left (w : G → ℝ) (f : I → G → ℂ) (g : G → ℂ) :
    ⟪∑ i, f i, g⟫_[ℂ, w] = ∑ i, ⟪f i, g⟫_[ℂ, w] := by
  simp only [wInner, Finset.sum_apply, sum_inner, Finset.smul_sum]
  rw [Finset.sum_comm]

omit [AddCommGroup G] in
theorem weighted_sum_right (w : G → ℝ) (f : G → ℂ) (g : I → G → ℂ) :
    ⟪f, ∑ i, g i⟫_[ℂ, w] = ∑ i, ⟪f, g i⟫_[ℂ, w] := by
  simp only [wInner, Finset.sum_apply, inner_sum, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem character_parseval (χ : I → AddChar G ℂ) (hχ : Function.Injective χ)
    (c d : I → ℂ) :
    ⟪sample χ c, sample χ d⟫ₙ_[ℂ] = ∑ i, star (c i) * d i := by
  classical
  simp only [sample, weighted_sum_left, weighted_sum_right, wInner_smul_left,
    wInner_smul_right, AddChar.wInner_cWeight_eq_boole, smul_eq_mul]
  simp [hχ.eq_iff, mul_comm]

theorem phase_parseval (χ : I → AddChar G ℂ) (hχ : Function.Injective χ)
    (c d u : I → ℂ) (hu : ∀ i, star (u i) * u i = 1) :
    ⟪sample χ (fun i => u i * c i), sample χ (fun i => u i * d i)⟫ₙ_[ℂ] =
      ⟪sample χ c, sample χ d⟫ₙ_[ℂ] := by
  rw [character_parseval χ hχ, character_parseval χ hχ]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_mul]
  calc
    star (c i) * star (u i) * (u i * d i) =
        (star (u i) * u i) * (star (c i) * d i) := by ring
    _ = star (c i) * d i := by rw [hu, one_mul]

omit [Fintype G] in
theorem discrete_translation (χ : I → AddChar G ℂ) (c : I → ℂ) (u x : G) :
    sample χ c (x + u) = sample χ (fun i => χ i u * c i) x := by
  simp only [sample, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    AddChar.map_add_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Sampling

section ZModSampling
variable {q : ℕ} [NeZero q]

noncomputable def mode (k : ZMod q) : AddChar (ZMod q) ℂ :=
  ZMod.stdAddChar.mulShift k

theorem mode_injective : Function.Injective (mode (q := q)) := by
  intro a b h
  apply ZMod.injective_stdAddChar
  have h1 := DFunLike.congr_fun h 1
  simpa [mode] using h1

theorem grid_parseval {I : Type*} [Fintype I] (k : I → ZMod q)
    (hk : Function.Injective k) (c d : I → ℂ) :
    ⟪sample (fun i => mode (k i)) c, sample (fun i => mode (k i)) d⟫ₙ_[ℂ] =
      ∑ i, star (c i) * d i :=
  character_parseval _ (mode_injective.comp hk) c d

omit [NeZero q] in
theorem initial_modes_injective {K : ℕ} (hK : K ≤ q) :
    Function.Injective (fun i : Fin K => (i.val : ZMod q)) := by
  intro a b hab
  apply Fin.ext
  have ha : a.val < q := lt_of_lt_of_le a.isLt hK
  have hb : b.val < q := lt_of_lt_of_le b.isLt hK
  simpa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hab

omit [NeZero q] in
theorem centered_modes_injective {K : ℕ} (hK : 2 * K + 1 ≤ q) :
    Function.Injective (fun i : Fin (2 * K + 1) => (i.val : ZMod q) - (K : ZMod q)) := by
  intro a b hab
  exact initial_modes_injective hK (sub_left_inj.mp hab)

end ZModSampling

section Projector
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

noncomputable def twist (ρ : Representation ℂ G V) (χ : G →* ℂˣ) :
    Representation ℂ G V where
  toFun g := ((χ g : ℂ)⁻¹) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Units.val_mul, mul_inv_rev, LinearMap.smul_apply,
      Module.End.mul_apply, map_smul]
    simp only [smul_smul]

variable [Fintype G]

noncomputable def characterProjector (ρ : Representation ℂ G V) (χ : G →* ℂˣ) : V →ₗ[ℂ] V :=
  let := invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card G : ℂ) ≠ 0)
  (twist ρ χ).averageMap

theorem characterProjector_apply (ρ : Representation ℂ G V) (χ : G →* ℂˣ) (v : V) :
    characterProjector ρ χ v = (Fintype.card G : ℂ)⁻¹ •
      ∑ g : G, ((χ g : ℂ)⁻¹) • ρ g v := by
  simp [characterProjector, Representation.averageMap, GroupAlgebra.average,
    map_sum, invOf_eq_inv, twist,
    LinearMap.sum_apply]

omit [Fintype G] in
theorem twist_invariant_iff (ρ : Representation ℂ G V) (χ : G →* ℂˣ) (v : V) :
    v ∈ (twist ρ χ).invariants ↔ ∀ g, ρ g v = (χ g : ℂ) • v := by
  change (∀ g, ((χ g : ℂ)⁻¹) • ρ g v = v) ↔ _
  constructor
  · intro h g
    have := congrArg (fun z : V => (χ g : ℂ) • z) (h g)
    simpa only [smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul] using this
  · intro h g
    rw [h g, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]

theorem characterProjector_eigen (ρ : Representation ℂ G V) (χ : G →* ℂˣ) (v : V) (g : G) :
    ρ g (characterProjector ρ χ v) = (χ g : ℂ) • characterProjector ρ χ v := by
  let := invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card G : ℂ) ≠ 0)
  exact (twist_invariant_iff ρ χ _).mp ((twist ρ χ).averageMap_invariant v) g

theorem characterProjector_fixes (ρ : Representation ℂ G V) (χ : G →* ℂˣ) (v : V)
    (hv : ∀ g, ρ g v = (χ g : ℂ) • v) : characterProjector ρ χ v = v := by
  let := invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card G : ℂ) ≠ 0)
  exact (twist ρ χ).averageMap_id v ((twist_invariant_iff ρ χ v).mpr hv)

theorem characterProjector_idempotent (ρ : Representation ℂ G V) (χ : G →* ℂˣ) (v : V) :
    characterProjector ρ χ (characterProjector ρ χ v) = characterProjector ρ χ v :=
  characterProjector_fixes ρ χ _ (characterProjector_eigen ρ χ v)

theorem characterProjector_range (ρ : Representation ℂ G V) (χ : G →* ℂˣ) (v : V) :
    v ∈ LinearMap.range (characterProjector ρ χ) ↔ ∀ g, ρ g v = (χ g : ℂ) • v := by
  constructor
  · rintro ⟨u, rfl⟩
    exact characterProjector_eigen ρ χ u
  · intro hv
    exact ⟨v, characterProjector_fixes ρ χ v hv⟩

theorem characterProjector_commutes (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (R : V →ₗ[ℂ] V) (hR : ∀ g v, R (ρ g v) = ρ g (R v)) (v : V) :
    R (characterProjector ρ χ v) = characterProjector ρ χ (R v) := by
  simp only [characterProjector_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [hR]

end Projector

section PermutationSign
variable {A V : Type*} [Fintype A] [DecidableEq A] [AddCommGroup V] [Module ℂ V]

noncomputable def complexSign : Equiv.Perm A →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

theorem signProjector_eigen (ρ : Representation ℂ (Equiv.Perm A) V) (v : V)
    (g : Equiv.Perm A) :
    ρ g (characterProjector ρ complexSign v) =
      (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) • characterProjector ρ complexSign v :=
  characterProjector_eigen ρ complexSign v g

theorem complexSign_inverse (g : Equiv.Perm A) :
    ((complexSign g : ℂ)⁻¹) = (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) := by
  change (((complexSign g)⁻¹ : ℂˣ) : ℂ) = _
  have h : (complexSign g)⁻¹ = complexSign g := by
    change ((Units.map (Int.castRingHom ℂ).toMonoidHom) (Equiv.Perm.sign g))⁻¹ = _
    rw [← map_inv, Int.units_inv_eq_self]
  rw [h]
  rfl

theorem signProjector_apply (ρ : Representation ℂ (Equiv.Perm A) V) (v : V) :
    characterProjector ρ complexSign v = (Fintype.card (Equiv.Perm A) : ℂ)⁻¹ •
      ∑ g : Equiv.Perm A, (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) • ρ g v := by
  rw [characterProjector_apply]
  simp only [complexSign_inverse]

end PermutationSign

section Margins

def acceptance (energy threshold scale : ℝ) : ℝ :=
  1 / 2 - (energy - threshold) / (4 * scale)

theorem total_error_budget (η : ℝ) (hη : 0 ≤ η) :
    η + η / 4 + η / 8 + η / 16 ≤ 2 * η := by linarith

theorem total_energy_transfer (E Ebox Ecap Eband Egrid η : ℝ) (hη : 0 ≤ η)
    (hbox : |Ebox - E| ≤ η) (hcap : |Ecap - Ebox| ≤ η / 4)
    (hband : |Eband - Ecap| ≤ η / 8) (hgrid : |Egrid - Eband| ≤ η / 16) :
    |Egrid - E| ≤ 2 * η := by
  have h := abs_add (Egrid - Eband) (Eband - Ecap)
  have h' := abs_add (Egrid - Ecap) (Ecap - Ebox)
  have h'' := abs_add (Egrid - Ebox) (Ebox - E)
  have he1 : Egrid - Eband + (Eband - Ecap) = Egrid - Ecap := by ring
  have he2 : Egrid - Ecap + (Ecap - Ebox) = Egrid - Ebox := by ring
  have he3 : Egrid - Ebox + (Ebox - E) = Egrid - E := by ring
  rw [he1] at h
  rw [he2] at h'
  rw [he3] at h''
  have hb := total_error_budget η hη
  linarith

theorem yes_margin (a b e η Q : ℝ) (hQ : 0 < Q) (hgap : a < b)
    (hη : η ≤ (b - a) / 100) (he : e ≤ a + 2 * η) :
    1 / 2 + (b - a) / (10 * Q) ≤ acceptance e ((a + b) / 2) Q := by
  unfold acceptance
  have h4 : 0 < 4 * Q := by positivity
  have h10 : 0 < 10 * Q := by positivity
  field_simp
  nlinarith

theorem no_margin (a b e η Q : ℝ) (hQ : 0 < Q) (hgap : a < b)
    (hη : η ≤ (b - a) / 100) (he : b - 2 * η ≤ e) :
    acceptance e ((a + b) / 2) Q ≤ 1 / 2 - (b - a) / (10 * Q) := by
  unfold acceptance
  have h4 : 0 < 4 * Q := by positivity
  have h10 : 0 < 10 * Q := by positivity
  field_simp
  nlinarith

theorem approximation_yes (p p' γ : ℝ) (hp : 1 / 2 + γ ≤ p)
    (herr : |p' - p| ≤ γ / 10) : 1 / 2 + 9 * γ / 10 ≤ p' := by
  have := (abs_le.mp herr).1
  linarith

theorem approximation_no (p p' γ : ℝ) (hp : p ≤ 1 / 2 - γ)
    (herr : |p' - p| ≤ γ / 10) : p' ≤ 1 / 2 - 9 * γ / 10 := by
  have := (abs_le.mp herr).2
  linarith

theorem subnormalized_no (w p bound : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hp0 : 0 ≤ p) (hp : p ≤ bound) : w * p ≤ bound := by
  calc
    w * p ≤ 1 * p := mul_le_mul_of_nonneg_right hw1 hp0
    _ ≤ bound := by simpa using hp

theorem subnormalized_approximation_no (w p p' γ : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2 - γ) (herr : |p' - w * p| ≤ γ / 10) :
    p' ≤ 1 / 2 - 9 * γ / 10 := by
  exact approximation_no (w * p) p' γ (subnormalized_no w p _ hw hw1 hp0 hp) herr

end Margins

end CM275
