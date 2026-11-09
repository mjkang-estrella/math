import CompletionCore
import FaceCore
import Mathlib.Data.Set.Card
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace TripleCertificates
open FullereneGeometry
theorem active_iff_dot (q : Fin 32 → E) (p : Fin 60 → E)
    (A : Fin 32 → V) (D : ℤ) (P : Fin 60 → Point)
    (hD : (0:ℝ) < D) (hq : ∀ i, rv (A i) = (D:ℝ) • q i)
    (hp : ∀ v, rp (P v) = p v) (hd : ∀ v, 0 < (P v).den) (i : Fin 32) (v : Fin 60) :
    active (A i) D (P v) ↔ dot (q i) (p v) = 1 := by
  have hh := binding_dot q A D hq i (p v)
  rw [← hp v,dot_rp] at hh
  rw [hp v] at hh
  have hd' : (0:ℝ) < (P v).den := by exact_mod_cast hd v
  constructor
  · intro h
    have he := active_real (A i) D (P v) (hd v) h
    rw [hp v] at he
    rw [binding_dot q A D hq] at he
    nlinarith
  · intro h
    rw [h,mul_one] at hh
    have he := (div_eq_iff hd'.ne').mp hh
    exact_mod_cast he

theorem same_of_real_eq (p r : Point) (hp : 0 < p.den) (hr : 0 < r.den)
    (h : rp p = rp r) : same p r := by
  have hp' : (p.den:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hr' : (r.den:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h0 := (div_eq_div_iff hp' hr').mp (congrFun h 0)
  have h1 := (div_eq_div_iff hp' hr').mp (congrFun h 1)
  have h2 := (div_eq_div_iff hp' hr').mp (congrFun h 2)
  constructor
  · change (p.num.x:ℝ)*r.den=(r.num.x:ℝ)*p.den at h0; exact_mod_cast h0
  constructor
  · change (p.num.y:ℝ)*r.den=(r.num.y:ℝ)*p.den at h1; exact_mod_cast h1
  · change (p.num.z:ℝ)*r.den=(r.num.z:ℝ)*p.den at h2; exact_mod_cast h2
end TripleCertificates

namespace FullereneGeometry
theorem section_extremePoints_image {n m : ℕ} (q : Fin n → E) (p : Fin m → E)
    (hv : (poly q).extremePoints ℝ = Set.range p) (I : Fin n → Finset (Fin m))
    (hi : ∀ i v, v ∈ I i ↔ dot (q i) (p v) = 1) (i : Fin n) :
    (facetSection q i).extremePoints ℝ = p '' (↑(I i) : Set (Fin m)) := by
  rw [section_extremePoints_of_complete q p hv]
  ext x
  constructor
  · rintro ⟨⟨v,rfl⟩,hx⟩; exact ⟨v,(hi i v).mpr hx,rfl⟩
  · rintro ⟨v,hv,rfl⟩; exact ⟨⟨v,rfl⟩,(hi i v).mp hv⟩
end FullereneGeometry
