import BidiskStable
import BidiskReduced
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
namespace ContactPilot
noncomputable section
open MvPolynomial
private abbrev ca : Poly₂ := MvPolynomial.C Complex.I * (1-Z)
private abbrev cb : Poly₂ := 1+Z
private abbrev cc : Poly₂ := MvPolynomial.C Complex.I * (1-W)
private abbrev ce : Poly₂ := 1+W
private theorem deg_add {p q : Poly₂} {j : Fin 2} {a b : ℕ}
    (hp : degreeOf j p ≤ a) (hq : degreeOf j q ≤ b) : degreeOf j (p+q) ≤ max a b :=
  (degreeOf_add_le j p q).trans (max_le_max hp hq)
private theorem deg_sub {p q : Poly₂} {j : Fin 2} {a b : ℕ}
    (hp : degreeOf j p ≤ a) (hq : degreeOf j q ≤ b) : degreeOf j (p-q) ≤ max a b :=
  (degreeOf_sub_le j p q).trans (max_le_max hp hq)
private theorem deg_mul {p q : Poly₂} {j : Fin 2} {a b : ℕ}
    (hp : degreeOf j p ≤ a) (hq : degreeOf j q ≤ b) : degreeOf j (p*q) ≤ a+b :=
  (degreeOf_mul_le j p q).trans (Nat.add_le_add hp hq)
private theorem deg_pow {p : Poly₂} {j : Fin 2} {a : ℕ} (hp : degreeOf j p ≤ a) (n : ℕ) :
    degreeOf j (p^n) ≤ a*n := by simpa [Nat.mul_comm] using (degreeOf_pow_le j p n).trans (Nat.mul_le_mul_left n hp)

private theorem degree_cayleyN_0 : degreeOf 0 cayleyN ≤ 3 := by
  have ha : degreeOf 0 ca ≤ 1 := by
    dsimp [ca, cc]
    apply (degreeOf_mul_le 0 _ _).trans
    simpa [ca, cc, Z, W, degreeOf_X] using Nat.add_le_add (le_refl (degreeOf 0 (MvPolynomial.C Complex.I : Poly₂))) (degreeOf_sub_le 0 (1 : Poly₂) Z)
  have hb : degreeOf 0 cb ≤ 1 := by
    simpa [cb, ce, Z, W, degreeOf_X] using degreeOf_add_le (0 : Fin 2) (1 : Poly₂) Z
  have hc : degreeOf 0 cc ≤ 0 := by
    dsimp [ca, cc]
    apply (degreeOf_mul_le 0 _ _).trans
    simpa [ca, cc, Z, W, degreeOf_X] using Nat.add_le_add (le_refl (degreeOf 0 (MvPolynomial.C Complex.I : Poly₂))) (degreeOf_sub_le 0 (1 : Poly₂) W)
  have he : degreeOf 0 ce ≤ 0 := by
    simpa [cb, ce, Z, W, degreeOf_X] using degreeOf_add_le (0 : Fin 2) (1 : Poly₂) W
  have h : degreeOf 0 ((cb*(((cc*ca)-(cc*cb))-(cb*ce)))*(((cc*ca)+(cc*cb))-(cb*ce))) ≤ _ := (deg_mul (deg_mul hb (deg_sub (deg_sub (deg_mul hc ha) (deg_mul hc hb)) (deg_mul hb he))) (deg_sub (deg_add (deg_mul hc ha) (deg_mul hc hb)) (deg_mul hb he)))
  have hid : ((cb*(((cc*ca)-(cc*cb))-(cb*ce)))*(((cc*ca)+(cc*cb))-(cb*ce))) = cayleyN := by unfold cayleyN; dsimp [ca, cb, cc, ce]; try ring
  rw [hid] at h
  norm_num at h ⊢
  exact h

private theorem degree_cayleyQ_0 : degreeOf 0 cayleyQ ≤ 3 := by
  have ha : degreeOf 0 ca ≤ 1 := by
    dsimp [ca, cc]
    apply (degreeOf_mul_le 0 _ _).trans
    simpa [ca, cc, Z, W, degreeOf_X] using Nat.add_le_add (le_refl (degreeOf 0 (MvPolynomial.C Complex.I : Poly₂))) (degreeOf_sub_le 0 (1 : Poly₂) Z)
  have hb : degreeOf 0 cb ≤ 1 := by
    simpa [cb, ce, Z, W, degreeOf_X] using degreeOf_add_le (0 : Fin 2) (1 : Poly₂) Z
  have hc : degreeOf 0 cc ≤ 0 := by
    dsimp [ca, cc]
    apply (degreeOf_mul_le 0 _ _).trans
    simpa [ca, cc, Z, W, degreeOf_X] using Nat.add_le_add (le_refl (degreeOf 0 (MvPolynomial.C Complex.I : Poly₂))) (degreeOf_sub_le 0 (1 : Poly₂) W)
  have he : degreeOf 0 ce ≤ 0 := by
    simpa [cb, ce, Z, W, degreeOf_X] using degreeOf_add_le (0 : Fin 2) (1 : Poly₂) W
  have h : degreeOf 0 ((((((-((cc^2)*(ca^3)))+((2*(cc^2))*(ca*(cb^2))))+(((4*cc)*(ca^2))*(cb*ce)))+(((2*cc)*ca)*((cb^2)*ce)))-((cc*(cb^3))*ce))-((3*ca)*((cb^2)*(ce^2)))) ≤ _ := (deg_sub (deg_sub (deg_add (deg_add (deg_add (by simpa only [degreeOf_neg] using (deg_mul (deg_pow hc 2) (deg_pow ha 3))) (deg_mul (deg_mul (show degreeOf 0 (2 : Poly₂) ≤ 0 from by rw [show (2 : Poly₂) = MvPolynomial.C (2 : ℂ) by norm_num [map_ofNat]]; simp) (deg_pow hc 2)) (deg_mul ha (deg_pow hb 2)))) (deg_mul (deg_mul (deg_mul (show degreeOf 0 (4 : Poly₂) ≤ 0 from by rw [show (4 : Poly₂) = MvPolynomial.C (4 : ℂ) by norm_num [map_ofNat]]; simp) hc) (deg_pow ha 2)) (deg_mul hb he))) (deg_mul (deg_mul (deg_mul (show degreeOf 0 (2 : Poly₂) ≤ 0 from by rw [show (2 : Poly₂) = MvPolynomial.C (2 : ℂ) by norm_num [map_ofNat]]; simp) hc) ha) (deg_mul (deg_pow hb 2) he))) (deg_mul (deg_mul hc (deg_pow hb 3)) he)) (deg_mul (deg_mul (show degreeOf 0 (3 : Poly₂) ≤ 0 from by rw [show (3 : Poly₂) = MvPolynomial.C (3 : ℂ) by norm_num [map_ofNat]]; simp) ha) (deg_mul (deg_pow hb 2) (deg_pow he 2))))
  have hid : ((((((-((cc^2)*(ca^3)))+((2*(cc^2))*(ca*(cb^2))))+(((4*cc)*(ca^2))*(cb*ce)))+(((2*cc)*ca)*((cb^2)*ce)))-((cc*(cb^3))*ce))-((3*ca)*((cb^2)*(ce^2)))) = cayleyQ := by unfold cayleyQ; dsimp [ca, cb, cc, ce]; try ring
  rw [hid] at h
  norm_num at h ⊢
  exact h

private theorem degree_cayleyN_1 : degreeOf 1 cayleyN ≤ 2 := by
  have ha : degreeOf 1 ca ≤ 0 := by
    dsimp [ca, cc]
    apply (degreeOf_mul_le 1 _ _).trans
    simpa [ca, cc, Z, W, degreeOf_X] using Nat.add_le_add (le_refl (degreeOf 1 (MvPolynomial.C Complex.I : Poly₂))) (degreeOf_sub_le 1 (1 : Poly₂) Z)
  have hb : degreeOf 1 cb ≤ 0 := by
    simpa [cb, ce, Z, W, degreeOf_X] using degreeOf_add_le (1 : Fin 2) (1 : Poly₂) Z
  have hc : degreeOf 1 cc ≤ 1 := by
    dsimp [ca, cc]
    apply (degreeOf_mul_le 1 _ _).trans
    simpa [ca, cc, Z, W, degreeOf_X] using Nat.add_le_add (le_refl (degreeOf 1 (MvPolynomial.C Complex.I : Poly₂))) (degreeOf_sub_le 1 (1 : Poly₂) W)
  have he : degreeOf 1 ce ≤ 1 := by
    simpa [cb, ce, Z, W, degreeOf_X] using degreeOf_add_le (1 : Fin 2) (1 : Poly₂) W
  have h : degreeOf 1 ((cb*(((cc*ca)-(cc*cb))-(cb*ce)))*(((cc*ca)+(cc*cb))-(cb*ce))) ≤ _ := (deg_mul (deg_mul hb (deg_sub (deg_sub (deg_mul hc ha) (deg_mul hc hb)) (deg_mul hb he))) (deg_sub (deg_add (deg_mul hc ha) (deg_mul hc hb)) (deg_mul hb he)))
  have hid : ((cb*(((cc*ca)-(cc*cb))-(cb*ce)))*(((cc*ca)+(cc*cb))-(cb*ce))) = cayleyN := by unfold cayleyN; dsimp [ca, cb, cc, ce]; try ring
  rw [hid] at h
  norm_num at h ⊢
  exact h

private theorem degree_cayleyQ_1 : degreeOf 1 cayleyQ ≤ 2 := by
  have ha : degreeOf 1 ca ≤ 0 := by
    dsimp [ca, cc]
    apply (degreeOf_mul_le 1 _ _).trans
    simpa [ca, cc, Z, W, degreeOf_X] using Nat.add_le_add (le_refl (degreeOf 1 (MvPolynomial.C Complex.I : Poly₂))) (degreeOf_sub_le 1 (1 : Poly₂) Z)
  have hb : degreeOf 1 cb ≤ 0 := by
    simpa [cb, ce, Z, W, degreeOf_X] using degreeOf_add_le (1 : Fin 2) (1 : Poly₂) Z
  have hc : degreeOf 1 cc ≤ 1 := by
    dsimp [ca, cc]
    apply (degreeOf_mul_le 1 _ _).trans
    simpa [ca, cc, Z, W, degreeOf_X] using Nat.add_le_add (le_refl (degreeOf 1 (MvPolynomial.C Complex.I : Poly₂))) (degreeOf_sub_le 1 (1 : Poly₂) W)
  have he : degreeOf 1 ce ≤ 1 := by
    simpa [cb, ce, Z, W, degreeOf_X] using degreeOf_add_le (1 : Fin 2) (1 : Poly₂) W
  have h : degreeOf 1 ((((((-((cc^2)*(ca^3)))+((2*(cc^2))*(ca*(cb^2))))+(((4*cc)*(ca^2))*(cb*ce)))+(((2*cc)*ca)*((cb^2)*ce)))-((cc*(cb^3))*ce))-((3*ca)*((cb^2)*(ce^2)))) ≤ _ := (deg_sub (deg_sub (deg_add (deg_add (deg_add (by simpa only [degreeOf_neg] using (deg_mul (deg_pow hc 2) (deg_pow ha 3))) (deg_mul (deg_mul (show degreeOf 1 (2 : Poly₂) ≤ 0 from by rw [show (2 : Poly₂) = MvPolynomial.C (2 : ℂ) by norm_num [map_ofNat]]; simp) (deg_pow hc 2)) (deg_mul ha (deg_pow hb 2)))) (deg_mul (deg_mul (deg_mul (show degreeOf 1 (4 : Poly₂) ≤ 0 from by rw [show (4 : Poly₂) = MvPolynomial.C (4 : ℂ) by norm_num [map_ofNat]]; simp) hc) (deg_pow ha 2)) (deg_mul hb he))) (deg_mul (deg_mul (deg_mul (show degreeOf 1 (2 : Poly₂) ≤ 0 from by rw [show (2 : Poly₂) = MvPolynomial.C (2 : ℂ) by norm_num [map_ofNat]]; simp) hc) ha) (deg_mul (deg_pow hb 2) he))) (deg_mul (deg_mul hc (deg_pow hb 3)) he)) (deg_mul (deg_mul (show degreeOf 1 (3 : Poly₂) ≤ 0 from by rw [show (3 : Poly₂) = MvPolynomial.C (3 : ℂ) by norm_num [map_ofNat]]; simp) ha) (deg_mul (deg_pow hb 2) (deg_pow he 2))))
  have hid : ((((((-((cc^2)*(ca^3)))+((2*(cc^2))*(ca*(cb^2))))+(((4*cc)*(ca^2))*(cb*ce)))+(((2*cc)*ca)*((cb^2)*ce)))-((cc*(cb^3))*ce))-((3*ca)*((cb^2)*(ce^2)))) = cayleyQ := by unfold cayleyQ; dsimp [ca, cb, cc, ce]; try ring
  rw [hid] at h
  norm_num at h ⊢
  exact h

theorem bidisk_denominator_bounds : ∀ d ∈ bidiskDenominator.support, d 0 ≤ 3 ∧ d 1 ≤ 2 := by
  intro d hd
  unfold bidiskDenominator at hd
  constructor
  · apply (le_degreeOf_of_mem_support 0 hd).trans
    exact (degreeOf_sub_le 0 _ _).trans (max_le degree_cayleyQ_0
      ((degreeOf_mul_le 0 _ _).trans (by simpa using degree_cayleyN_0)))
  · apply (le_degreeOf_of_mem_support 1 hd).trans
    exact (degreeOf_sub_le 1 _ _).trans (max_le degree_cayleyQ_1
      ((degreeOf_mul_le 1 _ _).trans (by simpa using degree_cayleyN_1)))
end
end ContactPilot
