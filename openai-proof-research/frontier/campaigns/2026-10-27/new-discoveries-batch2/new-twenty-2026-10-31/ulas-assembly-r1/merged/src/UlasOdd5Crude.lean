import UlasOdd5Transfer
set_option linter.unusedSimpArgs false
open PowerSeries Polynomial
namespace Ulas.Round5Odd
open Round4

theorem fourScaled_sub {F G : Polynomial ℤ} (hF : FourScaled F) (hG : FourScaled G) :
    FourScaled (F-G) := by intro E; simpa using dvd_sub (hF E) (hG E)

theorem fourScaled_mul {F G : Polynomial ℤ} (hF : FourScaled F) (hG : FourScaled G) :
    FourScaled (F*G) := by
  intro E
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  rw [← he, pow_add]
  exact mul_dvd_mul (hF p.1) (hG p.2)

theorem fourScaled_sum {α : Type*} (s : Finset α) (f : α → Polynomial ℤ)
    (h : ∀ a ∈ s, FourScaled (f a)) : FourScaled (∑ a ∈ s, f a) := by
  intro E
  simp only [finsetSum_coeff]
  exact Finset.dvd_sum (fun a ha => h a ha E)

theorem fourScaled_monomial (a : ℤ) (e : ℕ) (ha : (4:ℤ)^e ∣ a) :
    FourScaled (Polynomial.monomial e a) := by
  intro E
  by_cases he : e=E
  · subst E; simpa using ha
  · simp [Polynomial.coeff_monomial,he]

noncomputable def halfTerm (m E : ℕ) : Polynomial ℤ :=
  if E%2=0 then Polynomial.X^(E/2)*(halfPair (m+E/2)).1
  else 2*Polynomial.X^(E/2+1)*(halfPair (m+E/2)).2

noncomputable def halfTransfer (m : ℕ) (G : Polynomial ℤ) : Polynomial ℤ :=
  ∑ E ∈ G.support, Polynomial.C (G.coeff E)*halfTerm m E

theorem halfTransfer_scaled (m : ℕ) (G : Polynomial ℤ) (hG : FourScaled G) :
    FourScaled (halfTransfer m G) := by
  classical
  apply fourScaled_sum
  intro E _
  unfold halfTerm
  split_ifs with he
  · have hd : (4:ℤ)^(E/2) ∣ G.coeff E :=
      dvd_trans (pow_dvd_pow _ (by omega)) (hG E)
    have h := fourScaled_mul (fourScaled_monomial _ _ hd) (halfPair_scaled (m+E/2)).1
    simpa [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc] using h
  · have hd : (4:ℤ)^(E/2+1) ∣ 2*G.coeff E := by
      have hle : E/2+1 ≤ E := by omega
      exact dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow _ hle) (hG E)) 2
    have h := fourScaled_mul (fourScaled_monomial _ _ hd) (halfPair_scaled (m+E/2)).2
    convert h using 1
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
    norm_num
    ring

/-- Crude bound for the half-angle construction, before the missing odd factorization. -/
theorem crude_halfAngle (m : ℕ) (G : Polynomial ℤ) (hG : FourScaled G) (F : ℕ) :
    (2:ℤ)^(2*F+3) ∣ 2*(halfTransfer m G-G).coeff (F+1) := by
  have h := fourScaled_sub (halfTransfer_scaled m G hG) hG (F+1)
  have hp : (2:ℤ)^(2*F+3) = 2*(4:ℤ)^(F+1) := by
    rw [show 2*F+3 = 2*(F+1)+1 by omega, pow_succ', pow_mul]
    norm_num
  rw [hp]
  exact mul_dvd_mul_left 2 h

/-- The square used by the odd initialization has the required coefficient scaling. -/
theorem halfAngle_square_scaled (h : ℕ) : FourScaled ((halfPair h).1^2) := by
  rw [pow_two]
  exact fourScaled_mul (halfPair_scaled h).1 (halfPair_scaled h).1
end Ulas.Round5Odd
