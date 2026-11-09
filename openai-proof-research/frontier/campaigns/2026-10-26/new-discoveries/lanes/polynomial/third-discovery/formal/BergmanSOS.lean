import BergmanWeight
import BergmanSource

open Finset
namespace BergmanUnitCircle

lemma triangular_sum_sos {m n : ℕ} (hmn : n < m) {z : ℂ} (hz : ‖z‖=1) :
    (∑ r ∈ range (2*m-1), ∑ q ∈ range (2*m-1),
      (BergmanConvolution.triangle m r * BergmanConvolution.triangle m q) •
        coefficientWeight m n r q z) = z^(m-n)*(gram m n z:ℂ) := by
  have hm : 0 < m := by omega
  rw [BergmanConvolution.triangle_sum_reflected m hm]
  calc
    _ = ∑ p ∈ range m, ∑ p' ∈ range m, ∑ q ∈ range m, ∑ q' ∈ range m,
        z^(m-n)*(if ((m-n)*p+q)%m=((m-n)*p'+q')%m then
          z^(((m-n)*p+q)/m)*star (z^(((m-n)*p'+q')/m)) else 0) := by
      apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro p' hp'
      apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro q' hq'
      exact reflected_weight hmn (mem_range.mp hp') (mem_range.mp hq') hz
    _ = z^(m-n)*(∑ p ∈ range m, ∑ p' ∈ range m, ∑ q ∈ range m, ∑ q' ∈ range m,
        if ((m-n)*p+q)%m=((m-n)*p'+q')%m then
          z^(((m-n)*p+q)/m)*star (z^(((m-n)*p'+q')/m)) else 0) := by
      simp only [mul_sum]
    _ = z^(m-n)*(∑ r ∈ range m, A m n r z*star (A m n r z)) := by
      rw [four_sum_gram hmn]
    _ = _ := by simp [gram,Complex.mul_conj]

lemma compressedQ_sos {m n : ℕ} (hmn : n < m) {z : ℂ} (hz : ‖z‖=1) :
    compressedQ m n z = z^(m-n)*(gram m n z:ℂ) := by
  rw [← triangular_sum_sos hmn hz]
  unfold compressedQ coefficientWeight
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro q _
  rw [D_nat_cast,D_nat_cast]
  split_ifs <;> simp [nsmul_eq_mul]

/-- Exact sum of squares of the literal source diagonal polynomial, for all coprime pairs. -/
theorem sourceQ_sos {m n : ℕ} (hn : 0 < n) (hmn : n < m) {z : ℂ} (hz : ‖z‖=1) :
    sourceQ m n z = z^(m-n)*(gram m n z:ℂ) := by
  have hnz : z≠0 := by intro he; simp [he] at hz
  rw [sourceQ_eq_compressedQ hn hmn hnz,compressedQ_sos hmn hz]

/-- The full source nonvanishing conjecture, without a sum-of-squares hypothesis. -/
theorem source_conjecture_368572 {m n : ℕ} (hn : 0 < n) (hmn : n < m)
    (hcop : Nat.Coprime m n) {z : ℂ} (hz : ‖z‖=1) : sourceQ m n z≠0 := by
  rw [sourceQ_sos hn hmn hz]
  have hnz : z≠0 := by intro he; simp [he] at hz
  have hg : 0 < gram m n z := gram_pos hn hmn hcop hnz
  apply mul_ne_zero (pow_ne_zero _ hnz)
  exact_mod_cast (ne_of_gt hg)

end BergmanUnitCircle
