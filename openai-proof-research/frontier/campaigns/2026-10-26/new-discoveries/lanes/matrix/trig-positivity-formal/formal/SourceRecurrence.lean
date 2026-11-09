import SourceCoefficients
open PowerSeries Finset
open scoped PowerSeries
namespace TrigSource

noncomputable def euler (B : PowerSeries ℝ) : PowerSeries ℝ := X*derivative B

lemma coeff_euler (B : PowerSeries ℝ) (k : ℕ) : coeff k (euler B)=(k:ℝ)*coeff k B := by
  cases k with
  | zero => simp [euler, coeff_zero_eq_constantCoeff_apply]
  | succ k => rw [euler, coeff_succ_X_mul, coeff_derivative]; push_cast; ring

lemma root_euler_ode (D : ℕ) (hD : 0<D) (B : PowerSeries ℝ)
    (hroot : B^2*(1-X)=1-X^D) :
    2*(euler B-X*euler B-X^D*euler B+X^(D+1)*euler B) =
      X*B+C ((D:ℝ)-1)*(X^(D+1)*B)-C (D:ℝ)*(X^D*B) := by
  have ho := root_ode D hD B hroot
  have hx : (X:PowerSeries ℝ)^(D-1)*X=X^D := by rw [← pow_succ]; congr 1; omega
  simp only [smul_eq_C_mul, map_sub, map_one, map_natCast] at ho ⊢
  unfold euler
  rw [pow_succ, ← hx]
  rw [← hx] at ho
  linear_combination X*ho

/-- The exact corrected four-term recurrence, without division or negative indices. -/
def CoeffRec (D : ℕ) (a : ℕ → ℝ) (k : ℕ) : Prop :=
  (2*(k:ℝ))*a k = (2*(k:ℝ)-1)*a (k-1)
    +(if D≤k then (2*(k:ℝ)-3*(D:ℝ))*a (k-D) else 0)
    -(if D+1≤k then (2*(k:ℝ)-3*(D:ℝ)-1)*a (k-D-1) else 0)

lemma root_coeff_recurrence (D : ℕ) (hD : 0<D) (B : PowerSeries ℝ)
    (hroot : B^2*(1-X)=1-X^D) (k : ℕ) (hk : 1≤k) :
    CoeffRec D (fun j => coeff j B) k := by
  have ho := congrArg (fun F : PowerSeries ℝ => coeff k F) (root_euler_ode D hD B hroot)
  have hX (F : PowerSeries ℝ) : coeff k (X*F)=coeff (k-1) F := by
    have hkk : k=(k-1)+1 := by omega
    rw [hkk, coeff_succ_X_mul]
    congr 1
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_C_mul, hX,
    coeff_X_pow_mul', coeff_euler] at ho
  have hC : coeff k ((C (D:ℝ)-C 1)*(X^(D+1)*B)) =
      ((D:ℝ)-1)*(if D+1≤k then coeff (k-(D+1)) B else 0) := by
    rw [← map_sub, coeff_C_mul, coeff_X_pow_mul']
  rw [hC] at ho
  unfold CoeffRec
  by_cases h1 : D≤k
  · by_cases h2 : D+1≤k
    · simp only [h1, h2, ite_true] at ho ⊢
      have hs1 : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub hk]; norm_num
      have hsD : ((k-D:ℕ):ℝ)=(k:ℝ)-(D:ℝ) := by rw [Nat.cast_sub h1]
      have hsD1 : ((k-(D+1):ℕ):ℝ)=(k:ℝ)-(D:ℝ)-1 := by rw [Nat.cast_sub h2]; push_cast; ring
      have hi : k-(D+1)=k-D-1 := by omega
      rw [hs1, hsD, hsD1, hi] at ho
      linear_combination ho
    · simp only [h1, h2, ite_true, ite_false] at ho ⊢
      have hs1 : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub hk]; norm_num
      have hsD : ((k-D:ℕ):ℝ)=(k:ℝ)-(D:ℝ) := by rw [Nat.cast_sub h1]
      rw [hs1, hsD] at ho
      linear_combination ho
  · have h2 : ¬D+1≤k := by omega
    simp only [h1, h2, ite_false] at ho ⊢
    have hs1 : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub hk]; norm_num
    rw [hs1] at ho
    linear_combination ho

lemma recurrence_unique_upto {D N : ℕ} (hD : 0<D) {a b : ℕ → ℝ}
    (h0 : a 0=b 0)
    (ha : ∀ k, 1≤k → k≤N → CoeffRec D a k)
    (hb : ∀ k, 1≤k → k≤N → CoeffRec D b k) :
    ∀ k, k≤N → a k=b k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkN
    by_cases hk0 : k=0
    · simpa [hk0] using h0
    · have hk : 1≤k := by omega
      have ha' := ha k hk hkN
      have hb' := hb k hk hkN
      unfold CoeffRec at ha' hb'
      have hp : a (k-1)=b (k-1) := ih _ (by omega) (by omega)
      have h1 : (if D≤k then (2*(k:ℝ)-3*(D:ℝ))*a (k-D) else 0)=
          (if D≤k then (2*(k:ℝ)-3*(D:ℝ))*b (k-D) else 0) := by
        split_ifs with h
        · rw [ih (k-D) (by omega) (by omega)]
        · rfl
      have h2 : (if D+1≤k then (2*(k:ℝ)-3*(D:ℝ)-1)*a (k-D-1) else 0)=
          (if D+1≤k then (2*(k:ℝ)-3*(D:ℝ)-1)*b (k-D-1) else 0) := by
        split_ifs with h
        · rw [ih (k-D-1) (by omega) (by omega)]
        · rfl
      rw [hp, h1, h2] at ha'
      have hpos : (0:ℝ)<k := by exact_mod_cast hk
      nlinarith

end TrigSource
