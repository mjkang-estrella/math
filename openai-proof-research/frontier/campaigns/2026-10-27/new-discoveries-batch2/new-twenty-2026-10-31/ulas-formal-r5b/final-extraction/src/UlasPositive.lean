import UlasReadout
open PowerSeries
namespace Ulas.Round4
def Nonneg (f : PowerSeries ℤ) : Prop := ∀ n, 0 ≤ coeff n f

theorem nonneg_mul {f g : PowerSeries ℤ} (hf : Nonneg f) (hg : Nonneg g) :
    Nonneg (f*g) := by
  intro n
  rw [coeff_mul]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hf a.1) (hg a.2)

theorem nonneg_pow {f : PowerSeries ℤ} (hf : Nonneg f) (m : ℕ) : Nonneg (f^m) := by
  induction m with
  | zero => intro n; simp [coeff_one]; positivity
  | succ m ih => simpa [pow_succ] using nonneg_mul ih hf

theorem geom_nonneg (k : ℕ) : Nonneg (geomStep k) := by
  intro n
  simp only [geomStep, coeff_mk]
  split_ifs <;> norm_num

theorem G_nonneg (N : ℕ) : Nonneg (G N) := by
  induction N with
  | zero => simpa [G] using geom_nonneg 1
  | succ N ih => rw [G_succ]; exact nonneg_mul ih (geom_nonneg _)

theorem C_nonneg : Nonneg C := by
  intro n
  exact (C_agree n (n+1) le_rfl n le_rfl).symm ▸ G_nonneg (n+1) n

/-- Keeping the summand (n,0) supplies a coefficient lower bound. -/
theorem coeff_mul_ge_left {f g : PowerSeries ℤ} (hf : Nonneg f) (hg : Nonneg g)
    (hg0 : coeff 0 g = 1) (n : ℕ) : coeff n f ≤ coeff n (f*g) := by
  rw [coeff_mul]
  have h := Finset.single_le_sum (fun a _ => mul_nonneg (hf a.1) (hg a.2))
    (show (n,0) ∈ Finset.antidiagonal n by simp)
  simpa [hg0] using h

theorem G_pos (N n : ℕ) : 0 < coeff n (G N) := by
  induction N with
  | zero => simp [G, geomStep]
  | succ N ih =>
    rw [G_succ]
    have h := coeff_mul_ge_left (G_nonneg N) (geom_nonneg (2^N)) (by simp [geomStep]) n
    omega

theorem C_pos (n : ℕ) : 0 < coeff n C := by
  rw [C_agree n (n+1) le_rfl n le_rfl]
  exact G_pos _ _

theorem C_difference : (1-X)*C = (1+X)*expand 2 (by decide) C := by
  conv_lhs => rw [C_functional, w, ← one_add_y]
  have h := X_one_add_y
  calc
    _ = ((1-X)*(1+y))*((1+X)*expand 2 (by decide) C) := by ring
    _ = _ := by
      have hh : (1-X)*(1+y) = 1 := by linear_combination -h
      rw [hh, one_mul]

theorem C_step_pos (n : ℕ) :
    0 < coeff n ((1+X)*expand 2 (by decide) C) := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_expand]
    by_cases h : 2 ∣ n
    · have h' : ¬ 2 ∣ n+1 := by omega
      simpa [h, h'] using C_pos (n/2)
    · have h' : 2 ∣ n+1 := by omega
      simpa [h, h'] using C_pos ((n+1)/2)

theorem C_step_nonneg : Nonneg ((1+X)*expand 2 (by decide) C) :=
  fun n => (C_step_pos n).le

theorem c_strict_step (m n : ℕ) : c (m+1) n < c (m+1) (n+1) := by
  have hf : (1-X)*C^(m+1) = ((1+X)*expand 2 (by decide) C)*C^m := by
    rw [pow_succ]
    calc
      _ = ((1-X)*C)*C^m := by ring
      _ = _ := by rw [C_difference]
  have hg0 : coeff 0 (C^m) = 1 := by simp
  have hge := coeff_mul_ge_left C_step_nonneg (nonneg_pow C_nonneg m) hg0 (n+1)
  have hp := C_step_pos (n+1)
  have he := congrArg (coeff (n+1)) hf
  simp only [sub_mul, one_mul, map_sub, coeff_succ_X_mul] at he
  unfold c
  omega

theorem c_strictMono (m : ℕ) (hm : 1 ≤ m) : StrictMono (c m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact strictMono_nat_of_lt_succ (c_strict_step k)

theorem diff_pos (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) : 0 < diff m n := by
  exact sub_pos.mpr (c_strictMono m hm (by omega : n < 4*n))
theorem diff_ne_zero (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) : diff m n ≠ 0 :=
  ne_of_gt (diff_pos m n hm hn)
end Ulas.Round4
