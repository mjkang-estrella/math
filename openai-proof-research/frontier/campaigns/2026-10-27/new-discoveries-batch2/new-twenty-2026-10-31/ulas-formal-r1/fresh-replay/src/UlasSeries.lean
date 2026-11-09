import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

open PowerSeries
namespace Ulas
noncomputable def geomStep (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if k ∣ n then 1 else 0
noncomputable def G (N : ℕ) : PowerSeries ℤ :=
  geomStep 1 * ∏ i ∈ Finset.range N, geomStep (2 ^ i)
def Agree (n : ℕ) (f g : PowerSeries ℤ) : Prop :=
  ∀ i ≤ n, coeff i f = coeff i g

theorem agree_mul {n : ℕ} {f g a b : PowerSeries ℤ}
    (h : Agree n f g) (h' : Agree n a b) : Agree n (f*a) (g*b) := by
  intro i hi
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' := Finset.mem_antidiagonal.mp hx
  rw [h x.1 (by omega), h' x.2 (by omega)]

theorem agree_pow {n : ℕ} {f g : PowerSeries ℤ} (h : Agree n f g) (m : ℕ) :
    Agree n (f^m) (g^m) := by
  induction m with
  | zero => intro i hi; rfl
  | succ m ih => simpa only [pow_succ] using agree_mul ih h

theorem geom_agree_one {n k : ℕ} (h : n < k) : Agree n (geomStep k) 1 := by
  intro i hi
  simp only [geomStep, coeff_mk, coeff_one]
  by_cases hz : i = 0
  · simp [hz]
  · have hn : ¬ k ∣ i := fun hd => hz (by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hd; omega)
    simp [hz, hn]

theorem G_succ (N : ℕ) : G (N+1) = G N * geomStep (2^N) := by
  simp [G, Finset.prod_range_succ, mul_assoc]

theorem G_agree (n N : ℕ) (h : n+1 ≤ N) : Agree n (G N) (G (n+1)) := by
  induction N, h using Nat.le_induction with
  | base => intro i hi; rfl
  | succ N h ih =>
    rw [G_succ]
    have hk : n < 2^N := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self.le)
    simpa using agree_mul ih (geom_agree_one hk)

theorem coeff_G_stable (m n N : ℕ) (h : n+1 ≤ N) :
    coeff n ((G N)^m) = coeff n ((G (n+1))^m) :=
  agree_pow (G_agree n N h) m n le_rfl

/-- Coefficientwise stabilized infinite product, including the extra unit-part factor. -/
noncomputable def C : PowerSeries ℤ := mk fun n => coeff n (G (n+1))
noncomputable def c (m n : ℕ) : ℤ := coeff n (C^m)

theorem C_agree (n N : ℕ) (h : n+1 ≤ N) : Agree n C (G N) := by
  intro i hi
  simp only [C, coeff_mk]
  exact (G_agree i N (by omega) i le_rfl).symm

theorem c_eq_finite (m n N : ℕ) (h : n+1 ≤ N) :
    c m n = coeff n ((G N)^m) := agree_pow (C_agree n N h) m n le_rfl
end Ulas
