import StackSortBasic
open Filter Topology
noncomputable section
namespace StackSort
/-- Explicit dyadic index, written recursively to avoid subtraction in iteration. -/
def index (a : ℕ) (k : ℕ) : ℕ := Nat.rec a (fun _ t => 2 * t + 1) k

@[simp] theorem index_zero (a : ℕ) : index a 0 = a := rfl
@[simp] theorem index_succ (a k : ℕ) : index a (k+1) = 2 * index a k + 1 := rfl

theorem index_formula (a k : ℕ) : index a k + 1 = (a + 1) * 2 ^ k := by
  induction k with
  | zero => simp [index_zero]
  | succ k ih =>
    simp only [index_succ, pow_succ]
    nlinarith

theorem index_strictMono (a : ℕ) : StrictMono (index a) := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [index_succ]
  omega

/-- L4, independently of the missing combinatorial proof of doubling. -/
theorem iteration (d : ℕ → ℝ)
    (hd : ∀ n, 0 ≤ d n)
    (hdouble : ∀ n, d n ^ 2 ≤ (2 * n + 1 : ℝ) * d (2 * n + 1))
    (a : ℕ) (c : ℝ) (hc : 0 ≤ c) (hbase : 4 * (a + 1 : ℝ) * c ≤ d a) :
    ∀ k, 4 * (index a k + 1 : ℝ) * c ^ (2 ^ k) ≤ d (index a k) := by
  intro k
  induction k with
  | zero => simpa [index_zero, index_succ] using hbase
  | succ k ih =>
    have hn : (0 : ℝ) ≤ index a k := Nat.cast_nonneg _
    have hp : 0 ≤ c ^ (2 ^ k) := pow_nonneg hc _
    have hs := sq_le_sq₀ (by positivity : 0 ≤ 4 * (index a k + 1 : ℝ) * c ^ (2 ^ k))
      (hd (index a k))
    have hsq := hs.mpr ih
    have hdb := hdouble (index a k)
    have hpow : c ^ (2 ^ (k + 1)) = (c ^ (2 ^ k)) ^ 2 := by
      rw [pow_succ, pow_mul]
    simp only [index_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hpow]
    have hcoef : (2 * (index a k : ℝ) + 1) * (4 * (2 * (index a k : ℝ) + 1 + 1)) ≤
        (4 * ((index a k : ℝ) + 1)) ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (c ^ (2 ^ k)))
    have hpos : 0 < 2 * (index a k : ℝ) + 1 := by positivity
    apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      _ ≤ (4 * ((index a k : ℝ) + 1) * c ^ (2 ^ k)) ^ 2 := by convert hh using 1 <;> ring
      _ ≤ _ := hsq.trans hdb

/-- Generic analytic consequence of an explicit infinite subsequence. -/
theorem limit_ge_of_subsequence (u : ℕ → ℝ) (a : ℕ)
    (hu : ∀ k, (1.73 : ℝ) < u (index a k)) (L : ℝ)
    (hL : Tendsto u atTop (𝓝 L)) : 1.73 ≤ L := by
  apply ge_of_tendsto (hL.comp (index_strictMono a).tendsto_atTop)
  exact Filter.Eventually.of_forall (fun k => (hu k).le)

theorem frequently_of_subsequence (u : ℕ → ℝ) (a : ℕ)
    (hu : ∀ k, (1.73 : ℝ) < u (index a k)) :
    ∃ᶠ n in atTop, (1.73 : ℝ) < u n := by
  rw [Filter.frequently_atTop]
  intro N
  exact ⟨index a N, (index_strictMono a).id_le N, hu N⟩
theorem root_gt_of_pow_gt (d : ℝ) (hd : 0 ≤ d) (n : ℕ) (hn : 0 < n)
    (hp : (1.73 : ℝ) ^ n < d) : 1.73 < d ^ (1 / (n : ℝ)) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (Real.rpow_lt_rpow_iff (by positivity : (0 : ℝ) ≤ 1.73 ^ n) hd
    (one_div_pos.mpr hnr)).mpr hp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1.73)] at h
  simpa [ne_of_gt hnr] using h

theorem subsequence_above (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hdouble : ∀ n, d n ^ 2 ≤ (2 * n + 1 : ℝ) * d (2 * n + 1))
    (a : ℕ) (ha : 0 < a)
    (hbase : 4 * (a + 1 : ℝ) * (1.73 : ℝ) ^ (a + 1) ≤ d a) :
    ∀ k, 1.73 < d (index a k) ^ (1 / (index a k : ℝ)) := by
  intro k
  have hn : 0 < index a k := lt_of_lt_of_le ha ((index_strictMono a).monotone (Nat.zero_le k))
  have hi := iteration d hd hdouble a ((1.73 : ℝ) ^ (a + 1)) (by positivity) hbase k
  rw [← pow_mul, ← index_formula] at hi
  have hq : 0 < (1.73 : ℝ) ^ index a k := by positivity
  have hcoef : 1 < 4 * (index a k + 1 : ℝ) * (1.73 : ℝ) := by
    have : (0 : ℝ) ≤ index a k := Nat.cast_nonneg _
    nlinarith
  have hp : (1.73 : ℝ) ^ index a k < d (index a k) := by
    rw [pow_succ] at hi
    nlinarith [mul_lt_mul_of_pos_right hcoef hq]
  exact root_gt_of_pow_gt _ (hd _) _ hn hp
end StackSort
