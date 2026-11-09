import StackSortEquivariance
import StackSortAnalysis
import StackSortControls
import StackSortSmall
import StackSortMaximum
open Filter Topology BigOperators
noncomputable section
namespace StackSort
set_option maxRecDepth 10000

/-- OPEN L3: the real form of the source doubling injection. -/
def Doubling : Prop := ∀ a : ℕ, deg a ^ 2 ≤ (2 * a + 1 : ℝ) * deg (2 * a + 1)
/-- OPEN L6 + L7: connect the numerically certified lower-recursion output to the literal count. -/
def Lower130 : Prop := lower130 ≤ P 130
/-- Statement of the now-proved maximum-fibre family bound. -/
def MaxFamilyBound : Prop := ∀ n : ℕ, 2 ^ (n - 1) ≤ maxFib n

/-- L2, discharged below. -/
def Standardisation : Prop := ∀ (φ : ℕ ↪o ℕ) (w : List ℕ),
    s (w.map φ) = (s w).map φ
theorem standardisation_proved : Standardisation := s_map_orderEmbedding
/-- Additional exact intermediate obligation L3, integer form. -/
def DoublingInjection : Prop := ∀ a : ℕ,
    Nat.choose (2 * a) a * P a ^ 2 ≤ P (2 * a + 1)
def seed20 : List ℕ := [1, 1, 4, 26, 224, 2356, 29064, 411172, 6573624, 117448188, 2322885008, 50429847572, 1192782788192, 30533141865700, 841025569061736, 24802500974885020, 779708932637648392, 26028895710444355516, 919586611535156918680, 34279121480711537327388, 1344580237342589147760320]

/-- OPEN L7: exact seeds must come from a proved counting recursion. -/
def ExactSeeds20 : Prop := ∀ n : ℕ, 1 ≤ n → n ≤ 20 → P n = seed20[n]!

/-- Additional exact intermediate obligation L6. -/
def RootSplit : Prop := ∀ n : ℕ, 2 ≤ n →
    4 * P (n - 1) + ∑ i ∈ Finset.Icc 1 (n - 2),
      Nat.choose (n - 1) i * P i * P (n - 1 - i) ≤ P n

/-- The numeric inequality is closed; only its linkage to the pair count is assumed. -/
theorem base130_of_lower (h : Lower130) :
    4 * (130 + 1 : ℝ) * (1.73 : ℝ) ^ (130 + 1) ≤ deg 130 := by
  have hb : (lower130 : ℝ) ≤ P 130 := by exact_mod_cast h
  have hc : (4 * 131 * Nat.factorial 130 * 173 ^ 131 : ℕ) < lower130 * 100 ^ 131 := certificate130
  have hcr : (4 : ℝ) * 131 * (Nat.factorial 130 : ℝ) * 173 ^ 131 <
      (lower130 : ℝ) * 100 ^ 131 := by exact_mod_cast hc
  have hf : (0 : ℝ) < Nat.factorial 130 := by positivity
  unfold deg
  apply (le_div_iff₀ hf).mpr
  rw [show (130 : ℝ) + 1 = 131 by norm_num, show (1.73 : ℝ) = 173 / 100 by norm_num]
  change 4 * 131 * (173 / 100 : ℝ) ^ 131 * (Nat.factorial 130 : ℝ) ≤ (P 130 : ℝ)
  calc
    _ = (4 * 131 * (Nat.factorial 130 : ℝ) * 173 ^ 131) / 100 ^ 131 := by rw [div_pow]; ring
    _ ≤ (lower130 : ℝ) := (div_le_iff₀ (by positivity)).mpr hcr.le
    _ ≤ _ := hb

/-- CONDITIONAL source endpoint: the missing propositions are explicit arguments. -/
theorem subsequence_companion (hD : Doubling) (hB : Lower130) :
    ∀ k, (1.73 : ℝ) < roots (index 130 k) :=
  subsequence_above deg deg_nonneg hD 130 (by norm_num) (base130_of_lower hB)

theorem limit_ge (hD : Doubling) (hB : Lower130) :
    ∀ L, Tendsto (fun n => deg n ^ (1 / (n : ℝ))) atTop (𝓝 L) → (1.73 : ℝ) ≤ L :=
  limit_ge_of_subsequence roots 130 (subsequence_companion hD hB)

theorem nonvacuity (hD : Doubling) (hB : Lower130) :
    ∃ᶠ n in atTop, (1.73 : ℝ) < deg n ^ (1 / (n : ℝ)) :=
  frequently_of_subsequence roots 130 (subsequence_companion hD hB)

theorem mathdb_345545 (hD : Doubling) (hB : Lower130) : ¬ Conj := by
  rintro ⟨L, hL, hi⟩
  exact (not_lt_of_ge (limit_ge hD hB L hL)) hi.2

theorem threshold_pow (n : ℕ) (hn : 5 ≤ n) :
    (1.73 : ℝ) ^ n < 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have he : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [pow_succ, he, pow_succ]
    have hp : (0 : ℝ) < 2 ^ (n - 1) := by positivity
    nlinarith

theorem max_companion :
    ∀ n ≥ 5, (1.73 : ℝ) < (maxFib n : ℝ) ^ (1 / (n : ℝ)) := by
  intro n hn
  have hb : (2 : ℝ) ^ (n - 1) ≤ maxFib n := by exact_mod_cast max_family_bound n
  exact root_gt_of_pow_gt _ (by positivity) n (by omega) ((threshold_pow n hn).trans_le hb)

theorem max_limit_ge (L : ℝ)
    (hL : Tendsto maxRoots atTop (𝓝 L)) : (1.73 : ℝ) ≤ L := by
  apply ge_of_tendsto hL
  filter_upwards [Filter.eventually_ge_atTop 5] with n hn
  exact (max_companion n hn).le

theorem mathdb_345545_max : ¬ ConjMax := by
  rintro ⟨L, hL, hi⟩
  exact (not_lt_of_ge (max_limit_ge L hL)) hi.2
end StackSort
