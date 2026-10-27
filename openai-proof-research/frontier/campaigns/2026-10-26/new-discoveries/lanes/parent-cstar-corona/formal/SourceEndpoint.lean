import LocalSeries
import Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace CStarCorona

def SourceHolomorphic (f : A → A) : Prop :=
  ∀ a : A, ‖a‖ < 1 → ∃ r : ℝ, 0 < r ∧
    (∀ z : A, ‖z - a‖ < r → ‖z‖ < 1) ∧ ∃ b : ℕ → A,
      ∀ z : A, ‖z - a‖ < r → HasSum (fun n => b n * (z - a) ^ n) (f z)

def SourceBounded (f : A → A) : Prop :=
  ∃ C : ℝ, ∀ z : A, ‖z‖ < 1 → ‖f z‖ ≤ C

def SourceCoronaClaim : Prop :=
  ∀ (n : ℕ) (f : Fin (n + 1) → A → A),
    (∀ i, SourceHolomorphic (f i) ∧ SourceBounded (f i)) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ z : A, ‖z‖ < 1 →
      algebraMap ℝ A δ ≤ ∑ i, f i z * star (f i z) ∧
      algebraMap ℝ A δ ≤ ∑ i, star (f i z) * f i z) →
    ∃ (g h : Fin (n + 1) → A → A),
      (∀ i, SourceHolomorphic (g i) ∧ SourceBounded (g i) ∧
        SourceHolomorphic (h i) ∧ SourceBounded (h i)) ∧
      ∀ z : A, ‖z‖ < 1 → (∑ i, f i z * g i z) = 1 ∧ (∑ i, h i z * f i z) = 1

def affineCoefficients (a : A) (n : ℕ) : A :=
  if n = 0 then witness a else if n = 1 then coeff else 0

theorem witness_local_series (a z : A) :
    HasSum (fun n => affineCoefficients a n * (z - a) ^ n) (witness z) := by
  have ht : HasSum (fun n => affineCoefficients a n * (z - a) ^ n)
      (∑ n ∈ Finset.range 2, affineCoefficients a n * (z - a) ^ n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    have hn2 : 2 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    simp [affineCoefficients, show n ≠ 0 by omega, show n ≠ 1 by omega]
  have he : (∑ n ∈ Finset.range 2, affineCoefficients a n * (z - a) ^ n) =
      witness z := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [affineCoefficients, witness]
    noncomm_ring
  exact he ▸ ht

theorem witness_source_holomorphic : SourceHolomorphic witness := by
  intro a ha
  refine ⟨(1 - ‖a‖) / 2, by positivity, ?_, affineCoefficients a, ?_⟩
  · intro z hz
    have he : ‖z‖ ≤ ‖z - a‖ + ‖a‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - a) a
    linarith
  · intro z _
    exact witness_local_series a z

theorem witness_source_bounded : SourceBounded witness :=
  ⟨5 / 4, witness_norm_bound⟩

theorem source_holomorphic_local_zero (g : A → A) (hg : SourceHolomorphic g) :
    LocalPowerAtZero g := by
  obtain ⟨r, hr, _, b, hb⟩ := hg 0 (by simp)
  refine ⟨r, hr, b, ?_⟩
  intro z hz
  simpa only [sub_zero] using hb z (by simpa only [sub_zero] using hz)

theorem source_counterexample : ¬SourceCoronaClaim := by
  intro hc
  have hf : ∀ i : Fin 1, SourceHolomorphic ((fun _ : Fin 1 => witness) i) ∧
      SourceBounded ((fun _ : Fin 1 => witness) i) := by
    intro _
    exact ⟨witness_source_holomorphic, witness_source_bounded⟩
  have hl : ∃ δ : ℝ, 0 < δ ∧ ∀ z : A, ‖z‖ < 1 →
      algebraMap ℝ A δ ≤ ∑ i : Fin 1, witness z * star (witness z) ∧
      algebraMap ℝ A δ ≤ ∑ i : Fin 1, star (witness z) * witness z := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro z hz
    simpa using witness_order_bounds z hz
  obtain ⟨g, _, hg, hinv⟩ := hc 0 (fun _ => witness) hf hl
  apply no_local_power_right_inverse (g 0) (source_holomorphic_local_zero _ (hg 0).1)
  intro z hz
  simpa using (hinv z hz).1

end CStarCorona
