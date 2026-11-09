module
public import URMatchingSurvivorMatching
public import URMatchingSurvivorObstruction
public import Mathlib.Basic.Real.Basic
@[expose] public section
namespace URMatching
open scoped Classical

theorem survivor_matching_number_large {N h : ℕ} (σ : PermutationTuples N 100)
    (hd : 100 * (removedVertices N h σ).card < N) :
    99 * N < 100 * matchingNumber (survivorGraph h σ) := by
  have hm := card_le_matchingNumber _ (firstMatching_isMatching (h := h) σ)
  have hr := firstMatching_retained σ hd
  omega

theorem survivor_strict_ratio {a h : ℕ} (σ : PermutationTuples (4*a) 100)
    (hd : 100 * (removedVertices (4*a) h σ).card < 4*a)
    (hn : SurvivorNoHole h a σ) :
    (urMatchingNumber (survivorGraph h σ) : ℝ) <
      (3/4 : ℝ) * (matchingNumber (survivorGraph h σ) : ℝ) := by
  have hu := survivor_ur_number_lt σ hn
  have hm := survivor_matching_number_large σ hd
  have hnat : 4 * urMatchingNumber (survivorGraph h σ) <
      3 * matchingNumber (survivorGraph h σ) := by omega
  have hreal : (4 : ℝ) * (urMatchingNumber (survivorGraph h σ) : ℝ) <
      3 * (matchingNumber (survivorGraph h σ) : ℝ) := by exact_mod_cast hnat
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  simpa [mul_comm] using hreal

theorem exists_survivor_strict_ratio (h : ℕ) : ∃ a : ℕ, 0 < a ∧ h ≤ a ∧
    ∃ σ : PermutationTuples (4*a) 100,
      DegreeBound (survivorGraph h σ) 100 ∧
      (urMatchingNumber (survivorGraph h σ) : ℝ) <
        (3/4 : ℝ) * (matchingNumber (survivorGraph h σ) : ℝ) := by
  obtain ⟨a,ha,hh,σ,hd,hdeg,hn⟩ := exists_induced_survivor h
  exact ⟨a,ha,hh,σ,hdeg,survivor_strict_ratio σ hd hn⟩
end URMatching
