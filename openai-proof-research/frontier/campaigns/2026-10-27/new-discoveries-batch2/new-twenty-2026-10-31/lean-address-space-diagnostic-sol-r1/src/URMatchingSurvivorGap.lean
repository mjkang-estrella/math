module
public import URMatchingSurvivorMatching
public import URMatchingSurvivorObstruction
@[expose] public section
namespace URMatching
open scoped Classical

theorem survivor_matching_number_large {N h : ℕ} (σ : PermutationTuples N 100)
    (hd : 100 * (removedVertices N h σ).card < N) :
    99 * N < 100 * matchingNumber (survivorGraph h σ) := by
  have hm := card_le_matchingNumber _ (firstMatching_isMatching (h := h) σ)
  have hr := firstMatching_retained σ hd
  omega

theorem survivor_strict_gap {a h : ℕ} (σ : PermutationTuples (4*a) 100)
    (hd : 100 * (removedVertices (4*a) h σ).card < 4*a)
    (hn : SurvivorNoHole h a σ) :
    4 * urMatchingNumber (survivorGraph h σ) <
      3 * matchingNumber (survivorGraph h σ) := by
  have hu := survivor_ur_number_lt σ hn
  have hm := survivor_matching_number_large σ hd
  omega

theorem exists_survivor_strict_gap (h : ℕ) : ∃ a : ℕ, 0 < a ∧ h ≤ a ∧
    ∃ σ : PermutationTuples (4*a) 100,
      DegreeBound (survivorGraph h σ) 100 ∧
      4 * urMatchingNumber (survivorGraph h σ) <
        3 * matchingNumber (survivorGraph h σ) := by
  obtain ⟨a,ha,hh,σ,hd,hdeg,hn⟩ := exists_induced_survivor h
  exact ⟨a,ha,hh,σ,hdeg,survivor_strict_gap σ hd hn⟩
end URMatching
