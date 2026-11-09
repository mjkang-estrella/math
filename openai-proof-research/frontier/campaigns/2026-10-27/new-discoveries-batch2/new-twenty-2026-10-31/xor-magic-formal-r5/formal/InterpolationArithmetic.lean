import Literal
namespace XorMagic

theorem interpolation_indices (d a t : ℕ) (hd : 1 ≤ d) (ht : t ≤ d+2*a) :
    ∃ k j : ℕ, k ≤ d ∧ j ≤ a ∧ t = k+2*j := by
  by_cases h : t / 2 ≤ a
  · refine ⟨t % 2, t / 2, ?_, h, ?_⟩ <;> omega
  · refine ⟨t-2*a, a, ?_, le_rfl, ?_⟩ <;> omega

theorem interpolation_degree (d m t : ℕ) (hd : 1 ≤ d) (hm : d+1 ≤ m)
    (ht : d+2*t ≤ 4*m-4-d) :
    ∃ k j : ℕ, k ≤ d ∧ j ≤ m-1-d ∧ d+2*t = d+2*k+4*j := by
  have bound : t ≤ d+2*(m-1-d) := by omega
  obtain ⟨k,j,hk,hj,heq⟩ := interpolation_indices d (m-1-d) t hd bound
  exact ⟨k,j,hk,hj,by omega⟩
end XorMagic
