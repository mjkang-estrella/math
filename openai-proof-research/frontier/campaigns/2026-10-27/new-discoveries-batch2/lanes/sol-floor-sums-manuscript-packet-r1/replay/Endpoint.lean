import SourceBridge
import Dag276
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
namespace Assembly
theorem query_of_neg_bound (m H : ℕ) (hm : 0 < m) (hH : 1 ≤ H) (hHm : H ≤ m)
    (a : Fin 4 → ℕ) (ha : ∀ i, a i < m) (hs : Monotone a)
    (hneg : FloorSums.clampedSum m H a < -3 * ((m/3 : ℕ) : ℤ)) : Query (sourceEnv m H a) := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have s01 := hs (show (0 : Fin 4) ≤ 1 by decide)
  have s12 := hs (show (1 : Fin 4) ≤ 2 by decide)
  have s23 := hs (show (2 : Fin 4) ≤ 3 by decide)
  have hr := Nat.mod_lt m (show 0 < 3 by decide)
  have hd := Nat.mod_add_div m 3
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · change ((H : ℤ) ≤ (m : ℤ))
    omega
  · change ((a 1 : ℤ) ≤ (a 2 : ℤ))
    omega
  · change ((a 0 : ℤ) ≤ (a 1 : ℤ))
    omega
  · change ((H : ℤ) ≥ (1 : ℤ))
    omega
  · change (((m/3 : ℕ) : ℤ) ≥ (0 : ℤ))
    omega
  · change ((m : ℤ) ≥ (1 : ℤ))
    omega
  · change ((a 2 : ℤ) ≤ (a 3 : ℤ))
    omega
  · change ((a 1 : ℤ) ≥ (0 : ℤ))
    omega
  · change ((a 0 : ℤ) ≥ (0 : ℤ))
    omega
  · change ((m : ℤ) ≤ (((3 : ℤ) * ((m/3 : ℕ) : ℤ)) + (2 : ℤ)))
    omega
  · change ((a 3 : ℤ) ≥ (0 : ℤ))
    omega
  · change ((a 2 : ℤ) ≥ (0 : ℤ))
    omega
  · change ((a 0 : ℤ) < (m : ℤ))
    omega
  · change ((a 1 : ℤ) < (m : ℤ))
    omega
  · change ((a 2 : ℤ) < (m : ℤ))
    omega
  · change ((a 3 : ℤ) < (m : ℤ))
    omega
  · change e11660 (sourceEnv m H a) < -3 * ((m/3 : ℕ) : ℤ)
    rw [sum_match]
    exact hneg
theorem sorted_clamped_bound : FloorSums.SortedClampedBound := by
  intro m H hm hH hHm a ha hs
  by_contra hb
  have hneg : FloorSums.clampedSum m H a < -3 * ((m/3 : ℕ) : ℤ) := lt_of_not_ge hb
  exact n22671 (sourceEnv m H a) (query_of_neg_bound m H hm hH hHm a ha hs hneg)
theorem literal_endpoint : FloorSums.LiteralEndpoint := FloorSums.endpoint_of_sorted_clamped_bound sorted_clamped_bound
end Assembly
