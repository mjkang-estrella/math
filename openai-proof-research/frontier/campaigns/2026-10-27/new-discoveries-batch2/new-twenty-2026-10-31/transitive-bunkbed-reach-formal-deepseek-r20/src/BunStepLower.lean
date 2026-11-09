import BunState

namespace Bun

theorem stepU_lower_closed (m u k : Nat) (R S : Finset Nat) (x y z : Bool) (sigma : Bool)
    (hR : ∀ a ∈ R, u ≤ a) (hS : ∀ a ∈ S, u ≤ a) (hm : u ≤ m)
    (hk : k ∈ sval sigma (stepU m R S x y z)) : u ≤ k := by
  have h0 : sval sigma (stepU m R S x y z)
      = if sigma then (stepU m R S x y z).2 else (stepU m R S x y z).1 := rfl
  rw [h0] at hk
  split at hk
  · have hk2 : k ∈ (if (ind x y z).2 then insert m S else S) := hk
    split at hk2
    · rcases Finset.mem_insert.1 hk2 with rfl | hk2
      · exact hm
      · exact hS _ hk2
    · exact hS _ hk2
  · have hk1 : k ∈ (if (ind x y z).1 then insert m R else R) := hk
    split at hk1
    · rcases Finset.mem_insert.1 hk1 with rfl | hk1
      · exact hm
      · exact hR _ hk1
    · exact hR _ hk1

end Bun
