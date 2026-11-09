import BunState

namespace Bun

/-- Membership transfer through one component of the pure new-index update:
an old index `k ≠ m` lies in `if c then insert m T else T` exactly when it lies
in `T`, for either truth value of the indicator `c`. -/
theorem mem_stepU_component (k m : Nat) (T : Finset Nat) (c : Bool) (hkm : k ≠ m) :
    k ∈ (if c then insert m T else T) ↔ k ∈ T := by
  cases c
  · exact Iff.rfl
  · constructor
    · intro h
      have h' : k ∈ insert m T := h
      rcases Finset.mem_insert.1 h' with he | hk'
      · exact absurd he hkm
      · exact hk'
    · exact fun h => Finset.mem_insert.2 (Or.inr h)

/-- The actual `stepU` update preserves membership of every old index `k ≠ m`
in the layer `σ` selector of the state: both indicator truth values and both
layers are covered, with no finiteness or enumeration assumptions. -/
theorem stepU_old_mem_iff (m k : Nat) (R S : Finset Nat) (x y z σ : Bool) (hkm : k ≠ m) :
    k ∈ sval σ (stepU m R S x y z) ↔ k ∈ sval σ (R, S) := by
  have h1 : (stepU m R S x y z).2
      = if (ind x y z).2 then insert m S else S := rfl
  have h2 : (stepU m R S x y z).1
      = if (ind x y z).1 then insert m R else R := rfl
  have key1 : k ∈ (stepU m R S x y z).1 ↔ k ∈ R := by
    rw [h2]
    exact mem_stepU_component k m R (ind x y z).1 hkm
  have key2 : k ∈ (stepU m R S x y z).2 ↔ k ∈ S := by
    rw [h1]
    exact mem_stepU_component k m S (ind x y z).2 hkm
  cases σ
  · have e1 : sval false (stepU m R S x y z) = (stepU m R S x y z).1 := rfl
    have e2 : sval false (R, S) = R := rfl
    rw [e1, e2]
    exact key1
  · have e1 : sval true (stepU m R S x y z) = (stepU m R S x y z).2 := rfl
    have e2 : sval true (R, S) = S := rfl
    rw [e1, e2]
    exact key2

end Bun

#print axioms Bun.mem_stepU_component
#print axioms Bun.stepU_old_mem_iff
