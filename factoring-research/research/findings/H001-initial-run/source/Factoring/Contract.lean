import Std

namespace Factoring

/-- Ordinary binary input length, including one bit for zero. -/
def inputBits (n : Nat) : Nat := n.log2 + 1

def NontrivialFactor (n d : Nat) : Prop := 1 < d ∧ d < n ∧ d ∣ n

instance (n d : Nat) : Decidable (NontrivialFactor n d) :=
  inferInstanceAs (Decidable (1 < d ∧ d < n ∧ d ∣ n))

/-- Composite-input promise; factors need not themselves be prime. -/
def Composite (n : Nat) : Prop := ∃ d, NontrivialFactor n d

def accepts (n d : Nat) : Bool := decide (NontrivialFactor n d)

theorem accepts_iff (n d : Nat) : accepts n d = true ↔ NontrivialFactor n d := by
  simp [accepts]

theorem factor_implies_composite {n d : Nat} (h : NontrivialFactor n d) :
    Composite n := ⟨d, h⟩

theorem factor_has_cofactor {n d : Nat} (h : NontrivialFactor n d) :
    ∃ q, n = d * q := h.2.2

theorem cofactor_smaller {n d : Nat} (h : NontrivialFactor n d) : n / d < n := by
  have h₁ := h.1
  have h₂ := h.2.1
  exact Nat.div_lt_self (by omega) h₁


theorem zero_rejected (n : Nat) : ¬ NontrivialFactor n 0 := by
  simp [NontrivialFactor]

theorem one_rejected (n : Nat) : ¬ NontrivialFactor n 1 := by
  simp [NontrivialFactor]

theorem self_rejected (n : Nat) : ¬ NontrivialFactor n n := by
  simp [NontrivialFactor]

end Factoring
