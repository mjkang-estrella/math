prelude
import Init.Data.Nat.Dvd
import Init.Data.Nat.Lemmas

/-! Small kernel-checked arithmetic start. The literal Jacobi theorem is not
formalized here. Full ordinary proof and remaining bridge plan are separate. -/
namespace JacobiShifted

def Dyadic (p n : Nat) : Prop := ∃ a : Nat, n = 2^p*a

theorem dyadic_mul {p q f g : Nat} (hf : Dyadic p f) (hg : Dyadic q g) :
    Dyadic (p+q) (f*g) := by
  rcases hf with ⟨a, rfl⟩
  rcases hg with ⟨b, rfl⟩
  refine ⟨a*b, ?_⟩
  simp only [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem dyadic_doubled_product {p q f g : Nat} (hf : Dyadic p f) (hg : Dyadic q g) :
    Dyadic (p+q+1) (2*f*g) := by
  rcases hf with ⟨a, rfl⟩
  rcases hg with ⟨b, rfl⟩
  refine ⟨a*b, ?_⟩
  simp only [Nat.pow_add, Nat.pow_one, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem dyadic_weaken {p q f : Nat} (hpq : q ≤ p) (hf : Dyadic p f) :
    Dyadic q f := by
  rcases Nat.exists_eq_add_of_le hpq with ⟨k, hk⟩
  rcases hf with ⟨a, ha⟩
  refine ⟨2^k*a, ?_⟩
  rw [ha, hk, Nat.pow_add, Nat.mul_assoc]

theorem dyadic_square {p f : Nat} (hf : Dyadic p f) : Dyadic p (f*f) := by
  rcases hf with ⟨a, ha⟩
  exact ⟨a*f, by rw [ha]; simp only [Nat.mul_assoc]⟩

theorem dyadic_doubled_product_weaken {p q z f g : Nat}
    (hf : Dyadic p f) (hg : Dyadic q g) (hz : z ≤ p+q+1) :
    Dyadic z (2*f*g) := dyadic_weaken hz (dyadic_doubled_product hf hg)

#print axioms dyadic_mul
#print axioms dyadic_doubled_product
#print axioms dyadic_weaken
#print axioms dyadic_square
#print axioms dyadic_doubled_product_weaken
end JacobiShifted
