import MaskBridge
set_option autoImplicit false
namespace Polyomino57.Diagonal.FiniteProof.Packed
def halfCheck (k n : ℕ) (table : ℕ → ℕ) (u : ℕ) : Bool :=
  (submasks k u).all (fun a => if a = 0 ∨ a = u ∨ u ^^^ a < a then true
    else bitCheck n (table a) (table (u ^^^ a)) (table u))
theorem bitCheck_comm (n a b c : ℕ) : bitCheck n a b c = bitCheck n b a c := by
  simp only [bitCheck, slack, Nat.add_comm a b]
  rfl
theorem halfCheck_sound {k n : ℕ} {table : ℕ → ℕ}
    (checked : ∀ u < 2^k, halfCheck k n table u = true)
    (A B : Finset ℕ) (hA : A ⊆ Finset.range k) (hB : B ⊆ Finset.range k)
    (hneA : A.Nonempty) (hneB : B.Nonempty) (hd : Disjoint A B) :
    bitCheck n (rowOf k table A) (rowOf k table B) (rowOf k table (A ∪ B)) = true := by
  have one : ∀ A B : Finset ℕ, A ⊆ Finset.range k → B ⊆ Finset.range k →
      A.Nonempty → B.Nonempty → Disjoint A B → encode k A ≤ encode k B →
      bitCheck n (rowOf k table A) (rowOf k table B) (rowOf k table (A ∪ B)) = true := by
    intro A B hA hB hneA hneB hd ho
    have hu := checked (encode k (A ∪ B)) (encode_lt _ _)
    have ham : encode k A ∈ submasks k (encode k (A ∪ B)) := by
      apply encode_mem_submasks
      intro i hi ha
      simp [encode_bit, hi, ha]
    have hx := encode_complement (k := k) hd
    have han := encode_nonzero hA hneA
    have hab : encode k A ≠ encode k (A ∪ B) := by
      intro he
      rw [← he, Nat.xor_self] at hx
      exact encode_nonzero hB hneB hx.symm
    simp only [halfCheck, List.all_eq_true] at hu
    have hp := hu _ ham
    simp only [han, hab, hx, not_lt.mpr ho, or_self, ite_false] at hp
    exact hp
  by_cases ho : encode k A ≤ encode k B
  · exact one A B hA hB hneA hneB hd ho
  · have hp := one B A hB hA hneB hneA hd.symm (by omega)
    rw [Finset.union_comm B A] at hp
    rw [rowOf, rowOf, rowOf, bitCheck_comm] at hp
    exact hp
end Polyomino57.Diagonal.FiniteProof.Packed
