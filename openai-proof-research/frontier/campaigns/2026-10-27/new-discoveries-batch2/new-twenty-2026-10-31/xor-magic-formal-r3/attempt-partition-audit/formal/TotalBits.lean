import Literal
namespace XorMagic

theorem total_bits {n : ℕ} (hn : 2 ≤ n) : (∑ x : Bits n, x) = 0 := by
  classical
  ext i
  simp only [Finset.sum_apply, Pi.zero_apply]
  have hi : ∃ j : Fin n, j ≠ i := by
    by_cases h : i = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by simp [h, Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
  obtain ⟨j, hji⟩ := hi
  let flip : Bits n → Bits n := fun x => Function.update x j (x j + 1)
  apply Finset.sum_involution (fun x _ => flip x)
  · intro x _
    simp only [flip, Function.update_of_ne (Ne.symm hji)]
    exact CharTwo.add_self_eq_zero (x i)
  · intro x _ _ heq
    have he := congrFun heq j
    simp only [flip, Function.update_self] at he
    have : (1 : ZMod 2) = 0 := by linear_combination he
    exact (by decide : (1 : ZMod 2) ≠ 0) this
  · intro x _
    exact Finset.mem_univ _
  · intro x _
    ext k
    by_cases hk : k = j
    · subst k
      simp [flip, add_assoc, show (1 : ZMod 2) + 1 = 0 by decide]
    · simp [flip, Function.update_of_ne hk]

theorem total_labels {V : Type} [Fintype V] {n : ℕ} (hn : 2 ≤ n)
    (l : V ≃ Bits n) : (∑ v, l v) = 0 := by
  rw [Equiv.sum_comp l (fun x : Bits n => x)]
  exact total_bits hn
end XorMagic
