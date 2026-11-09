import CMDRRCounts

namespace CMDRR
variable {α : Type} [Fintype α]
theorem count_partition (p q : α → Prop) :
    count (fun x => p x ∧ q x) + count (fun x => p x ∧ ¬ q x) = count p := by
  classical
  have h1 : count (fun x => p x ∧ q x) =
      ((Finset.univ.filter p).filter q).card := by
    unfold count
    congr 1
    ext x
    simp
  have h2 : count (fun x => p x ∧ ¬ q x) =
      ((Finset.univ.filter p).filter (fun x => ¬ q x)).card := by
    unfold count
    congr 1
    ext x
    simp
  rw [h1,h2]
  exact Finset.card_filter_add_card_filter_not q

theorem count_perm (p : α → Prop) (f : Equiv.Perm α) :
    count (fun x => p (f x)) = count p := by
  classical
  let e : {x // p (f x)} ≃ {x // p x} :=
    { toFun := fun x => ⟨f x.1,x.2⟩
      invFun := fun x => ⟨f.symm x.1,by simpa using x.2⟩
      left_inv := fun x => by apply Subtype.ext; exact f.symm_apply_apply x.1
      right_inv := fun x => by apply Subtype.ext; exact f.apply_symm_apply x.1 }
  rw [count_eq_card,count_eq_card]
  exact Fintype.card_congr e

/-- Degree balance on two equally sized parts: the number of internal
directed edges in one part equals that in its complement. This holds for
any permutation, so in particular for an actual spouse row. -/
theorem complementary_internal_edges (p : α → Prop) (f : Equiv.Perm α)
    (hc : count p = count (fun x => ¬ p x)) :
    count (fun x => p x ∧ p (f x)) =
      count (fun x => ¬ p x ∧ ¬ p (f x)) := by
  have h1 := count_partition p (fun x => p (f x))
  have h2 := count_partition (fun x => ¬ p (f x)) p
  have he := count_perm (fun x => ¬ p x) f
  have he1 := count_congr (fun x : α =>
    (and_comm : (¬ p (f x) ∧ p x) ↔ (p x ∧ ¬ p (f x))))
  have he2 := count_congr (fun x : α =>
    (and_comm : (¬ p (f x) ∧ ¬ p x) ↔ (¬ p x ∧ ¬ p (f x))))
  omega
end CMDRR
