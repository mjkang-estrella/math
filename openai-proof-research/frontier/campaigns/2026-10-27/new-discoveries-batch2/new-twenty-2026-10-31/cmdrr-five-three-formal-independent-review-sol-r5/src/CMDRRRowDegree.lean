import CMDRRSpouseCycles
import CMDRRDegree

open scoped Classical
namespace CMDRR.Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)

noncomputable def rowSinglesEquiv (m : Fin 5) (hm : m.val < 3) :
    Fin 2 ≃ {w : Row (s := canonical) m // 3 ≤ w.1.val} where
  toFun t := ⟨⟨⟨3+t.val,by omega⟩,by
    change ¬ (m = _ ∧ m.val < 3)
    rintro ⟨he,_⟩
    have hh := congrArg Fin.val he
    simp only at hh
    omega⟩,by simp⟩
  invFun w := ⟨w.1.1.val-3,by have hh := w.1.1.isLt; have hg := w.2; omega⟩
  left_inv t := by apply Fin.ext; simp
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    have hg := w.2
    simp only
    omega

theorem row_singles_card (m : Fin 5) (hm : m.val < 3) :
    count (fun w : Row (s := canonical) m => 3 ≤ w.1.val) = 2 := by
  classical
  rw [count_eq_card]
  exact @Fintype.card_congr _ (Fin 2)
    (@Subtype.fintype (Row (s := canonical) m) (fun w => 3 ≤ w.1.val)
      (fun _ => Classical.propDecidable _) inferInstance)
    inferInstance (rowSinglesEquiv m hm).symm

theorem row_complementary_degree (m : Fin 5) (hm : m.val < 3) :
    count (fun w : Row (s := canonical) m =>
      3 ≤ w.1.val ∧ 3 ≤ (h.rowPerm m w).1.val) =
    count (fun w : Row (s := canonical) m =>
      ¬ 3 ≤ w.1.val ∧ ¬ 3 ≤ (h.rowPerm m w).1.val) := by
  classical
  apply complementary_internal_edges
  have hp := row_singles_card m hm
  have ht := count_partition (fun _ : Row (s := canonical) m => True)
    (fun w => 3 ≤ w.1.val)
  have h1 := count_congr (fun w : Row (s := canonical) m =>
    (show (True ∧ 3 ≤ w.1.val) ↔ 3 ≤ w.1.val from by simp))
  have h2 := count_congr (fun w : Row (s := canonical) m =>
    (show (True ∧ ¬ 3 ≤ w.1.val) ↔ ¬ 3 ≤ w.1.val from by simp))
  have h3 : count (fun _ : Row (s := canonical) m => True) = 4 := by
    unfold count
    simp only [Finset.filter_true,Finset.card_univ]
    exact canonical_row_card m hm
  omega
end CMDRR.Source
