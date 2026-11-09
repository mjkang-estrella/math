import CMDRRNonexistence
namespace CMDRR.Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)

/-- The actual column map is identified by column_cell_correspondence. -/
theorem spouse_column_four (w : Fin 5) (hw : w.val < 3) :
    ∃ x c : Row (s := canonical) w,
      h.columnPerm w (h.columnPerm w (h.columnPerm w x)) = c ∧ h.columnPerm w c = x ∧
      x ≠ h.columnPerm w x ∧ x ≠ h.columnPerm w (h.columnPerm w x) ∧ x ≠ c ∧
      h.columnPerm w x ≠ h.columnPerm w (h.columnPerm w x) ∧ h.columnPerm w x ≠ c ∧
      h.columnPerm w (h.columnPerm w x) ≠ c ∧
      ∀ y, y = x ∨ y = h.columnPerm w x ∨
        y = h.columnPerm w (h.columnPerm w x) ∨ y = c :=
  h.canonical_swap_source.spouse_row_four w hw

theorem single_column_five (w : Fin 5) (hw : 3 ≤ w.val) (x : Row (s := canonical) w) :
    let p := h.columnPerm w
    p (p (p (p (p x)))) = x ∧
    x ≠ p x ∧ x ≠ p (p x) ∧ x ≠ p (p (p x)) ∧ x ≠ p (p (p (p x))) ∧
    p x ≠ p (p x) ∧ p x ≠ p (p (p x)) ∧ p x ≠ p (p (p (p x))) ∧
    p (p x) ≠ p (p (p x)) ∧ p (p x) ≠ p (p (p (p x))) ∧
    p (p (p x)) ≠ p (p (p (p x))) ∧
    ∀ y, y = x ∨ y = p x ∨ y = p (p x) ∨ y = p (p (p x)) ∨ y = p (p (p (p x))) :=
  h.canonical_swap_source.single_row_five w hw x
end CMDRR.Source
