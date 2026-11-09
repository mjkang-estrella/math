module
public import GridFinal
@[expose] public section

namespace Grid343536
open SimpleGraph

theorem nofree_two : ¬ HasFreeVertex (G 2 2) := by
  rintro ⟨x, hx⟩
  have hd : transpose 2 2 ≠ 1 := by
    intro he
    have h := congrArg (fun g : G 2 2 ≃g G 2 2 => g (0, 1)) he
    change (1, 0) = (0, 1) at h
    exact (by decide : (1, 0) ≠ ((0, 1) : Fin 2 × Fin 2)) h
  have ha : rowFlip 2 2 * colFlip 2 2 * transpose 2 2 ≠ 1 := by
    intro he
    have h := congrArg (fun g : G 2 2 ≃g G 2 2 => g (0, 0)) he
    change (1, 1) = (0, 0) at h
    exact (by decide : (1, 1) ≠ ((0, 0) : Fin 2 × Fin 2)) h
  obtain ⟨i,j⟩ := x
  fin_cases i <;> fin_cases j
  · exact hd (hx _ rfl)
  · exact ha (hx _ rfl)
  · exact ha (hx _ rfl)
  · exact hd (hx _ rfl)

theorem nofree_three : ¬ HasFreeVertex (G 3 3) := by
  rintro ⟨x, hx⟩
  have hd : transpose 3 3 ≠ 1 := by
    intro he
    have h := congrArg (fun g : G 3 3 ≃g G 3 3 => g (0, 1)) he
    change (1, 0) = (0, 1) at h
    exact (by decide : (1, 0) ≠ ((0, 1) : Fin 3 × Fin 3)) h
  have ha : rowFlip 3 3 * colFlip 3 3 * transpose 3 3 ≠ 1 := by
    intro he
    have h := congrArg (fun g : G 3 3 ≃g G 3 3 => g (0, 0)) he
    change (2, 2) = (0, 0) at h
    exact (by decide : (2, 2) ≠ ((0, 0) : Fin 3 × Fin 3)) h
  have hr : rowFlip 3 3 ≠ 1 := by
    intro he
    have h := congrArg (fun g : G 3 3 ≃g G 3 3 => g (0, 0)) he
    change (2, 0) = (0, 0) at h
    exact (by decide : (2, 0) ≠ ((0, 0) : Fin 3 × Fin 3)) h
  have hc : colFlip 3 3 ≠ 1 := by
    intro he
    have h := congrArg (fun g : G 3 3 ≃g G 3 3 => g (0, 0)) he
    change (0, 2) = (0, 0) at h
    exact (by decide : (0, 2) ≠ ((0, 0) : Fin 3 × Fin 3)) h
  obtain ⟨i,j⟩ := x
  fin_cases i <;> fin_cases j
  · exact hd (hx _ rfl)
  · exact hc (hx _ rfl)
  · exact ha (hx _ rfl)
  · exact hr (hx _ rfl)
  · exact hd (hx _ rfl)
  · exact hr (hx _ rfl)
  · exact ha (hx _ rfl)
  · exact hc (hx _ rfl)
  · exact hd (hx _ rfl)

end Grid343536
