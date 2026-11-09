import CMDRRZeroA

namespace CMDRR.Source
variable {O : Type} [Fintype O]
variable {d : Schedule (Fin 5) (Fin 5) O} (h : Source canonical d)

include h in
/-- Partition of actual occurrences containing the two single women. -/
theorem female_single_occurrence_partition :
    A d + count (fun o => (d.game o).Women 3 4 ∧
      ¬ ∃ m n : Fin 5, m.val < 3 ∧ n.val < 3 ∧ (d.game o).Men m n) = 2 := by
  have hp := count_partition (fun o => (d.game o).Women 3 4)
    (fun o => ∃ m n : Fin 5, m.val < 3 ∧ n.val < 3 ∧ (d.game o).Men m n)
  have hr := h.canonical_women_repeat
  change A d + count (fun o => (d.game o).Women 3 4 ∧
      ¬ ∃ m n : Fin 5, m.val < 3 ∧ n.val < 3 ∧ (d.game o).Men m n) =
    count (fun o => (d.game o).Women 3 4) at hp
  omega
end CMDRR.Source
