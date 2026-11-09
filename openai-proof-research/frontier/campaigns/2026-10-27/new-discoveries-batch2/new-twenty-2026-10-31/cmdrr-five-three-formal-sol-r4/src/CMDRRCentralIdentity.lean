import CMDRRFemalePairs
open scoped Classical BigOperators
namespace CMDRR.Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)

include h in
/-- Each spouse row has equally many actual game occurrences internal to the
two single women and internal to the married women, with one incidence per man. -/
theorem spouse_row_occurrence_balance (m : Fin 5) (hm : m.val < 3) :
    count (fun o => (∃ w, (d.game o).Partners m w) ∧ (d.game o).Women 3 4) =
    count (fun o => (∃ w, (d.game o).Partners m w) ∧
      ∀ t ∈ (d.game o).teams, t.2.val < 3) := by
  have hl := h.row_internal_occurrences m (fun w : Fin 5 => 3 ≤ w.val)
  have hr := h.row_internal_occurrences m (fun w : Fin 5 => ¬ 3 ≤ w.val)
  have hc := h.row_complementary_degree m hm
  have he := count_congr (fun o : O =>
    and_congr (Iff.rfl : (∃ w, (d.game o).Partners m w) ↔ _)
      (d.game o).all_singles)
  simp only [Nat.not_le] at hr hc
  exact (hl.trans he).symm.trans (hc.trans hr)

include h in
/-- Central double count on the original occurrence counts, without any
single-row cycle-type assumption. -/
theorem central_incidence_identity : A d + B d = 1 + z d := by
  classical
  have he :
      (∑ m : Fin 5, if m.val < 3 then
        count (fun o => (∃ w, (d.game o).Partners m w) ∧ (d.game o).Women 3 4) else 0) =
      ∑ m : Fin 5, if m.val < 3 then
        count (fun o => (∃ w, (d.game o).Partners m w) ∧
          ∀ t ∈ (d.game o).teams, t.2.val < 3) else 0 := by
    apply Finset.sum_congr rfl
    intro m _
    split_ifs with hm
    · exact h.spouse_row_occurrence_balance m hm
    · rfl
  have hs := spouse_incidence_fubini (d := d) (fun o => (d.game o).Women 3 4)
  have hh := spouse_incidence_fubini (d := d)
    (fun o => ∀ t ∈ (d.game o).teams, t.2.val < 3)
  have hsw := h.female_single_weighted
  have hhw := h.married_women_weighted
  rw [hs,hh] at he
  omega
end CMDRR.Source
