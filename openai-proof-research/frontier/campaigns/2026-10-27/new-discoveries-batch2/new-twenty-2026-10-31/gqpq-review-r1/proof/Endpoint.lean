import Cover
import Obstruction
namespace Cover377831

theorem no_partial_quotient : ¬ ContainsSGQPQ H Finset.univ := by
  classical
  rintro ⟨n, op, π, surj, row, col, domain, support⟩
  have hd (a b : Fin n) : ∃ z, op a b = some z := domain a b (Finset.mem_univ _)
  let total (a b : Fin n) := Classical.choose (hd a b)
  have hop (a b : Fin n) : op a b = some (total a b) := Classical.choose_spec (hd a b)
  apply no_total_quotient total π surj
  · intro a b c h
    exact row a b c (total a b) (hop a b) (by rw [h]; exact hop a c)
  · intro b a c h
    change total a b = total c b at h
    exact col a c b (total a b) (hop a b) (by rw [h]; exact hop c b)
  · intro a b
    exact support a b (total a b) (hop a b)

theorem source_refutation : ¬ SourceConjecture := by
  intro h
  apply no_partial_quotient
  apply h 3 H Finset.univ
  simpa [Restricted] using covering_number

end Cover377831
