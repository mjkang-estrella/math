import PartitionConclusion
import PartitionPolynomial

namespace KeithMulticolor

/-- Full source-polynomial endpoint, with an actual fixed box, size, color
specialization and lattice line. No counting or coefficient hypotheses remain. -/
theorem source_full_counterexample_345259 :
    ¬ Unimodal (fun x : Fin 23 =>
      ((sourcePolynomial 25 325).coeff x.val).coeff (45 - 2 * x.val)) := by
  have heq : (fun x : Fin 23 =>
      ((sourcePolynomial 25 325).coeff x.val).coeff (45 - 2 * x.val)) =
        sourceCut := by
    funext x
    exact sourcePolynomial_coefficient _ _ _ _
  rw [heq]
  exact source_not_unimodal

theorem source_polynomial_strict_valley :
    ((sourcePolynomial 25 325).coeff 21).coeff 3 <
      ((sourcePolynomial 25 325).coeff 20).coeff 5 ∧
    ((sourcePolynomial 25 325).coeff 21).coeff 3 <
      ((sourcePolynomial 25 325).coeff 22).coeff 1 := by
  simp only [sourcePolynomial_coefficient]
  exact sourceCut_strict_valley

end KeithMulticolor
