import IntegerCore
import Mathlib.Data.List.FinRange
namespace TripleCertificates
def domain : List (Fin 32 × Fin 32 × Fin 32) :=
 (List.finRange 32).flatMap fun i => (List.finRange 32).flatMap fun j =>
  ((List.finRange 32).filter fun k => i < j ∧ j < k).map fun k => (i,j,k)
end TripleCertificates
