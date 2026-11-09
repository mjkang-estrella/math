import Sigma.Attainment
namespace Sigma365710
open Finset
-- Concrete kernel reductions, not an exhaustive checker or unbounded proof.
example : sigmaT (completeBipartite 4 1) = 12 := by decide
example : sigmaT (completeBipartite 4 1) ≠ 24 := by decide
example : (∑ u : Fin 4, ∑ v : Fin 4,
    (((completeBipartite 4 1).degree u : ℤ) -
      ((completeBipartite 4 1).degree v : ℤ)) ^ 2) = 24 := by decide
example : F 3 2 = 2 := by decide
example : F 3 2 ≠ (2 : ℤ) * (3 - 2) * ((3 - 2 * 2 : ℕ) : ℤ)^2 := by decide
example : ¬ (completeBipartite 2 0).Adj 0 1 := by decide
end Sigma365710
