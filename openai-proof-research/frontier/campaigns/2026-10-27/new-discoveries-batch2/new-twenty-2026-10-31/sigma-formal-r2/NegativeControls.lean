import Sigma.Endpoint
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
-- K(2,2) has a four-vertex path but its endpoints have a chord.
-- Thus a path alone cannot justify the induced-P4 deficit gap.
example : (completeBipartite 4 2).Adj 0 2 ∧
    (completeBipartite 4 2).Adj 2 1 ∧
    (completeBipartite 4 2).Adj 1 3 ∧
    (completeBipartite 4 2).Adj 0 3 := by decide
example : deficit (completeBipartite 4 2) = 0 := by decide
example : ¬ (2 : ℤ) ≤ deficit (completeBipartite 4 2) := by decide
-- Triangle-freeness is needed for deficit nonnegativity.
example : deficit (⊤ : SimpleGraph (Fin 3)) = -3 := by decide
-- A balanced complete bipartite graph need not maximize sigmaT.
example : sigmaT (completeBipartite 4 2) < sigmaT (completeBipartite 4 1) := by decide
end Sigma365710
