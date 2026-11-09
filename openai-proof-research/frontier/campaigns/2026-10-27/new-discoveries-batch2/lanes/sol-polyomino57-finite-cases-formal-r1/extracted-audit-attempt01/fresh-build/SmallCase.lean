import SmallGeometry
import SmallBase
import SmallEdge
import SmallMerge
import SmallFull
set_option autoImplicit false
namespace Polyomino57.Diagonal.FiniteProof.Small
open Polyomino57

theorem certificate : GraphPotential.Certificate (fun i j => Adj (point i) (point j))
    Finset.univ Finset.univ (fun i j => point j ∈ group i) value :=
  checked_certificate _ _ _ _ _ base_check edge_check merge_check

theorem case_10_10_1 : ∀ Q : Finset GridPoint, Q ⊆ domain 10 10 1 → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups 10 10 1) :=
  excludes 10 10 1 point point_injective Finset.univ Finset.univ group value
    domain_eq groups_mem certificate (by decide) full_check
end Polyomino57.Diagonal.FiniteProof.Small
