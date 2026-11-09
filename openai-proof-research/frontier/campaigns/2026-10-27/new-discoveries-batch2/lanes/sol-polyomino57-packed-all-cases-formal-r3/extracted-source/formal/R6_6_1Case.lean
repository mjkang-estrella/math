import R6_6_1Geometry
import R6_6_1Bounds
import R6_6_1Base
import R6_6_1Edge
import R6_6_1Merge
import R6_6_1Full
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem certificate : GraphPotential.Certificate (fun i j => Adj (point i) (point j))
    Finset.univ (Finset.range 12) (fun i j => point j ∈ group i) value := by
  apply bits_certificate 24 (fun v : Fin 24 => v.val) Finset.univ (Finset.range 12)
    (fun i j => Adj (point i) (point j)) (fun i j => point j ∈ group i) (rowOf 12 table)
  · intro v _; exact v.isLt
  · intro A _ _
    exact row_bounds (fun m hm => bounds_check ⟨m,hm⟩) A
  · intro A hA hn v _ hh
    have hb := base_check ⟨encode 12 A,encode_lt _ _⟩ (encode_nonzero hA hn) v
    rw [decode_encode _ _ hA] at hb
    exact hb hh
  · intro A hA hn v _ w _ he
    exact edge_check ⟨encode 12 A,encode_lt _ _⟩ (encode_nonzero hA hn) (v,w) (edge_mem v w he)
  · intro A B hA hB hnA hnB hd
    exact halfCheck_sound (fun u hu => merge_check ⟨u,hu⟩) A B hA hB hnA hnB hd
 theorem case_6_6_1 : ∀ Q : Finset GridPoint, Q ⊆ domain 6 6 1 → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups 6 6 1) :=
  excludes 6 6 1 point point_injective Finset.univ (Finset.range 12) group value
    domain_eq groups_mem certificate (by decide) (fun v _ => full_check v)
end R6_6_1
