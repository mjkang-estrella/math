import C8_4_1Geometry
import C8_4_1Bounds
import C8_4_1Base
import C8_4_1Edge
import C8_4_1Merge
import C8_4_1Full
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C8_4_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem certificate : GraphPotential.Certificate (fun i j => Adj (point i) (point j))
    Finset.univ (Finset.range 14) (fun i j => point j ∈ group i) value := by
  apply bits_certificate 22 (fun v : Fin 22 => v.val) Finset.univ (Finset.range 14)
    (fun i j => Adj (point i) (point j)) (fun i j => point j ∈ group i) (rowOf 14 table)
  · intro v _; exact v.isLt
  · intro A _ _
    exact row_bounds (fun m hm => bounds_check ⟨m,hm⟩) A
  · intro A hA hn v _ hh
    have hb := base_check ⟨encode 14 A,encode_lt _ _⟩ (encode_nonzero hA hn) v
    rw [decode_encode _ _ hA] at hb
    exact hb hh
  · intro A hA hn v _ w _ he
    exact edge_check ⟨encode 14 A,encode_lt _ _⟩ (encode_nonzero hA hn) (v,w) (edge_mem v w he)
  · intro A B hA hB hnA hnB hd
    exact unionCheck_sound (fun u hu => merge_check ⟨u,hu⟩) A B hA hB hnA hnB hd
 theorem case_8_4_1 : ∀ Q : Finset GridPoint, Q ⊆ domain 8 4 1 → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups 8 4 1) :=
  excludes 8 4 1 point point_injective Finset.univ (Finset.range 14) group value
    domain_eq groups_mem certificate (by decide) (fun v _ => full_check v)
end C8_4_1
