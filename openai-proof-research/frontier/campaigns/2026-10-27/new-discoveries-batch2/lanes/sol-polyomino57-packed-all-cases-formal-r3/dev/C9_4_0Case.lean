import C9_4_0Geometry
import C9_4_0Bounds
import C9_4_0Base
import C9_4_0Edge
import C9_4_0Merge
import C9_4_0Full
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C9_4_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem certificate : GraphPotential.Certificate (fun i j => Adj (point i) (point j))
    Finset.univ (Finset.range 11) (fun i j => point j ∈ group i) value := by
  apply bits_certificate 25 (fun v : Fin 25 => v.val) Finset.univ (Finset.range 11)
    (fun i j => Adj (point i) (point j)) (fun i j => point j ∈ group i) (rowOf 11 table)
  · intro v _; exact v.isLt
  · intro A _ _
    exact row_bounds (fun m hm => bounds_check ⟨m,hm⟩) A
  · intro A hA hn v _ hh
    have hb := base_check ⟨encode 11 A,encode_lt _ _⟩ (encode_nonzero hA hn) v
    rw [decode_encode _ _ hA] at hb
    exact hb hh
  · intro A hA hn v _ w _ he
    exact edge_check ⟨encode 11 A,encode_lt _ _⟩ (encode_nonzero hA hn) (v,w) (edge_mem v w he)
  · intro A B hA hB hnA hnB hd
    exact unionCheck_sound (fun u hu => merge_check ⟨u,hu⟩) A B hA hB hnA hnB hd
 theorem case_9_4_0 : ∀ Q : Finset GridPoint, Q ⊆ domain 9 4 0 → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups 9 4 0) :=
  excludes 9 4 0 point point_injective Finset.univ (Finset.range 11) group value
    domain_eq groups_mem certificate (by decide) (fun v _ => full_check v)
end C9_4_0
