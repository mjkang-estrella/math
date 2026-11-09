import Base
namespace Smyth1512
def row (b a i : ℕ) : List (List ℕ × List ℕ) :=
  (((comps 2 (b-i)).map (List.cons i)) ×ˢ comps 2 a).filter
    (fun p => inDB (sortL (p.1 ++ p.2)))
theorem comps_succ (m n : ℕ) : comps (m+1) n =
    (List.range (n+1)).flatMap (fun i => (comps m (n-i)).map (List.cons i)) := rfl
theorem count_rows (b a : ℕ) :
    (((comps 3 b) ×ˢ (comps 2 a)).filter (fun p => inDB (sortL (p.1 ++ p.2)))).length =
      ((List.range (b+1)).map (fun i => (row b a i).length)).sum := by
  rw [show 3 = 2+1 from rfl, comps_succ]
  simp only [row, SProd.sprod, List.product, List.flatMap_assoc, List.filter_flatMap, List.length_flatMap]
end Smyth1512
