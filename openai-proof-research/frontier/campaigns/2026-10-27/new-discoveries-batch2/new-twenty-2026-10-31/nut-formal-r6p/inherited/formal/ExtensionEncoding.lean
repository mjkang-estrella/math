import RowEncoding
namespace Nut8
/-- Intended adjacency bits of an extension by the final labelled vertex. -/
def extensionBit (n a mask i j : ℕ) : Bool :=
  if i = n then (if j = n then false else mask.testBit j)
  else if j = n then mask.testBit i else graphBit n a i j

lemma grid_decode (n r c : ℕ) (hc : c < n) :
    (r*n+c)/n = r ∧ (r*n+c)%n = c := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.mul_comm r n, Nat.mul_add_div hn, Nat.div_eq_of_lt hc, Nat.add_zero]
  · simp [Nat.add_mod, Nat.mod_eq_of_lt hc]

lemma grid_testBit (n : ℕ) (b : ℕ → ℕ → Bool) (i j : ℕ)
    (hi : i < n) (hj : j < n) :
    (((List.range n).flatMap (fun r => (List.range n).map
      (fun c => if b r c then 2^(r*n+c) else 0))).sum).testBit (i*n+j) = b i j := by
  have he : ((List.range n).flatMap (fun r => (List.range n).map
      (fun c => if b r c then 2^(r*n+c) else 0))).sum =
    ((List.range n).flatMap (fun r => (List.range n).map
      (fun c => if b ((r*n+c)/n) ((r*n+c)%n) then 2^(r*n+c) else 0))).sum := by
    rw [row_list_sum, row_list_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro c hc
    rw [(grid_decode n r c (Finset.mem_range.mp hc)).1,
      (grid_decode n r c (Finset.mem_range.mp hc)).2]
  rw [he, row_encode_testBit n (fun k => b (k/n) (k%n)) i j hi hj,
    (grid_decode n i j hj).1, (grid_decode n i j hj).2]

/-- The inherited arithmetic extension has exactly its intended row-major bits. -/
theorem extendGraph_testBit (n a mask i j : ℕ) (hi : i < n+1) (hj : j < n+1) :
    graphBit (n+1) (extendGraph n a mask) i j = extensionBit n a mask i j := by
  have he : extendGraph n a mask =
    ((List.range (n+1)).flatMap (fun r => (List.range (n+1)).map
      (fun c => if extensionBit n a mask r c then 2^(r*(n+1)+c) else 0))).sum := by
    unfold extendGraph
    rw [row_list_sum, row_list_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro c hc
    unfold extensionBit
    split_ifs <;> simp_all
  unfold graphBit
  rw [he]
  exact grid_testBit _ _ _ _ hi hj
end Nut8
