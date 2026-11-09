import Antimagic5ALeafParameters
namespace Antimagic.Round5A
open Finset Round4A

theorem internal_children_sum (s n h i : ℕ) (hs : 2 ≤ s)
    (hh : 1 ≤ h) (hn : h + 1 < n) (hi : i < (2*s)^h) :
    (∑ j ∈ range (2*s), internalLabel (2*s) n (h+1) ((2*s)*i+j)) =
      (2*s) * center (2*s) n := by
  have he : Even (2*s) := ⟨s,by omega⟩
  have ho := offset_even (2*s) n (h+1) he (by omega)
  obtain ⟨b,hb⟩ := ho
  have hp : (2*s)*i + 2*s ≤ (2*s)^(h+1) := by
    rw [pow_succ]
    nlinarith
  have hc := coordinate_bound (2*s) n (h+1) ((2*s)*i+2*s-1) (by omega) hn (by omega)
  have hz := shell_size (2*s) n he (by omega)
  have hed := internalEdges_split (2*s) n (by omega)
  have hZ : 1 ≤ center (2*s) n := by simp [center]
  rw [hb] at hc
  have hlin : 2*s*i = 2*(s*i) := by exact Nat.mul_assoc _ _ _
  rw [hlin] at hc
  have hrem : 2*s*i+2*s-1+1 = 2*s*i+2*s := by omega
  calc
    _ = ∑ j ∈ range (2*s), shellEntry (center (2*s) n) (2*(b+s*i)+j) := by
      apply sum_congr rfl
      intro j _
      rw [internalLabel_shell (2*s) n (h+1) _ (by omega), unpatched (2*s) (h+1) _ (by omega)]
      congr 1
      rw [hb]; simp only [Nat.mul_add, Nat.mul_assoc]; omega
    _ = _ := shellEntry_sum _ (b+s*i) s (by omega)

def leafConstant (s n : ℕ) : ℕ :=
  s * (2 * internalEdges (2*s) n + (2*s) * (2*s)^(n-1) + 1) + center (2*s) n

theorem leaf_formula (s n i j : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) (hj : j < 2*s) :
    largeLabel (2*s) n n ((2*s)*i+j) = internalEdges (2*s) n +
      leafEntry s ((2*s)^(n-1)/2) (parentParameter (2*s) n i) j := by
  have he : Even (2*s) := ⟨s,by omega⟩
  have hd : ((2*s)*i+j)/(2*s) = i := by rw [Nat.mul_add_div (by omega : 0 < 2*s), Nat.div_eq_of_lt hj]; omega
  have hm : ((2*s)*i+j)%(2*s) = j := by simp [Nat.add_mod, Nat.mod_eq_of_lt hj]
  have ha : (if center (2*s) n < internalLabel (2*s) n (n-1) (((2*s)*i+j)/(2*s))
      then internalLabel (2*s) n (n-1) (((2*s)*i+j)/(2*s)) - center (2*s) n
      else (2*s)^(n-1)+1+internalLabel (2*s) n (n-1) (((2*s)*i+j)/(2*s)) - center (2*s) n) =
      parentParameter (2*s) n i := by rw [hd]; rfl
  rw [largeLabel_leaf s n _ _ (by omega) hn ha (even_power (2*s) (n-1) he (by omega)),hm]

/-- Every actual last-row parent has the same incoming-plus-children sum. -/
theorem leaf_parent_sum (s n i : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n)
    (hi : i < (2*s)^(n-1)) :
    internalLabel (2*s) n (n-1) i +
      (∑ j ∈ range (2*s), largeLabel (2*s) n n ((2*s)*i+j)) = leafConstant s n := by
  have he : Even (2*s) := ⟨s,by omega⟩
  have ha := parentParameter_range (2*s) n i (by omega) he hn hi
  have hp := even_power (2*s) (n-1) he (by omega)
  have hsum := leafEntry_sum s ((2*s)^(n-1)/2) (parentParameter (2*s) n i) (by omega) (by omega)
  have hcancel := tupleParameter_cancel (center (2*s) n) ((2*s)^(n-1)/2) i
    (last_shell_bound (2*s) n he hn) (by omega)
  have hparam : tupleParameter (center (2*s) n) (2*((2*s)^(n-1)/2)) (shellEntry (center (2*s) n) i) =
      parentParameter (2*s) n i := by
    rw [← hp]; unfold parentParameter; rw [last_internal_shell (2*s) n i (by omega) hn]
  rw [hparam, ← last_internal_shell (2*s) n i (by omega) hn] at hcancel
  have htotal : (∑ j ∈ range (2*s), largeLabel (2*s) n n ((2*s)*i+j)) =
      (2*s) * internalEdges (2*s) n + ∑ j ∈ range (2*s), leafEntry s ((2*s)^(n-1)/2) (parentParameter (2*s) n i) j := by
    calc
      _ = ∑ j ∈ range (2*s), (internalEdges (2*s) n + leafEntry s ((2*s)^(n-1)/2) (parentParameter (2*s) n i) j) := by
        apply sum_congr rfl
        intro j hj
        exact leaf_formula s n i j hs hn (mem_range.mp hj)
      _ = _ := by rw [sum_add_distrib]; simp
  rw [← hp] at hsum
  rw [htotal]
  unfold leafConstant
  nlinarith

#print axioms internal_children_sum
#print axioms leaf_parent_sum
end Antimagic.Round5A
