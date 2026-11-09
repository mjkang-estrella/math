import Antimagic6AWeights
namespace Antimagic.Round6A
open Round4A Round5A

theorem patchedIndex_row_involutive (h i : ℕ) :
    patchedIndex 2 h (patchedIndex 2 h i)=i := by
  by_cases hh : h=2
  · subst h; exact patchedIndex_involutive i
  · simp [patchedIndex,hh]

theorem patchedIndex_row_bound (h i : ℕ) (hi : i<2^h) :
    patchedIndex 2 h i<2^h := by
  by_cases hh : h=2
  · subst h
    norm_num only at hi ⊢
    unfold patchedIndex
    split_ifs <;> omega
  · simpa [patchedIndex,hh] using hi

theorem patchedIndex_row_injective (h : ℕ) :
    Function.Injective (patchedIndex 2 h) := by
  intro i j he
  have := congrArg (patchedIndex 2 h) he
  simpa only [patchedIndex_row_involutive] using this

/-- The patch permutes each row and hence preserves its exact set of labels. -/
theorem binary_internal_shell (n h i : ℕ) (hh : h≠1) :
    internalLabel 2 n h i=shellEntry (center 2 n) (offset 2 n h+patchedIndex 2 h i) :=
  internalLabel_shell 2 n h i hh

theorem binary_center (n : ℕ) (hn : 3 ≤ n) :
    internalEdges 2 n=2*center 2 n ∧ center 2 n+1=2^(n-1) := by
  have hg := internalEdges_geometric 2 n (by omega) (by omega)
  have hs := shell_size 2 n (by decide) hn
  have hl := internalEdges_lower 2 n hn
  have hp : 2^n=2*2^(n-1) := by
    rw [Nat.mul_comm,← pow_succ,Nat.sub_add_cancel (by omega : 1≤n)]
  omega

/-- Explicit row-two labels: these are the only four modified shell positions. -/
theorem binary_row_two (n : ℕ) (hn : 3 ≤ n) :
    internalLabel 2 n 2 0=2 ∧ internalLabel 2 n 2 1=2*center 2 n-1 ∧
    internalLabel 2 n 2 2=1 ∧ internalLabel 2 n 2 3=2*center 2 n-2 := by
  have hs := internalEdges_split 2 n (by omega)
  have ho := offset_step 2 n 1 (by omega)
  have hc := binary_center n hn
  have hl := internalEdges_lower 2 n hn
  norm_num only at hs ho hl
  have hO : offset 2 n 2+4=2*(center 2 n-1) := by omega
  have hz : 3 ≤ center 2 n := by omega
  have ho2 : offset 2 n 2=2*(center 2 n-3) := by omega
  simp [internalLabel,patchedIndex,ho2,Nat.add_mod,Nat.mul_mod_right]
  omega

#print axioms patchedIndex_row_involutive
#print axioms binary_center
#print axioms binary_row_two
end Antimagic.Round6A
