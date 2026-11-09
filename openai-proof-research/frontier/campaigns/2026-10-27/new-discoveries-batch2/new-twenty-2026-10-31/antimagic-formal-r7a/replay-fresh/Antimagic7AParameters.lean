import Antimagic6ABinaryWeights
namespace Antimagic.Round7A
open Round4A Round5A Round6A

theorem last_internal_shell (n i : ℕ) (hn : 3  ≤  n) :
    internalLabel 2 n (n-1) i = shellEntry (center 2 n) (patchedIndex 2 (n-1) i) := by
  rw [binary_internal_shell n (n-1) i (by omega), offset_top 2 n (n-1) (by omega), Nat.zero_add]

theorem parentParameter_range (n i : ℕ) (hn : 3  ≤  n) (hi : i<2^(n-1)) :
    1  ≤  parentParameter 2 n i ∧ parentParameter 2 n i  ≤  2^(n-1) := by
  have hp := even_power 2 (n-1) (by decide) (by omega)
  unfold parentParameter
  rw [last_internal_shell n i hn]
  nth_rw 1 [hp]
  simpa only [← hp] using tupleParameter_range (center 2 n) (2^(n-1)/2) _
    (last_shell_bound 2 n (by decide) hn) (by have := patchedIndex_row_bound (n-1) i hi; omega)

theorem parentParameter_injective (n : ℕ) (hn : 3  ≤  n) :
    Function.Injective (fun i : Fin (2^(n-1)) => parentParameter 2 n i.val) := by
  intro i j eq
  have hp := even_power 2 (n-1) (by decide) (by omega)
  unfold parentParameter at eq
  dsimp only at eq
  rw [last_internal_shell n i.val hn,last_internal_shell n j.val hn] at eq
  conv at eq => lhs; arg 2; rw [hp]
  conv at eq => rhs; arg 2; rw [hp]
  have hij := tupleParameter_injective (center 2 n) (2^(n-1)/2)
    (last_shell_bound 2 n (by decide) hn)
    (a₁ := ⟨patchedIndex 2 (n-1) i.val,by have := patchedIndex_row_bound (n-1) i.val i.isLt; omega⟩)
    (a₂ := ⟨patchedIndex 2 (n-1) j.val,by have := patchedIndex_row_bound (n-1) j.val j.isLt; omega⟩) eq
  exact Fin.ext (patchedIndex_row_injective (n-1) (congrArg Fin.val hij))

def parentMap (n : ℕ) (hn : 3  ≤  n) (i : Fin (2^(n-1))) : Fin (2^(n-1)) :=
  ⟨parentParameter 2 n i.val-1,by have := parentParameter_range n i.val hn i.isLt; omega⟩

theorem parentMap_bijective (n : ℕ) (hn : 3  ≤  n) : Function.Bijective (parentMap n hn) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,rfl⟩
  intro i j eq
  apply parentParameter_injective n hn
  have h := congrArg Fin.val eq
  change parentParameter 2 n i.val-1=parentParameter 2 n j.val-1 at h
  have := parentParameter_range n i.val hn i.isLt
  have := parentParameter_range n j.val hn j.isLt
  dsimp only
  omega

theorem parent_cancel (n i : ℕ) (hn : 3  ≤  n) (hi : i<2^(n-1)) :
    internalLabel 2 n (n-1) i + parentParameter 2 n i =
      center 2 n + sigma (2^(n-1)/2) (parentParameter 2 n i) := by
  have hp := even_power 2 (n-1) (by decide) (by omega)
  have hc := tupleParameter_cancel (center 2 n) (2^(n-1)/2) (patchedIndex 2 (n-1) i)
    (last_shell_bound 2 n (by decide) hn) (by have := patchedIndex_row_bound (n-1) i hi; omega)
  rw [← hp, ← last_internal_shell n i hn] at hc
  exact hc

#print axioms parentMap_bijective
#print axioms parent_cancel
end Antimagic.Round7A
