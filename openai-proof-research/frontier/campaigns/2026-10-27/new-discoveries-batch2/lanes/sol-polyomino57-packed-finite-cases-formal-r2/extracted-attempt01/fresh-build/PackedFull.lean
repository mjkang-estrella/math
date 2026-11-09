import PackedFull0
import PackedFull1
import PackedFull2
import PackedFull3
import PackedFull4
import PackedFull5
import PackedFull6
import PackedFull7
set_option autoImplicit false
namespace PackedFull
open Polyomino57.Diagonal.FiniteProof.Packed
def pairs : List (ℕ × ℕ) := PackedFull0.pairs ++ PackedFull1.pairs ++ PackedFull2.pairs ++ PackedFull3.pairs ++ PackedFull4.pairs ++ PackedFull5.pairs ++ PackedFull6.pairs ++ PackedFull7.pairs
theorem coordinate_merge {a b : ℕ} (h : (a,b) ∈ pairs) : ∀ i < 24, digit 4247760990196309169816327290028259334472460 i + 1 ≤ digit a i + digit b i := by
  simp only [pairs, List.mem_append] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact checkedPairs_sound PackedFull0.fully_checked h
  · exact checkedPairs_sound PackedFull1.fully_checked h
  · exact checkedPairs_sound PackedFull2.fully_checked h
  · exact checkedPairs_sound PackedFull3.fully_checked h
  · exact checkedPairs_sound PackedFull4.fully_checked h
  · exact checkedPairs_sound PackedFull5.fully_checked h
  · exact checkedPairs_sound PackedFull6.fully_checked h
  · exact checkedPairs_sound PackedFull7.fully_checked h
end PackedFull
