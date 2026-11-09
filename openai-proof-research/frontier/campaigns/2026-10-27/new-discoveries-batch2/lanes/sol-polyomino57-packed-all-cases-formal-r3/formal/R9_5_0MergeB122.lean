import R9_5_0MergeU1023S0
import R9_5_0MergeU1023S1
import R9_5_0MergeU1023S2
import R9_5_0MergeU1023S3
import R9_5_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB122 : ∀ u : Fin 1, unionCheck 10 30 table (u.val+1023) = true := by
  intro u
  have he : u.val+1023 = 1023 := by omega
  rw [he]
  change (submasks 10 1023).all (fun a => if a = 0 ∨ a = 1023 then true else bitCheck 30 (table a) (table (1023 ^^^ a)) (table 1023)) = true
  apply all_split _ _ 256
  · exact slice1023_0
  ·
    apply all_split _ _ 256
    · exact slice1023_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice1023_2
      ·
        simp only [List.drop_drop]
        exact slice1023_3
end R9_5_0
