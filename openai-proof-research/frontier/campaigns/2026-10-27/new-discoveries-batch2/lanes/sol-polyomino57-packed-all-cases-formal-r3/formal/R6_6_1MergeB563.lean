import R6_6_1MergeU3007S0
import R6_6_1MergeU3007S1
import R6_6_1MergeU3007S2
import R6_6_1MergeU3007S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB563 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+3007) = true := by
  intro u
  have he : u.val+3007 = 3007 := by omega
  rw [he]
  change (submasks 12 3007).all (fun a => if a = 0 ∨ a = 3007 then true else bitCheck 24 (table a) (table (3007 ^^^ a)) (table 3007)) = true
  apply all_split _ _ 256
  · exact slice3007_0
  ·
    apply all_split _ _ 256
    · exact slice3007_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice3007_2
      ·
        simp only [List.drop_drop]
        exact slice3007_3
end R6_6_1
