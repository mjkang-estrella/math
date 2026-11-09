import R6_6_1MergeU3838S0
import R6_6_1MergeU3838S1
import R6_6_1MergeU3838S2
import R6_6_1MergeU3838S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB870 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+3838) = true := by
  intro u
  have he : u.val+3838 = 3838 := by omega
  rw [he]
  change (submasks 12 3838).all (fun a => if a = 0 ∨ a = 3838 then true else bitCheck 24 (table a) (table (3838 ^^^ a)) (table 3838)) = true
  apply all_split _ _ 256
  · exact slice3838_0
  ·
    apply all_split _ _ 256
    · exact slice3838_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice3838_2
      ·
        simp only [List.drop_drop]
        exact slice3838_3
end R6_6_1
