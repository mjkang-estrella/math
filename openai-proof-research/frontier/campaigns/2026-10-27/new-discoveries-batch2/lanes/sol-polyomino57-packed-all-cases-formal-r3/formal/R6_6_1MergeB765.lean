import R6_6_1MergeU3582S0
import R6_6_1MergeU3582S1
import R6_6_1MergeU3582S2
import R6_6_1MergeU3582S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB765 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+3582) = true := by
  intro u
  have he : u.val+3582 = 3582 := by omega
  rw [he]
  change (submasks 12 3582).all (fun a => if a = 0 ∨ a = 3582 then true else bitCheck 24 (table a) (table (3582 ^^^ a)) (table 3582)) = true
  apply all_split _ _ 256
  · exact slice3582_0
  ·
    apply all_split _ _ 256
    · exact slice3582_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice3582_2
      ·
        simp only [List.drop_drop]
        exact slice3582_3
end R6_6_1
