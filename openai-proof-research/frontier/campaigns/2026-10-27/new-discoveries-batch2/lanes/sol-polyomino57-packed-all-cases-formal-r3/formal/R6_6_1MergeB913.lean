import R6_6_1MergeU3935S0
import R6_6_1MergeU3935S1
import R6_6_1MergeU3935S2
import R6_6_1MergeU3935S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB913 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+3935) = true := by
  intro u
  have he : u.val+3935 = 3935 := by omega
  rw [he]
  change (submasks 12 3935).all (fun a => if a = 0 ∨ a = 3935 then true else bitCheck 24 (table a) (table (3935 ^^^ a)) (table 3935)) = true
  apply all_split _ _ 256
  · exact slice3935_0
  ·
    apply all_split _ _ 256
    · exact slice3935_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice3935_2
      ·
        simp only [List.drop_drop]
        exact slice3935_3
end R6_6_1
