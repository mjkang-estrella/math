import R6_6_1MergeU3999S0
import R6_6_1MergeU3999S1
import R6_6_1MergeU3999S2
import R6_6_1MergeU3999S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB956 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+3999) = true := by
  intro u
  have he : u.val+3999 = 3999 := by omega
  rw [he]
  change (submasks 12 3999).all (fun a => if a = 0 ∨ a = 3999 then true else bitCheck 24 (table a) (table (3999 ^^^ a)) (table 3999)) = true
  apply all_split _ _ 256
  · exact slice3999_0
  ·
    apply all_split _ _ 256
    · exact slice3999_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice3999_2
      ·
        simp only [List.drop_drop]
        exact slice3999_3
end R6_6_1
