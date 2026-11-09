import R6_6_1MergeU4061S0
import R6_6_1MergeU4061S1
import R6_6_1MergeU4061S2
import R6_6_1MergeU4061S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB1006 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+4061) = true := by
  intro u
  have he : u.val+4061 = 4061 := by omega
  rw [he]
  change (submasks 12 4061).all (fun a => if a = 0 ∨ a = 4061 then true else bitCheck 24 (table a) (table (4061 ^^^ a)) (table 4061)) = true
  apply all_split _ _ 256
  · exact slice4061_0
  ·
    apply all_split _ _ 256
    · exact slice4061_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice4061_2
      ·
        simp only [List.drop_drop]
        exact slice4061_3
end R6_6_1
