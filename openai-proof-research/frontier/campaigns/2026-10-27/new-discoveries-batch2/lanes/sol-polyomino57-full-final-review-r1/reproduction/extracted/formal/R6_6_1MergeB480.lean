import R6_6_1MergeU3967S0
import R6_6_1MergeU3967S1
import R6_6_1MergeU3967S2
import R6_6_1MergeU3967S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB480 : ∀ u : Fin 1, halfCheck 12 24 table (u.val+3967) = true := by
  intro u
  have he : u.val+3967 = 3967 := by omega
  rw [he]
  change (submasks 12 3967).all (fun a => if a = 0 ∨ a = 3967 ∨ 3967 ^^^ a < a then true else bitCheck 24 (table a) (table (3967 ^^^ a)) (table 3967)) = true
  apply all_split _ _ 512
  · exact slice3967_0
  ·
    apply all_split _ _ 512
    · exact slice3967_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 512
      · exact slice3967_2
      ·
        simp only [List.drop_drop]
        exact slice3967_3
end R6_6_1
