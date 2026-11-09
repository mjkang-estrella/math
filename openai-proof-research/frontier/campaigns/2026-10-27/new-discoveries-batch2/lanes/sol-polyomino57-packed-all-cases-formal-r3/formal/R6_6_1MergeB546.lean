import R6_6_1MergeU4093S0
import R6_6_1MergeU4093S1
import R6_6_1MergeU4093S2
import R6_6_1MergeU4093S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB546 : ∀ u : Fin 1, halfCheck 12 24 table (u.val+4093) = true := by
  intro u
  have he : u.val+4093 = 4093 := by omega
  rw [he]
  change (submasks 12 4093).all (fun a => if a = 0 ∨ a = 4093 ∨ 4093 ^^^ a < a then true else bitCheck 24 (table a) (table (4093 ^^^ a)) (table 4093)) = true
  apply all_split _ _ 512
  · exact slice4093_0
  ·
    apply all_split _ _ 512
    · exact slice4093_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 512
      · exact slice4093_2
      ·
        simp only [List.drop_drop]
        exact slice4093_3
end R6_6_1
