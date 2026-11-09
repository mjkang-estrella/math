import R6_6_1MergeU2047S0
import R6_6_1MergeU2047S1
import R6_6_1MergeU2047S2
import R6_6_1MergeU2047S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB183 : ∀ u : Fin 1, halfCheck 12 24 table (u.val+2047) = true := by
  intro u
  have he : u.val+2047 = 2047 := by omega
  rw [he]
  change (submasks 12 2047).all (fun a => if a = 0 ∨ a = 2047 ∨ 2047 ^^^ a < a then true else bitCheck 24 (table a) (table (2047 ^^^ a)) (table 2047)) = true
  apply all_split _ _ 512
  · exact slice2047_0
  ·
    apply all_split _ _ 512
    · exact slice2047_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 512
      · exact slice2047_2
      ·
        simp only [List.drop_drop]
        exact slice2047_3
end R6_6_1
