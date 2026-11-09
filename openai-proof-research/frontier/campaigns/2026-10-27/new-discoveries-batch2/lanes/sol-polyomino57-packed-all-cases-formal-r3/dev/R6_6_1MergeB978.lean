import R6_6_1MergeU4027S0
import R6_6_1MergeU4027S1
import R6_6_1MergeU4027S2
import R6_6_1MergeU4027S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB978 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+4027) = true := by
  intro u
  have he : u.val+4027 = 4027 := by omega
  rw [he]
  change (submasks 12 4027).all (fun a => if a = 0 ∨ a = 4027 then true else bitCheck 24 (table a) (table (4027 ^^^ a)) (table 4027)) = true
  apply all_split _ _ 256
  · exact slice4027_0
  ·
    apply all_split _ _ 256
    · exact slice4027_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice4027_2
      ·
        simp only [List.drop_drop]
        exact slice4027_3
end R6_6_1
