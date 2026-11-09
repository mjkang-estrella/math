import R6_6_1MergeU4075S0
import R6_6_1MergeU4075S1
import R6_6_1MergeU4075S2
import R6_6_1MergeU4075S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB1019 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+4075) = true := by
  intro u
  have he : u.val+4075 = 4075 := by omega
  rw [he]
  change (submasks 12 4075).all (fun a => if a = 0 ∨ a = 4075 then true else bitCheck 24 (table a) (table (4075 ^^^ a)) (table 4075)) = true
  apply all_split _ _ 256
  · exact slice4075_0
  ·
    apply all_split _ _ 256
    · exact slice4075_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice4075_2
      ·
        simp only [List.drop_drop]
        exact slice4075_3
end R6_6_1
