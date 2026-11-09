import R6_6_1MergeU4092S0
import R6_6_1MergeU4092S1
import R6_6_1MergeU4092S2
import R6_6_1MergeU4092S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB1036 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+4092) = true := by
  intro u
  have he : u.val+4092 = 4092 := by omega
  rw [he]
  change (submasks 12 4092).all (fun a => if a = 0 ∨ a = 4092 then true else bitCheck 24 (table a) (table (4092 ^^^ a)) (table 4092)) = true
  apply all_split _ _ 256
  · exact slice4092_0
  ·
    apply all_split _ _ 256
    · exact slice4092_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice4092_2
      ·
        simp only [List.drop_drop]
        exact slice4092_3
end R6_6_1
