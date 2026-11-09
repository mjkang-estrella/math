import R6_6_1MergeU4023S0
import R6_6_1MergeU4023S1
import R6_6_1MergeU4023S2
import R6_6_1MergeU4023S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB974 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+4023) = true := by
  intro u
  have he : u.val+4023 = 4023 := by omega
  rw [he]
  change (submasks 12 4023).all (fun a => if a = 0 ∨ a = 4023 then true else bitCheck 24 (table a) (table (4023 ^^^ a)) (table 4023)) = true
  apply all_split _ _ 256
  · exact slice4023_0
  ·
    apply all_split _ _ 256
    · exact slice4023_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice4023_2
      ·
        simp only [List.drop_drop]
        exact slice4023_3
end R6_6_1
