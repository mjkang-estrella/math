import R6_6_1MergeU3455S0
import R6_6_1MergeU3455S1
import R6_6_1MergeU3455S2
import R6_6_1MergeU3455S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB698 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+3455) = true := by
  intro u
  have he : u.val+3455 = 3455 := by omega
  rw [he]
  change (submasks 12 3455).all (fun a => if a = 0 ∨ a = 3455 then true else bitCheck 24 (table a) (table (3455 ^^^ a)) (table 3455)) = true
  apply all_split _ _ 256
  · exact slice3455_0
  ·
    apply all_split _ _ 256
    · exact slice3455_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice3455_2
      ·
        simp only [List.drop_drop]
        exact slice3455_3
end R6_6_1
