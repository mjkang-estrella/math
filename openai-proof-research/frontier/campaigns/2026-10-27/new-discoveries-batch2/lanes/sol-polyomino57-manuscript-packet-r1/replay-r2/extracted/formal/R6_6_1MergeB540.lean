import R6_6_1MergeU4087S0
import R6_6_1MergeU4087S1
import R6_6_1MergeU4087S2
import R6_6_1MergeU4087S3
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB540 : ∀ u : Fin 1, halfCheck 12 24 table (u.val+4087) = true := by
  intro u
  have he : u.val+4087 = 4087 := by omega
  rw [he]
  change (submasks 12 4087).all (fun a => if a = 0 ∨ a = 4087 ∨ 4087 ^^^ a < a then true else bitCheck 24 (table a) (table (4087 ^^^ a)) (table 4087)) = true
  apply all_split _ _ 512
  · exact slice4087_0
  ·
    apply all_split _ _ 512
    · exact slice4087_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 512
      · exact slice4087_2
      ·
        simp only [List.drop_drop]
        exact slice4087_3
end R6_6_1
