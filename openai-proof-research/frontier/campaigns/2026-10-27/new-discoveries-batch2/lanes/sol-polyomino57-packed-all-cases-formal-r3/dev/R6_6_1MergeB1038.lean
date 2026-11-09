import R6_6_1MergeU4094S0
import R6_6_1MergeU4094S1
import R6_6_1MergeU4094S2
import R6_6_1MergeU4094S3
import R6_6_1MergeU4094S4
import R6_6_1MergeU4094S5
import R6_6_1MergeU4094S6
import R6_6_1MergeU4094S7
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB1038 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+4094) = true := by
  intro u
  have he : u.val+4094 = 4094 := by omega
  rw [he]
  change (submasks 12 4094).all (fun a => if a = 0 ∨ a = 4094 then true else bitCheck 24 (table a) (table (4094 ^^^ a)) (table 4094)) = true
  apply all_split _ _ 256
  · exact slice4094_0
  ·
    apply all_split _ _ 256
    · exact slice4094_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice4094_2
      ·
        simp only [List.drop_drop]
        apply all_split _ _ 256
        · exact slice4094_3
        ·
          simp only [List.drop_drop]
          apply all_split _ _ 256
          · exact slice4094_4
          ·
            simp only [List.drop_drop]
            apply all_split _ _ 256
            · exact slice4094_5
            ·
              simp only [List.drop_drop]
              apply all_split _ _ 256
              · exact slice4094_6
              ·
                simp only [List.drop_drop]
                exact slice4094_7
end R6_6_1
