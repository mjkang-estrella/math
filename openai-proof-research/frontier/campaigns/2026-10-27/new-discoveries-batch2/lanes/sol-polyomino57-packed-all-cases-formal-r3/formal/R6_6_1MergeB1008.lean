import R6_6_1MergeU4063S0
import R6_6_1MergeU4063S1
import R6_6_1MergeU4063S2
import R6_6_1MergeU4063S3
import R6_6_1MergeU4063S4
import R6_6_1MergeU4063S5
import R6_6_1MergeU4063S6
import R6_6_1MergeU4063S7
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB1008 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+4063) = true := by
  intro u
  have he : u.val+4063 = 4063 := by omega
  rw [he]
  change (submasks 12 4063).all (fun a => if a = 0 ∨ a = 4063 then true else bitCheck 24 (table a) (table (4063 ^^^ a)) (table 4063)) = true
  apply all_split _ _ 256
  · exact slice4063_0
  ·
    apply all_split _ _ 256
    · exact slice4063_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice4063_2
      ·
        simp only [List.drop_drop]
        apply all_split _ _ 256
        · exact slice4063_3
        ·
          simp only [List.drop_drop]
          apply all_split _ _ 256
          · exact slice4063_4
          ·
            simp only [List.drop_drop]
            apply all_split _ _ 256
            · exact slice4063_5
            ·
              simp only [List.drop_drop]
              apply all_split _ _ 256
              · exact slice4063_6
              ·
                simp only [List.drop_drop]
                exact slice4063_7
end R6_6_1
