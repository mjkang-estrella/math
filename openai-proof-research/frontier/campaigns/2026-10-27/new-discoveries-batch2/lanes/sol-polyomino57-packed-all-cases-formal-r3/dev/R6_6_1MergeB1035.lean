import R6_6_1MergeU4091S0
import R6_6_1MergeU4091S1
import R6_6_1MergeU4091S2
import R6_6_1MergeU4091S3
import R6_6_1MergeU4091S4
import R6_6_1MergeU4091S5
import R6_6_1MergeU4091S6
import R6_6_1MergeU4091S7
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB1035 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+4091) = true := by
  intro u
  have he : u.val+4091 = 4091 := by omega
  rw [he]
  change (submasks 12 4091).all (fun a => if a = 0 ∨ a = 4091 then true else bitCheck 24 (table a) (table (4091 ^^^ a)) (table 4091)) = true
  apply all_split _ _ 256
  · exact slice4091_0
  ·
    apply all_split _ _ 256
    · exact slice4091_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice4091_2
      ·
        simp only [List.drop_drop]
        apply all_split _ _ 256
        · exact slice4091_3
        ·
          simp only [List.drop_drop]
          apply all_split _ _ 256
          · exact slice4091_4
          ·
            simp only [List.drop_drop]
            apply all_split _ _ 256
            · exact slice4091_5
            ·
              simp only [List.drop_drop]
              apply all_split _ _ 256
              · exact slice4091_6
              ·
                simp only [List.drop_drop]
                exact slice4091_7
end R6_6_1
