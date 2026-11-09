import R6_6_1MergeU3071S0
import R6_6_1MergeU3071S1
import R6_6_1MergeU3071S2
import R6_6_1MergeU3071S3
import R6_6_1MergeU3071S4
import R6_6_1MergeU3071S5
import R6_6_1MergeU3071S6
import R6_6_1MergeU3071S7
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB606 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+3071) = true := by
  intro u
  have he : u.val+3071 = 3071 := by omega
  rw [he]
  change (submasks 12 3071).all (fun a => if a = 0 ∨ a = 3071 then true else bitCheck 24 (table a) (table (3071 ^^^ a)) (table 3071)) = true
  apply all_split _ _ 256
  · exact slice3071_0
  ·
    apply all_split _ _ 256
    · exact slice3071_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice3071_2
      ·
        simp only [List.drop_drop]
        apply all_split _ _ 256
        · exact slice3071_3
        ·
          simp only [List.drop_drop]
          apply all_split _ _ 256
          · exact slice3071_4
          ·
            simp only [List.drop_drop]
            apply all_split _ _ 256
            · exact slice3071_5
            ·
              simp only [List.drop_drop]
              apply all_split _ _ 256
              · exact slice3071_6
              ·
                simp only [List.drop_drop]
                exact slice3071_7
end R6_6_1
