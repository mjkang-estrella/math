import R6_6_1MergeU3839S0
import R6_6_1MergeU3839S1
import R6_6_1MergeU3839S2
import R6_6_1MergeU3839S3
import R6_6_1MergeU3839S4
import R6_6_1MergeU3839S5
import R6_6_1MergeU3839S6
import R6_6_1MergeU3839S7
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB871 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+3839) = true := by
  intro u
  have he : u.val+3839 = 3839 := by omega
  rw [he]
  change (submasks 12 3839).all (fun a => if a = 0 ∨ a = 3839 then true else bitCheck 24 (table a) (table (3839 ^^^ a)) (table 3839)) = true
  apply all_split _ _ 256
  · exact slice3839_0
  ·
    apply all_split _ _ 256
    · exact slice3839_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice3839_2
      ·
        simp only [List.drop_drop]
        apply all_split _ _ 256
        · exact slice3839_3
        ·
          simp only [List.drop_drop]
          apply all_split _ _ 256
          · exact slice3839_4
          ·
            simp only [List.drop_drop]
            apply all_split _ _ 256
            · exact slice3839_5
            ·
              simp only [List.drop_drop]
              apply all_split _ _ 256
              · exact slice3839_6
              ·
                simp only [List.drop_drop]
                exact slice3839_7
end R6_6_1
