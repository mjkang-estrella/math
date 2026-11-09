import R6_6_1MergeU4079S0
import R6_6_1MergeU4079S1
import R6_6_1MergeU4079S2
import R6_6_1MergeU4079S3
import R6_6_1MergeU4079S4
import R6_6_1MergeU4079S5
import R6_6_1MergeU4079S6
import R6_6_1MergeU4079S7
import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem merge_checkB1023 : ∀ u : Fin 1, unionCheck 12 24 table (u.val+4079) = true := by
  intro u
  have he : u.val+4079 = 4079 := by omega
  rw [he]
  change (submasks 12 4079).all (fun a => if a = 0 ∨ a = 4079 then true else bitCheck 24 (table a) (table (4079 ^^^ a)) (table 4079)) = true
  apply all_split _ _ 256
  · exact slice4079_0
  ·
    apply all_split _ _ 256
    · exact slice4079_1
    ·
      simp only [List.drop_drop]
      apply all_split _ _ 256
      · exact slice4079_2
      ·
        simp only [List.drop_drop]
        apply all_split _ _ 256
        · exact slice4079_3
        ·
          simp only [List.drop_drop]
          apply all_split _ _ 256
          · exact slice4079_4
          ·
            simp only [List.drop_drop]
            apply all_split _ _ 256
            · exact slice4079_5
            ·
              simp only [List.drop_drop]
              apply all_split _ _ 256
              · exact slice4079_6
              ·
                simp only [List.drop_drop]
                exact slice4079_7
end R6_6_1
