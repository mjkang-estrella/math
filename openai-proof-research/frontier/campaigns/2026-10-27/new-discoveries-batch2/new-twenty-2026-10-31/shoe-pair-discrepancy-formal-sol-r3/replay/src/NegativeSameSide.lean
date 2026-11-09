import ShoeSemanticControls
open Shoe
-- Intentional mutation: falsely treat the same-side repeat as a cross-side match.
example : HasMatch sameSideSample 3 := by
  refine ⟨0,0,by norm_num,by norm_num,?_⟩
  norm_num [sameSideSample]
