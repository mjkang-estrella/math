import UlasFinal4
open Ulas Ulas.Round4
example : sectionEven (w^0*(y*(1+y)*ev (1:Polynomial ℤ))) =
    y*(1+y)*ev (Round3.reduced 0 (1:Polynomial ℤ)+1) := by
  exact lemma_R_unconditional 0 1
