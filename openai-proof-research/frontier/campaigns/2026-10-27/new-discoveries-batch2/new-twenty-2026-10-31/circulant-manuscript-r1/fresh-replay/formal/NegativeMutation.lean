import Circulant
open Circulant350979
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
-- Mutating one residual mask invalidates the asserted complete classification.
example : ¬ (∀ s : Fin 128, TriangleFreeAtZero s → RadiusTwoAtZero s → s = 40 ∨ s = 70) := by
  decide
