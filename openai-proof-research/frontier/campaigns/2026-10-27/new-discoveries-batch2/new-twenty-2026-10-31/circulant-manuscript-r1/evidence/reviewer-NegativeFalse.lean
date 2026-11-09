import Circulant
open Circulant350979
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
-- This deliberately false mutation must be rejected by the kernel.
example : ∀ s : Fin 128, TriangleFreeAtZero s → RadiusTwoAtZero s → s = 40 ∨ s = 70 := by
  decide
