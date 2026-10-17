/- Copyright 2026 Myeongjin Kang. MIT. Deliberately false proof goal. -/
import Controls
open RCLike
open scoped BigOperators
example : (1 / 2 + (1 : ℝ) / 8) ≤ CM275.acceptance (2 / 100) (1 / 2) 1 := by
  norm_num [CM275.acceptance]
