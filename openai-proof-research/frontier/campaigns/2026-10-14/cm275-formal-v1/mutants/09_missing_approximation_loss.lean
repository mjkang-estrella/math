/- Copyright 2026 Myeongjin Kang. MIT. Deliberately false proof goal. -/
import Controls
open RCLike
open scoped BigOperators
example : (1 / 2 + (1 : ℝ) / 10) ≤ 59 / 100 := by norm_num
