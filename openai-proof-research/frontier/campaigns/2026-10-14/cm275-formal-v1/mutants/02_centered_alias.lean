/- Copyright 2026 Myeongjin Kang. MIT. Deliberately false proof goal. -/
import Controls
open RCLike
open scoped BigOperators
example : Function.Injective (fun i : Fin 3 => (i.val : ZMod 2) - 1) := by
  decide
