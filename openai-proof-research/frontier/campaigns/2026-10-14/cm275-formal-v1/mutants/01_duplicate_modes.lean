/- Copyright 2026 Myeongjin Kang. MIT. Deliberately false proof goal. -/
import Controls
open RCLike
open scoped BigOperators
example :
    ⟪CM275.sample (fun _ : Fin 2 => (1 : AddChar (ZMod 1) ℂ)) (fun _ => 1),
      CM275.sample (fun _ : Fin 2 => (1 : AddChar (ZMod 1) ℂ)) (fun _ => 1)⟫ₙ_[ℂ] = 2 := by
  rw [CMControls.duplicate_energy]
  norm_num
