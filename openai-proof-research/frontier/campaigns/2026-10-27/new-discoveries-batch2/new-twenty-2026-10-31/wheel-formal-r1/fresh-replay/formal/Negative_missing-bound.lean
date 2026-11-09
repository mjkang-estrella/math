import Foundation
open WheelFormal
example (G : SimpleGraph (Fin 1)) : 2 ≤ fracChromatic G := by
  apply weighted_lower_inf G (fun _ => 2) (by intro v; norm_num) 1 (by norm_num)
