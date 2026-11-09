import Endpoints

namespace MathDB356266

/-- CDG (1992), Section 4, page 50: the printed 24-symbol word. -/
def w_cdg : Fin 24 → Fin 6 :=
![1, 2, 3, 4, 1, 2, 5, 3, 4, 1, 5, 3, 2, 1, 4, 5, 3, 2, 4, 1, 3, 2, 5, 4]

/-- Reduced cyclic four-windows of the printed word, with ranks starting at 0. -/
def t_cdg : Fin 24 → Fin 4 → Fin 4 :=
![![0, 1, 2, 3], ![1, 2, 3, 0], ![2, 3, 0, 1], ![2, 0, 1, 3], ![0, 1, 3, 2], ![0, 3, 1, 2], ![3, 1, 2, 0], ![1, 2, 0, 3], ![2, 0, 3, 1], ![0, 3, 2, 1], ![3, 2, 1, 0], ![2, 1, 0, 3], ![1, 0, 2, 3], ![0, 2, 3, 1], ![2, 3, 1, 0], ![3, 1, 0, 2], ![2, 1, 3, 0], ![1, 3, 0, 2], ![3, 0, 2, 1], ![0, 2, 1, 3], ![1, 0, 3, 2], ![1, 3, 2, 0], ![3, 2, 0, 1], ![3, 0, 1, 2]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem cdg_euler : EulerOrdering t_cdg := by
  unfold EulerOrdering Permutation Overlaps Function.Injective
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem cdg_realizes : Realizes t_cdg w_cdg := by
  unfold Realizes
  decide

end MathDB356266
