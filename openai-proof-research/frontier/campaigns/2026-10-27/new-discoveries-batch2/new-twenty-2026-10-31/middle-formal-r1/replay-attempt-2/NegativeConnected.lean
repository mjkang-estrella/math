import MiddleFinal
open R139.MiddleOCD
example : (G8.induce ({0, 2, 4, 5} : Set (Fin 8))).Preconnected := by
  intro a b
  exact (by decide : False).elim
