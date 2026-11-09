import PDTAR.Final
open PDTAR
example (hS : StarRigidityRemaining) (hT : ThreeThreeRigidityRemaining) :
    TARUnique (completeBipartiteGraph (Fin 2) (Fin 3)) := by
  rw [mathdb_353203_conditional hS hT 2 3 (by omega) (by omega)]
  norm_num
