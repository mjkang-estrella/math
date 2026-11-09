import LiftIncidence
open XorMagic
abbrev G : SimpleGraph (Fin 2) := ⊤
def edge : OrientedEdge G := ⟨(0,1),by decide⟩
example : incidenceB G (fun _ => 0) (incidenceD G (fun _ => 0)
    (fun w => if w = edge.val.2 then (1,0) else 0)) edge.val.1 = 0 := by decide
