import LiftGraph
noncomputable section
namespace XorMagic

def scalar (s : Fin 3) (x : Four) : Four :=
  if s = 0 then x else if s = 1 then omegaMap x else omegaSq x

theorem scalar_add : ∀ s x y, scalar s (x+y) = scalar s x + scalar s y := by decide

def inverseScalar (s : Fin 3) : Fin 3 := if s = 0 then 0 else if s = 1 then 2 else 1

def affineThree (s : Fin 3) (c : Four) : Four ≃ Four where
  toFun x := scalar s x + c
  invFun y := scalar (inverseScalar s) (y+c)
  left_inv := by revert s c; decide
  right_inv := by revert s c; decide

variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
/-- One representative of each undirected edge, ordered by the vertex index. -/
abbrev OrientedEdge := {p : Fin m × Fin m // p.1 < p.2 ∧ G.Adj p.1 p.2}

def orientedMap (e : OrientedEdge G → Four ≃ Four) (u v : Fin m) : Four ≃ Four :=
  if h : u < v ∧ G.Adj u v then e ⟨(u,v),h⟩
  else if h : v < u ∧ G.Adj v u then (e ⟨(v,u),h⟩).symm
  else Equiv.refl Four

theorem orientedMap_reverse (e : OrientedEdge G → Four ≃ Four) {u v : Fin m}
    (h : G.Adj u v) (x : Four) :
    orientedMap G e v u (orientedMap G e u v x) = x := by
  have hn : u ≠ v := h.ne
  rcases lt_or_gt_of_ne hn with hl | hl
  · simp [orientedMap, hl, h, h.symm, not_lt.mpr (le_of_lt hl)]
  · simp [orientedMap, hl, h, h.symm, not_lt.mpr (le_of_lt hl)]

/-- The actual four-fold affine graph, with one scalar and constant per oriented edge. -/
def affineTransport (s : OrientedEdge G → Fin 3) (c : OrientedEdge G → Four) :
    EdgeTransport G where
  map := orientedMap G (fun e => affineThree (s e) (c e))
  reverse := orientedMap_reverse G _

theorem forward_affine (s : OrientedEdge G → Fin 3) (c : OrientedEdge G → Four)
    (e : OrientedEdge G) (x : Four) :
    (affineTransport G s c).map e.val.1 e.val.2 x = scalar (s e) x + c e := by
  simp [affineTransport, orientedMap, e.property, affineThree]
end XorMagic
