import LiftWalks
noncomputable section
namespace XorMagic.EdgeTransport
variable {V : Type} {G : SimpleGraph V} (T : EdgeTransport G)

def projection : T.graph →g G where
  toFun := Prod.fst
  map_rel' h := h.1

/-- Lift a walk with a specified initial fibre point. -/
def liftWalk {u v : V} (p : G.Walk u v) (x : Four) :
    T.graph.Walk (u,x) (v,T.along p x) := by
  induction p generalizing x with
  | nil => exact .nil
  | @cons u v w h p ih => exact .cons ⟨h,rfl⟩ (ih (T.map u v x))

theorem length_liftWalk {u v : V} (p : G.Walk u v) (x : Four) :
    (T.liftWalk p x).length = p.length := by
  induction p generalizing x with
  | nil => rfl
  | @cons u v w h p ih =>
    change (T.liftWalk p (T.map u v x)).length + 1 = p.length + 1
    exact congrArg (fun n => n+1) (ih _)

theorem map_liftWalk {u v : V} (p : G.Walk u v) (x : Four) :
    (T.liftWalk p x).map T.projection = p := by
  induction p generalizing x with
  | nil => rfl
  | @cons u v w h p ih =>
    change SimpleGraph.Walk.cons h ((T.liftWalk p (T.map u v x)).map T.projection) = SimpleGraph.Walk.cons h p
    exact congrArg (SimpleGraph.Walk.cons h) (ih _)

/-- The fixed point of loop transport gives a closed lifted walk. -/
def closedLift {v : V} (p : G.Walk v v) (x : Four) (hx : T.along p x = x) :
    T.graph.Walk (v,x) (v,x) :=
  (T.liftWalk p x).copy rfl (Prod.ext rfl hx)

theorem length_closedLift {v : V} (p : G.Walk v v) (x : Four) (hx : T.along p x = x) :
    (T.closedLift p x hx).length = p.length := by
  simp only [closedLift, SimpleGraph.Walk.length_copy, T.length_liftWalk]

theorem map_closedLift {v : V} (p : G.Walk v v) (x : Four) (hx : T.along p x = x) :
    (T.closedLift p x hx).map T.projection = p := by
  simp only [closedLift, SimpleGraph.Walk.map_copy, T.map_liftWalk]
  rfl

/-- A simple cycle lifts with exactly its original length at a fixed point. -/
theorem isCycle_closedLift {v : V} (p : G.Walk v v) (hp : p.IsCycle)
    (x : Four) (hx : T.along p x = x) : (T.closedLift p x hx).IsCycle := by
  apply SimpleGraph.Walk.IsCycle.of_map (f := T.projection)
  rw [T.map_closedLift]
  exact hp

/-- Cycle persistence once the cycle composite is proved to have nonidentity slope. -/
theorem cycle_of_affine_holonomy {v : V} (p : G.Walk v v) (hp : p.IsCycle)
    (s : Bool) (c : Four) (h : ∀ x, T.along p x = affine s c x) :
    ∃ x : Four, ∃ q : T.graph.Walk (v,x) (v,x), q.IsCycle ∧ q.length = p.length := by
  obtain ⟨x,hx,_⟩ := affine_unique_fixed s c
  have he : T.along p x = x := (h x).trans hx
  exact ⟨x,T.closedLift p x he,T.isCycle_closedLift p hp x he,T.length_closedLift p x he⟩
end XorMagic.EdgeTransport
