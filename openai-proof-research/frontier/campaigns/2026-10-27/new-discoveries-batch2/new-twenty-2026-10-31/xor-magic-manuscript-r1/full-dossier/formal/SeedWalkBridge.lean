import WalkOrientationBridge
import RelabelMagic
namespace XorMagic
variable {m d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
/-- The indexed outgoing certificate binds the actual walk to the next slopes. -/
theorem ColouredCycleData.omegaWalk (C : ColouredCycleData G d)
    (p : G.Walk (C.cycle ⟨0,C.positive⟩) (C.cycle ⟨0,C.positive⟩))
    (hlen : p.length = C.length)
    (hind : ∀ i : Fin C.length, p.getVert i.val = C.cycle i) :
    OmegaWalk G (chosenSlopes G C.colouring) p := by
  apply omegaWalk_of_steps
  intro i hi
  have hil : i < C.length := by omega
  rw [hind ⟨i,hil⟩]
  by_cases hs : i+1 < C.length
  · rw [hind ⟨i+1,hs⟩]
    simpa only [Nat.mod_eq_of_lt hs] using C.outgoing ⟨i,hil⟩
  · have he : i+1 = C.length := by omega
    have hp : p.getVert (i+1) = C.cycle ⟨0,C.positive⟩ := by
      simpa only [he, hlen] using p.getVert_length
    rw [hp]
    simpa only [he,Nat.mod_self] using C.outgoing ⟨i,hil⟩

variable {V : Type} [Fintype V] [DecidableEq V] {K : SimpleGraph V}
    [DecidableRel K.Adj] {n : ℕ} {closed : Bool}
/-- Relabel a certified indexed walk as a seed on the next finite vertex type. -/
noncomputable def seedOfRelabelledWalk (C : ColouredCycleData K d)
    (regular : K.IsRegularOfDegree d)
    (magic : if closed then ClosedMagic K n else OpenMagic K n)
    (p : K.Walk (C.cycle ⟨0,C.positive⟩) (C.cycle ⟨0,C.positive⟩))
    (hcy : p.IsCycle) (hlen : p.length = C.length)
    (hind : ∀ i : Fin C.length, p.getVert i.val = C.cycle i)
    (hstart : C.colouring.colour (C.cycle ⟨0,C.positive⟩) = true)
    (e : K ≃g G) : ColouredSeed G n d closed := by
  let D := C.relabel e
  let q := p.map e.toHom
  have hi : ∀ i : Fin D.length, q.getVert i.val = D.cycle i := by
    intro i
    rw [SimpleGraph.Walk.getVert_map]
    exact congrArg e (hind i)
  have hl : q.length = D.length := (SimpleGraph.Walk.length_map _ _).trans hlen
  exact {
    seed := {
      regular := relabel_regular e regular
      magic := by cases closed <;> first | exact relabel_open e magic | exact relabel_closed e magic
      factorCycle := D.toFactorCycleData }
    strong := D.three_le
    colouring := D.colouring
    walk := q
    isCycle := (SimpleGraph.Walk.isCycle_map_iff_of_injective e.injective).mpr hcy
    length_eq := hl
    indexed := hi
    starts_true := by simpa [D, ColouredCycleData.relabel, FactorColouring.relabel] using hstart
    oriented := D.omegaWalk q hl hi }
end XorMagic
