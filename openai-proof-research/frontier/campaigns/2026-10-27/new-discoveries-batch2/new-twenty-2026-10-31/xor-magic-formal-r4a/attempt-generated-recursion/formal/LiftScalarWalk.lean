import LiftWalks
import LiftSections
namespace XorMagic

theorem scalar_comp : ∀ (a b : Fin 3) (x : Four),
    scalar (a+b) x = scalar a (scalar b x) := by decide

theorem scalar_one : ∀ x, scalar 1 x = omegaMap x := by decide

theorem scalar_two : ∀ x, scalar 2 x = omegaSq x := by decide

variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

def outgoingSlope (s : OrientedEdge G → Fin 3) (u v : Fin m) : Fin 3 :=
  if h : u < v ∧ G.Adj u v then s ⟨(u,v),h⟩
  else if h : v < u ∧ G.Adj v u then inverseScalar (s ⟨(v,u),h⟩)
  else 0

theorem outgoing_affine (s : OrientedEdge G → Fin 3) (c : OrientedEdge G → Four)
    (u v : Fin m) (x : Four) :
    (affineTransport G s c).map u v x = scalar (outgoingSlope G s u v) x +
      (affineTransport G s c).map u v 0 := by
  by_cases h : u < v ∧ G.Adj u v
  · simp [affineTransport, outgoingSlope, orientedMap, h, affineThree, scalar_zero]
  · by_cases h' : v < u ∧ G.Adj v u
    · simp [affineTransport, outgoingSlope, orientedMap, h, h', affineThree, scalar_add, scalar_zero]
    · simp [affineTransport, outgoingSlope, orientedMap, h, h', scalar]

/-- All directed edges of this walk have outgoing slope omega. This is a
local predicate; constructing an orientation satisfying it remains separate. -/
def OmegaWalk (s : OrientedEdge G → Fin 3) {u v : Fin m} : G.Walk u v → Prop
  | .nil => True
  | @SimpleGraph.Walk.cons _ _ u v w _ p => outgoingSlope G s u v = 1 ∧ OmegaWalk s p

theorem along_omega (s : OrientedEdge G → Fin 3) (c : OrientedEdge G → Four)
    {u v : Fin m} (p : G.Walk u v) (hp : OmegaWalk G s p) :
    ∃ b : Four, ∀ x, (affineTransport G s c).along p x = scalar (Fin.ofNat 3 p.length) x + b := by
  induction p with
  | nil => exact ⟨0,fun x => by simp [EdgeTransport.along, scalar]⟩
  | @cons u v w h p ih =>
    obtain ⟨b,hb⟩ := ih hp.2
    refine ⟨scalar (Fin.ofNat 3 p.length) ((affineTransport G s c).map u v 0) + b,fun x => ?_⟩
    change (affineTransport G s c).along p ((affineTransport G s c).map u v x) = _
    rw [hb, outgoing_affine, hp.1, scalar_add]
    have he : Fin.ofNat 3 (p.length+1) = Fin.ofNat 3 p.length + 1 := by
      apply Fin.ext
      simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
    rw [SimpleGraph.Walk.length_cons, he, scalar_comp]
    simp only [add_assoc]

/-- A consistently oriented cycle of length prime to 3 has the required
nonidentity affine holonomy, including the reversed scalar case. -/
theorem nontrivial_holonomy_of_omega_walk
    (s : OrientedEdge G → Fin 3) (c : OrientedEdge G → Four)
    {v : Fin m} (p : G.Walk v v) (hp : OmegaWalk G s p) (hn : p.length % 3 ≠ 0) :
    ∃ a b, ∀ x, (affineTransport G s c).along p x = affine a b x := by
  obtain ⟨b,hb⟩ := along_omega G s c p hp
  have he : (Fin.ofNat 3 p.length) ≠ 0 := by
    intro hh
    have hv := congrArg Fin.val hh
    exact hn hv
  have hc : (Fin.ofNat 3 p.length) = 1 ∨ (Fin.ofNat 3 p.length) = 2 := by
    have hv := (Fin.ofNat 3 p.length).isLt
    have hz : (Fin.ofNat 3 p.length).val ≠ 0 := fun h => he (Fin.ext h)
    rcases (by omega : (Fin.ofNat 3 p.length).val = 1 ∨ (Fin.ofNat 3 p.length).val = 2) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hc with h | h
  · exact ⟨true,b,fun x => by rw [hb,h,scalar_one]; rfl⟩
  · exact ⟨false,b,fun x => by rw [hb,h,scalar_two]; rfl⟩
end XorMagic
