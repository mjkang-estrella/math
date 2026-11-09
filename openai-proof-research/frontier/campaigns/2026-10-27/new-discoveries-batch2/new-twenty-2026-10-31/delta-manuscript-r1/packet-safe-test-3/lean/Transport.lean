import RawClosure
import Nodes
namespace Transport
open Literal
/-- A matrix represents a literal graph up to an arbitrary vertex equivalence. -/
def Represents (rows : Delta153.Graph) (g : Literal.Graph) : Prop :=
  ∃ vertex : Fin rows.length ≃ Fin g.order,
    ∀ i j, Delta153.edge rows i.val j.val = g.edge (vertex i) (vertex j)

/-- Literal moves commute with arbitrary relabelling of their source. -/
theorem relabel_move {g h r : Literal.Graph}
    (e : Fin r.order ≃ Fin g.order)
    (he : ∀ i j, r.edge i j = g.edge (e i) (e j))
    (move : YYDelta g h) : YYDelta r h := by
  obtain ⟨x,a,b,c,keep,hn,hi,hs,hab,hac,hbc,hax,hbx,hcx,hr,hm⟩ := move
  refine ⟨e.symm x,e.symm a,e.symm b,e.symm c,e.symm ∘ keep,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have := Fintype.card_congr e
    have ho : r.order = g.order := by simpa using this
    exact ho.trans hn
  · exact e.symm.injective.comp hi
  · intro v
    constructor
    · intro hv
      obtain ⟨i,hi⟩ := (hs (e v)).mp (fun hh => hv (by simpa using congrArg e.symm hh))
      exact ⟨i, by simp [hi]⟩
    · rintro ⟨i,hi⟩ h
      have hk : keep i = x := by simpa [Function.comp_def, h] using congrArg e hi
      exact ((hs x).mpr ⟨i,hk⟩) rfl
  · exact fun hh => hab (e.symm.injective hh)
  · exact fun hh => hac (e.symm.injective hh)
  · exact fun hh => hbc (e.symm.injective hh)
  · exact fun hh => hax (e.symm.injective hh)
  · exact fun hh => hbx (e.symm.injective hh)
  · exact fun hh => hcx (e.symm.injective hh)
  · intro v
    rw [he]
    simp only [Equiv.apply_symm_apply]
    rw [hr]
    congr 1
    simp only [← Equiv.eq_symm_apply]
  · intro i j
    rw [hm, he]
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    congr 1
    simp

/-- A one-step canonical simulation suffices for transport of all pure paths. -/
theorem pure_transport
    (step : ∀ {rows g h}, Represents rows g → YYDelta g h →
      ∃ x, x ∈ Delta153.verts rows ∧ Delta153.wye rows x = true ∧
        Represents (Delta153.reduce rows x) h)
    {rows g h} (rep : Represents rows g) (path : Literal.Pure g h) :
    ∃ target, RawClosure.Pure rows target ∧ Represents target h := by
  induction path generalizing rows with
  | refl => exact ⟨rows, RawClosure.Pure.refl rows, rep⟩
  | step move tail ih =>
    obtain ⟨x,hx,hw,rep'⟩ := step rep move
    obtain ⟨target,hp,ht⟩ := ih rep'
    exact ⟨target, RawClosure.Pure.step x hx hw hp, ht⟩

 theorem represented_order {rows g} (rep : Represents rows g) : rows.length = g.order := by
  simpa using Fintype.card_congr rep.choose

 theorem original_represents : Represents Delta153.original Concrete.g0 :=
  ⟨Equiv.refl _, by intro i j; rfl⟩
#print axioms relabel_move
#print axioms pure_transport
end Transport
