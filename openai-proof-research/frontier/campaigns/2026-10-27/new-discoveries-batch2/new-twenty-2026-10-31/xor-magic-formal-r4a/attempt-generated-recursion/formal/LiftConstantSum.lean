import LiftIncidence
import LiftScalarWalk
namespace XorMagic
variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

theorem incidenceB_eq_neighbor_constants (s : OrientedEdge G → Fin 3)
    (c : OrientedEdge G → Four) (v : Fin m) :
    incidenceB G s c v = ∑ u ∈ G.neighborFinset v, (affineTransport G s c).map v u 0 := by
  classical
  let S : Finset (OrientedEdge G) := Finset.univ.filter (fun e => e.val.1 = v ∨ e.val.2 = v)
  let f : OrientedEdge G → Four := fun e =>
    if e.val.1 = v then c e else if e.val.2 = v then scalar (inverseScalar (s e)) (c e) else 0
  have hs : incidenceB G s c v = ∑ e ∈ S, f e := by
    change (∑ e, f e) = _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : e.val.1 = v ∨ e.val.2 = v
    · simp only [h, ite_true]
    · simp only [not_or] at h
      simp [h.1,h.2,f]
  rw [hs]
  apply Finset.sum_bij (fun e _ => if e.val.1 = v then e.val.2 else e.val.1)
  · intro e he
    have hi : e.val.1 = v ∨ e.val.2 = v := (Finset.mem_filter.mp he).2
    rw [SimpleGraph.mem_neighborFinset]
    rcases hi with h | h
    · simpa [h] using e.property.2
    · by_cases h' : e.val.1 = v
      · simpa [h'] using e.property.2
      · simpa [h',h] using e.property.2.symm
  · intro e he e' he' hh
    have hi := (Finset.mem_filter.mp he).2
    have hi' := (Finset.mem_filter.mp he').2
    apply Subtype.ext
    apply Prod.ext
    all_goals split_ifs at hh <;> rcases hi with h | h <;> rcases hi' with h' | h' <;>
      have hl := e.property.1 <;> have hl' := e'.property.1 <;> omega
  · intro u hu
    have ha : G.Adj v u := by simpa using hu
    rcases lt_or_gt_of_ne ha.ne with h | h
    · refine ⟨⟨(v,u),h,ha⟩, ?_, ?_⟩
      · simp [S]
      · simp
    · refine ⟨⟨(u,v),h,ha.symm⟩, ?_, ?_⟩
      · simp [S]
      · simp [ne_of_lt h]
  · intro e he
    have hi := (Finset.mem_filter.mp he).2
    have hlt := e.property.1
    have ha := e.property.2
    have hnot : ¬ e.val.2 < e.val.1 := not_lt_of_gt hlt
    rcases hi with h | h
    · subst v
      simp [f,affineTransport,orientedMap,affineThree,scalar_zero,hlt,ha]
    · have hne : e.val.1 ≠ v := by rw [← h]; exact ne_of_lt hlt
      subst v
      simp [f,affineTransport,orientedMap,affineThree,hlt,ha,hnot,ne_of_lt hlt]
end XorMagic
