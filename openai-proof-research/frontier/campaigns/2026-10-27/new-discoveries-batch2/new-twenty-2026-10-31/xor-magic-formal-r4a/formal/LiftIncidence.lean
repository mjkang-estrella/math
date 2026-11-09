import LiftSections
namespace XorMagic
variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

/-- The constant-term incidence map for the same oriented affine edges as incidenceD. -/
def incidenceB (s : OrientedEdge G → Fin 3) :
    (OrientedEdge G → Four) →+ (Fin m → Four) where
  toFun c v := ∑ e : OrientedEdge G,
    if e.val.1 = v then c e else
    if e.val.2 = v then scalar (inverseScalar (s e)) (c e) else 0
  map_zero' := by
    funext v
    apply Finset.sum_eq_zero
    intro e _
    split_ifs <;> simp [scalar_zero]
  map_add' c c' := by
    funext v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp [scalar_add]
end XorMagic
namespace XorMagic
variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

theorem incidenceBD_entry (s : OrientedEdge G → Fin 3) (e : OrientedEdge G) (z : Four) :
    incidenceB G s (incidenceD G s (fun w => if w = e.val.2 then z else 0)) e.val.1 =
      z := by
  change (∑ f : OrientedEdge G,
    if f.val.1 = e.val.1 then
      (if f.val.2 = e.val.2 then z else 0) + scalar (s f) (if f.val.1 = e.val.2 then z else 0)
    else if f.val.2 = e.val.1 then scalar (inverseScalar (s f))
      ((if f.val.2 = e.val.2 then z else 0) + scalar (s f) (if f.val.1 = e.val.2 then z else 0))
    else 0) = _
  have huv : e.val.1 ≠ e.val.2 := ne_of_lt e.property.1
  rw [Finset.sum_eq_single e]
  · simp [huv, scalar_zero]
  · intro f _ hfe
    by_cases hfu : f.val.1 = e.val.1
    · have hfv : f.val.2 ≠ e.val.2 := by
        intro hh
        exact hfe (Subtype.ext (Prod.ext hfu hh))
      have hne : f.val.1 ≠ e.val.2 := by simpa only [hfu] using huv
      simp only [hfu, hfv, huv, ite_true, ite_false, scalar_zero, zero_add]
    · by_cases hfv : f.val.2 = e.val.1
      · have hne : f.val.1 ≠ e.val.2 := by
          intro hh
          have hlt := f.property.1
          rw [hh,hfv] at hlt
          exact (not_lt_of_gt e.property.1) hlt
        have htarget : f.val.2 ≠ e.val.2 := by simpa only [hfv] using huv
        simp only [hfu,hfv,hne,huv,ite_false,ite_true,scalar_zero,zero_add]
      · simp [hfu,hfv]
  · simp
end XorMagic

namespace XorMagic
variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
theorem incidenceBD_nonzero (s : OrientedEdge G → Fin 3) (e : OrientedEdge G) :
    ∃ b, incidenceB G s (incidenceD G s b) ≠ 0 := by
  refine ⟨(fun w => if w = e.val.2 then (1,0) else 0), ?_⟩
  intro h
  have he := congrFun h e.val.1
  rw [incidenceBD_entry] at he
  exact (by decide : ((1,0) : Four) ≠ 0) he
end XorMagic
