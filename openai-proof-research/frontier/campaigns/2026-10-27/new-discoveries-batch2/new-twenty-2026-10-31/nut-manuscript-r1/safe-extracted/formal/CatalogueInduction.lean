import MaskEligibility
import CheckedGraphIso
namespace Nut8
attribute [local instance] Classical.propDecidable
def Covered (n : ℕ) (targets : List ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.Connected → (∀ i, G.degree i ≤ 3) →
    ∃ a ∈ targets, ∃ e : Equiv.Perm (Fin n),
      ∀ i j, G.Adj (e i) (e j) ↔ graphBit n a i.val j.val = true

theorem covered_one : Covered 1 [0] := by
  intro G _ _
  refine ⟨0, by simp, Equiv.refl _, ?_⟩
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simp [graphBit]

theorem covered_step (k : ℕ) (sources targets : List ℕ)
    (ih : Covered (k+1) sources)
    (hclose : ∀ a ∈ sources, ∃ cs, extensionClosed (k+1) a targets cs = true) :
    Covered (k+2) targets := by
  classical
  intro G hc hd
  obtain ⟨v, hv, hvd⟩ := connected_subcubic_deleteFin k G hc hd
  obtain ⟨a, ha, e, he⟩ := ih (deleteFin G v) hv hvd
  have he' : ∀ i j, G.Adj (v.succAbove (e i)) (v.succAbove (e j)) ↔
      graphBit (k+1) a i.val j.val = true := he
  obtain ⟨cs, hcs⟩ := hclose a ha
  obtain ⟨c, _, _, ht, hi⟩ := extensionClosed_sound (k+1) a targets cs hcs
    (transportedMask G v e) (List.mem_range.mpr (transportedMask_lt G v e))
    (transportedMask_eligible (by omega) G hc hd v e he')
  let p := checkedEquiv c.2.2 (graphIsoCheck_sound _ _ _ _ hi).1
  refine ⟨c.2.1, ht, p.trans (extendLabels v e), ?_⟩
  intro i j
  change G.Adj (extendLabels v e (p i)) (extendLabels v e (p j)) ↔ _
  rw [transported_extension_spec G v e a he']
  have hb := (graphIsoCheck_sound _ _ _ _ hi).2 i.val (List.mem_range.mpr i.isLt)
    j.val (List.mem_range.mpr j.isLt)
  rw [← checkedVertex_lookup c.2.2 (graphIsoCheck_sound _ _ _ _ hi).1 i,
    ← checkedVertex_lookup c.2.2 (graphIsoCheck_sound _ _ _ _ hi).1 j] at hb
  exact (congrArg (fun b => b = true) hb).symm.to_iff
end Nut8
