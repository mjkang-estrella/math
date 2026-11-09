import Sem5Flux
open scoped BigOperators
namespace ChanLevine.Sem5
variable {n : ℕ} [NeZero n]

/-- Conservation across a finite cut with all residual sources on the cut. -/
theorem flux_cut (S : Finset (ZMod n)) (x r : ZMod n → ℤ)
    (F : ZMod n → ZMod n → ℤ) (hx : ∀ k, 0 ≤ x k)
    (hF : ∀ v k, 0 ≤ F v k) (hr : ∀ v, ∑ k, F v k = r v)
    (hout : ∀ k, k ∉ S → r k = 0)
    (hin : ∀ k ∈ S, 0 = x k + r k - ∑ v, F v k) :
    (∀ k ∈ S, x k = 0) ∧ (∀ v k, k ∉ S → F v k = 0) := by
  classical
  have hbal := Finset.sum_congr rfl hin
  simp only [Finset.sum_const_zero, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hbal
  have hrt : ∑ k ∈ S, r k = ∑ k, r k := by
    exact Finset.sum_subset (Finset.subset_univ _) (by intro k _ hk; exact hout k hk)
  rw [hrt] at hbal
  have htot : (∑ k ∈ S, ∑ v, F v k) + (∑ k ∈ Sᶜ, ∑ v, F v k) = ∑ k, r k := by
    rw [Finset.sum_add_sum_compl, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun v _ => hr v)
  have hxn : 0 ≤ ∑ k ∈ S, x k := Finset.sum_nonneg (fun k _ => hx k)
  have hfn : 0 ≤ ∑ k ∈ Sᶜ, ∑ v, F v k :=
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun v _ => hF v k))
  have hxz : ∑ k ∈ S, x k = 0 := by omega
  have hfz : ∑ k ∈ Sᶜ, ∑ v, F v k = 0 := by omega
  refine ⟨?_, ?_⟩
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hx k)).mp hxz
  · intro v k hk
    have hz : ∑ v, F v k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
        Finset.sum_nonneg (fun v _ => hF v k))).mp hfz k (by simpa using hk)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hF v k)).mp hz v (Finset.mem_univ v)

/-- The missing departures force a chip-free closed initial-rotor set. -/
theorem cappedDeficitTrap : Sem4.CappedDeficitTrap := by
  intro n inst hn c w d ht hex
  classical
  let S : Finset (ZMod n) := Finset.univ.filter (fun v => w.count v < 2)
  have hS : ∀ v, v ∈ S ↔ w.count v < 2 := by intro v; simp [S]
  let r : ZMod n → ℤ := fun v => 2 - (w.count v : ℤ)
  let F : ZMod n → ZMod n → ℤ := fun v k => residual c.lift (w.count v) v k
  have hb : ∀ v, w.count v ≤ 2 := ht.2.1
  have hcut := flux_cut S (fun k => (c.x k : ℤ)) r F
    (fun k => Int.natCast_nonneg _) (fun v k => residual_nonneg _ _ _ _)
    (fun v => residual_sum _ _ (hb v) v)
    (by intro k hk; dsimp [r]; have := hb k; have := (hS k).not.mp hk; omega)
    (by
      intro k hk
      have he := Sem4.capped_terminal_empty ht ((hS k).mp hk)
      have hf := residual_flux ht.1 hb k
      change d.x k = (c.x k : ℤ) + r k - ∑ v, F v k at hf
      omega)
  refine ⟨(S : Set (ZMod n)), ?_, ?_, ?_⟩
  · obtain ⟨v,hv⟩ := hex
    exact ⟨v, (hS v).mpr hv⟩
  · intro v hv
    have := hcut.1 v hv
    exact_mod_cast this
  · intro v hv
    by_contra hh
    have hz := hcut.2 v (Sem4.rotorNext c v) hh
    have hcount := (hS v).mp hv
    have hc : w.count v = 0 ∨ w.count v = 1 := by omega
    rcases hc with hc | hc <;> cases hq : c.q v <;>
      simp [F, residual, hc, Sem4.rotorNext, Config.lift, hq] at hz <;>
      split_ifs at hz <;> omega
end ChanLevine.Sem5
