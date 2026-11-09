import Nut
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
namespace Nut8
variable {V : Type} [Fintype V]

noncomputable def orbitMap (σ : Equiv.Perm V) (m : ℕ) [NeZero m]
    (p : Quotient (orbitSetoid σ) × ZMod m) : V := (σ ^ p.2.val) p.1.out

lemma orbitMap_mem (σ : Equiv.Perm V) (m : ℕ) [NeZero m]
    (q : Quotient (orbitSetoid σ)) (b : ZMod m) :
    orbitMap σ m (q,b) ∈ orbitFinset σ q.out := by
  rw [mem_orbitFinset]
  exact ⟨(b.val : ℤ), by rw [zpow_natCast]; rfl⟩

lemma orbitMap_quotient (σ : Equiv.Perm V) (m : ℕ) [NeZero m]
    (q : Quotient (orbitSetoid σ)) (b : ZMod m) :
    Quotient.mk (orbitSetoid σ) (orbitMap σ m (q,b)) = q := by
  calc
    _ = Quotient.mk (orbitSetoid σ) q.out :=
      (Quotient.sound ((mem_orbitFinset _ _ _).mp (orbitMap_mem σ m q b))).symm
    _ = q := Quotient.out_eq q

noncomputable def globalLabelQ (σ : Equiv.Perm V) (m : ℕ) [NeZero m]
    (hm : ∀ v, (orbitFinset σ v).card = m) :
    Quotient (orbitSetoid σ) × ZMod m ≃ V := by
  classical
  apply Equiv.ofBijective (orbitMap σ m)
  constructor
  · rintro ⟨q,b⟩ ⟨q',b'⟩ h
    have hq : q = q' := by
      rw [← orbitMap_quotient σ m q b, ← orbitMap_quotient σ m q' b', h]
    subst q'
    have hmod := ((cycleOn_orbit σ q.out).pow_apply_eq_pow_apply
      ((mem_orbitFinset σ q.out q.out).2 (.refl σ q.out))).1 h
    rw [hm] at hmod
    have hv : b.val = b'.val := hmod.eq_of_lt_of_lt (ZMod.val_lt b) (ZMod.val_lt b')
    exact Prod.ext rfl (ZMod.val_injective m hv)
  · intro v
    let q : Quotient (orbitSetoid σ) := Quotient.mk _ v
    have hv : v ∈ orbitFinset σ q.out := by
      rw [mem_orbitFinset]
      exact Quotient.exact (Quotient.out_eq q)
    obtain ⟨a,ha⟩ := (labelOrbit σ q.out).surjective ⟨v,hv⟩
    refine ⟨(q, (a.val : ZMod m)), ?_⟩
    have hlt : a.val < m := by
      have h := a.isLt
      simpa only [hm] using h
    change (σ ^ (a.val : ZMod m).val) q.out = v
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    exact congrArg Subtype.val ha

lemma globalLabelQ_translate (σ : Equiv.Perm V) (m : ℕ) [NeZero m]
    (hm : ∀ v, (orbitFinset σ v).card = m)
    (q : Quotient (orbitSetoid σ)) (b : ZMod m) :
    globalLabelQ σ m hm (q,b+1) = σ (globalLabelQ σ m hm (q,b)) := by
  change (σ ^ (b+1).val) q.out = σ ((σ ^ b.val) q.out)
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  rw [← pow_eq_pow_mod (b.val+1) (pow_eq_one_of_equal_orbits σ m hm), pow_succ']
  rfl

/-- Coordinates have exactly eight orbits, with the cyclic generator acting by translation. -/
noncomputable def globalLabel8 (σ : Equiv.Perm V) (m : ℕ) [NeZero m]
    (hm : ∀ v, (orbitFinset σ v).card = m)
    (hc : Nat.card (Quotient (orbitSetoid σ)) = 8) : Fin 8 × ZMod m ≃ V := by
  classical
  letI := Fintype.ofFinite (Quotient (orbitSetoid σ))
  have hcard : Fintype.card (Quotient (orbitSetoid σ)) = 8 := by
    rwa [Nat.card_eq_fintype_card] at hc
  exact (Equiv.prodCongr (Fintype.equivFinOfCardEq hcard).symm (Equiv.refl _)).trans
    (globalLabelQ σ m hm)

lemma globalLabel8_translate (σ : Equiv.Perm V) (m : ℕ) [NeZero m]
    (hm : ∀ v, (orbitFinset σ v).card = m)
    (hc : Nat.card (Quotient (orbitSetoid σ)) = 8) (i : Fin 8) (b : ZMod m) :
    globalLabel8 σ m hm hc (i,b+1) = σ (globalLabel8 σ m hm hc (i,b)) := by
  classical
  exact globalLabelQ_translate σ m hm _ b
/-- The requested orientation of the global labelling and its action formula. -/
theorem global_coordinates8 (σ : Equiv.Perm V) (m : ℕ) [NeZero m]
    (hm : ∀ v, (orbitFinset σ v).card = m)
    (hc : Nat.card (Quotient (orbitSetoid σ)) = 8) :
    ∃ E : V ≃ Fin 8 × ZMod m,
      ∀ v, E (σ v) = ((E v).1, (E v).2 + 1) := by
  let L := globalLabel8 σ m hm hc
  refine ⟨L.symm, ?_⟩
  intro v
  apply L.injective
  rw [L.apply_symm_apply]
  have h := globalLabel8_translate σ m hm hc (L.symm v).1 (L.symm v).2
  simpa only [L, Prod.eta, Equiv.apply_symm_apply] using h.symm
/-- Part A1, instantiated directly from the inherited graph predicates. -/
theorem nut_circulant_global_coordinates [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Nut G) (hc : Circulant 8 G) :
    ∃ (σ : G ≃g G) (m : ℕ), 0 < m ∧
      ∃ E : V ≃ Fin 8 × ZMod m, ∀ v, E (σ v) = ((E v).1, (E v).2 + 1) := by
  have hV : 0 < Fintype.card V := lt_of_lt_of_le (by decide : 0 < 2) hn.1
  let : Nonempty V := Fintype.card_pos_iff.mp hV
  obtain ⟨σ, hq, m, hm⟩ := hc
  have hp := orbit_size_pos σ.toEquiv m hm
  let : NeZero m := ⟨Nat.ne_of_gt hp⟩
  exact ⟨σ, m, hp, global_coordinates8 σ.toEquiv m hm hq⟩
end Nut8
