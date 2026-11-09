import CrownVConv1
import CrownVConv2
import CrownVFamCutB

/-!
The converse classification: every cut set of the crown graph (n ≥ 4) is the
cut of a valid family.  Case split on whether `T` meets the X side, the Y side,
or both; the witness constraints plus the no-common-neighbor lemma force the
five nonempty shapes, and `T = ∅` gives `zero`.  Combined with
`cutsetFam_of_valid` this yields the full `Cutset ↔ ∃ valid family` equivalence.
-/

namespace CrownV

variable {n : ℕ}

/-- Converse classification: a cut set is the cut of a valid family. -/
theorem validFam_of_cutset (hn : 4 ≤ n) {T : Finset (V n)} (hT : Cutset T) :
    ∃ f : Fam n, FamValid n f ∧ famCut n f = T := by
  classical
  by_cases h0 : T = ∅
  · exact ⟨.zero, trivial, by rw [famCut_zero]; exact h0.symm⟩
  have hwit : ∀ t : V n, t ∈ T → ∃ b c : V n, b ∈ (Finset.univ : Finset (V n)) \ T ∧
      c ∈ Finset.univ \ T ∧ cadj t b ∧ cadj t c ∧ ¬ SameC (Finset.univ \ T) b c :=
    fun t ht => cutWitness hT ht h0
  by_cases hXA : ∃ x : V n, x ∈ T ∧ sideX x
  · obtain ⟨x, hxT, hxs⟩ := hXA
    obtain ⟨i, hei⟩ := inl_of_sideX hxs
    subst hei
    obtain ⟨b, c, hbD, hcD, hxb, hxc, hdis⟩ := hwit (Sum.inl i) hxT
    obtain ⟨k, hek⟩ := inr_of_sideY (sideY_of_cadj_inl hxb)
    subst hek
    obtain ⟨m, hem⟩ := inr_of_sideY (sideY_of_cadj_inl hxc)
    subst hem
    have hkm : k ≠ m := by
      intro h; subst h
      exact hdis Relation.ReflTransGen.refl
    have hdX : ∀ l : Fin n, Sum.inl l ∈ Finset.univ \ T → l = k ∨ l = m :=
      fun l hl => notSameC_Xcommon hbD hcD hdis hl
    by_cases hYA : ∃ y : V n, y ∈ T ∧ sideY y
    · -- both sides meet T: the mixed shape
      obtain ⟨y, hyT, hys⟩ := hYA
      obtain ⟨j, hej⟩ := inr_of_sideY hys
      subst hej
      obtain ⟨a, a', haD, haD2, hya, hya2, hdis2⟩ := hwit (Sum.inr j) hyT
      obtain ⟨p, hep⟩ := inl_of_isX (sideX_of_cadj_inr hya)
      subst hep
      obtain ⟨q, heq⟩ := inl_of_isX (sideX_of_cadj_inr hya2)
      subst heq
      have hpq : p ≠ q := by
        intro h; subst h
        exact hdis2 Relation.ReflTransGen.refl
      have hdY : ∀ l : Fin n, Sum.inr l ∈ Finset.univ \ T → l = p ∨ l = q :=
        fun l hl => notSameC_Ycommon haD haD2 hdis2 hl
      have hpm := hdX p haD
      have hqm := hdX q haD2
      have hXkD : Sum.inl k ∈ Finset.univ \ T := by
        rcases hqm with e | e
        · rw [← e]; exact haD2
        · rcases hpm with f | f
          · rw [← f]; exact haD
          · exact absurd (f.trans e.symm) hpq
      have hXmD : Sum.inl m ∈ Finset.univ \ T := by
        rcases hpm with e | e
        · rcases hqm with f | f
          · exact absurd (f.trans e.symm) (Ne.symm hpq)
          · rw [← f]; exact haD2
        · rw [← e]; exact haD
      have hpqkm : ∀ l : Fin n, l = p ∨ l = q → l = k ∨ l = m := by
        intro l h
        rcases h with e | e
        · rcases hpm with f | f
          · exact Or.inl (e.trans f)
          · exact Or.inr (e.trans f)
        · rcases hqm with f | f
          · exact Or.inl (e.trans f)
          · exact Or.inr (e.trans f)
      have hXiff : ∀ l : Fin n, Sum.inl l ∈ Finset.univ \ T ↔ l = k ∨ l = m := by
        intro l; constructor
        · intro h; exact hdX l h
        · intro h; rcases h with e | e
          · rw [e]; exact hXkD
          · rw [e]; exact hXmD
      have hYiff : ∀ l : Fin n, Sum.inr l ∈ Finset.univ \ T ↔ l = k ∨ l = m := by
        intro l; constructor
        · intro h; exact hpqkm l (hdY l h)
        · intro h; rcases h with e | e
          · rw [e]; exact hbD
          · rw [e]; exact hcD
      exact famEq_mixed hkm hXiff hYiff
    · -- no Y in T: fullX or delX, or a refuted two-survivor shape
      have hnoY : ∀ y : V n, y ∈ T → ¬ sideY y := fun y hy hsy => hYA ⟨y, hy, hsy⟩
      have hballY : ∀ j : Fin n, Sum.inr j ∈ Finset.univ \ T :=
        fun j => mem_sdiff_univ_of_notMem (fun h => hnoY _ h isX_inr)
      have hYnone : ∀ l : Fin n, Sum.inr l ∉ T := fun l h => hnoY _ h isX_inr
      by_cases hkD : Sum.inl k ∈ Finset.univ \ T
      · by_cases hmD : Sum.inl m ∈ Finset.univ \ T
        · -- both X survivors present: the four-step path connects the witnesses
          exact absurd (sameC_refuteX hkm hkD hmD hballY hn) hdis
        · have hXiff : ∀ l : Fin n, Sum.inl l ∈ T ↔ l ≠ k := by
            intro l; constructor
            · intro hT' e
              have hTk : Sum.inl k ∈ T := by rw [← e]; exact hT'
              exact (Finset.mem_sdiff.1 hkD).2 hTk
            · intro hne
              by_contra hT'
              have hD : Sum.inl l ∈ Finset.univ \ T := mem_sdiff_univ_of_notMem hT'
              rcases hdX l hD with e | e
              · exact absurd e hne
              · rw [e] at hD; exact absurd hD hmD
          exact famEq_delX hXiff hYnone
      · by_cases hmD : Sum.inl m ∈ Finset.univ \ T
        · have hXiff : ∀ l : Fin n, Sum.inl l ∈ T ↔ l ≠ m := by
            intro l; constructor
            · intro hT' e
              have hTm : Sum.inl m ∈ T := by rw [← e]; exact hT'
              exact (Finset.mem_sdiff.1 hmD).2 hTm
            · intro hne
              by_contra hT'
              have hD : Sum.inl l ∈ Finset.univ \ T := mem_sdiff_univ_of_notMem hT'
              rcases hdX l hD with e | e
              · rw [e] at hD; exact absurd hD hkD
              · exact absurd e hne
          exact famEq_delX hXiff hYnone
        · have hXall : ∀ l : Fin n, Sum.inl l ∈ T := by
            intro l
            by_contra hT'
            have hD : Sum.inl l ∈ Finset.univ \ T := mem_sdiff_univ_of_notMem hT'
            rcases hdX l hD with e | e
            · rw [e] at hD; exact absurd hD hkD
            · rw [e] at hD; exact absurd hD hmD
          exact famEq_fullX hXall hYnone
  · -- no X in T: fullY or delY, or a refuted two-survivor shape
    have hnoX : ∀ x : V n, x ∈ T → ¬ sideX x := fun x hx hsx => hXA ⟨x, hx, hsx⟩
    have hballX : ∀ l : Fin n, Sum.inl l ∈ Finset.univ \ T :=
      fun l => mem_sdiff_univ_of_notMem (fun h => hnoX _ h isX_inl)
    have hXnone : ∀ l : Fin n, Sum.inl l ∉ T := fun l h => hnoX _ h isX_inl
    obtain ⟨y, hyT, hys⟩ : ∃ y : V n, y ∈ T ∧ sideY y := by
      obtain ⟨y, hyT⟩ := Finset.nonempty_iff_ne_empty.2 h0
      cases y with
      | inl kk => exact absurd ⟨Sum.inl kk, hyT, isX_inl⟩ hXA
      | inr kk => exact ⟨Sum.inr kk, hyT, isX_inr⟩
    obtain ⟨j, hej⟩ := inr_of_sideY hys
    subst hej
    obtain ⟨a, a', haD, haD2, hya, hya2, hdis2⟩ := hwit (Sum.inr j) hyT
    obtain ⟨p, hep⟩ := inl_of_isX (sideX_of_cadj_inr hya)
    subst hep
    obtain ⟨q, heq⟩ := inl_of_isX (sideX_of_cadj_inr hya2)
    subst heq
    have hpq : p ≠ q := by
      intro h; subst h
      exact hdis2 Relation.ReflTransGen.refl
    have hdY : ∀ l : Fin n, Sum.inr l ∈ Finset.univ \ T → l = p ∨ l = q :=
      fun l hl => notSameC_Ycommon haD haD2 hdis2 hl
    by_cases hpD : Sum.inr p ∈ Finset.univ \ T
    · by_cases hqD : Sum.inr q ∈ Finset.univ \ T
      · -- both Y survivors present: the four-step path connects the witnesses
        exact absurd (sameC_refuteY hpq hpD hqD hballX hn) hdis2
      · have hYiff : ∀ l : Fin n, Sum.inr l ∈ T ↔ l ≠ p := by
          intro l; constructor
          · intro hT' e
            have hTp : Sum.inr p ∈ T := by rw [← e]; exact hT'
            exact (Finset.mem_sdiff.1 hpD).2 hTp
          · intro hne
            by_contra hT'
            have hD : Sum.inr l ∈ Finset.univ \ T := mem_sdiff_univ_of_notMem hT'
            rcases hdY l hD with e | e
            · exact absurd e hne
            · rw [e] at hD; exact absurd hD hqD
        exact famEq_delY hYiff hXnone
    · by_cases hqD : Sum.inr q ∈ Finset.univ \ T
      · have hYiff : ∀ l : Fin n, Sum.inr l ∈ T ↔ l ≠ q := by
          intro l; constructor
          · intro hT' e
            have hTq : Sum.inr q ∈ T := by rw [← e]; exact hT'
            exact (Finset.mem_sdiff.1 hqD).2 hTq
          · intro hne
            by_contra hT'
            have hD : Sum.inr l ∈ Finset.univ \ T := mem_sdiff_univ_of_notMem hT'
            rcases hdY l hD with e | e
            · rw [e] at hD; exact absurd hD hpD
            · exact absurd e hne
        exact famEq_delY hYiff hXnone
      · have hYall : ∀ l : Fin n, Sum.inr l ∈ T := by
          intro l
          by_contra hT'
          have hD : Sum.inr l ∈ Finset.univ \ T := mem_sdiff_univ_of_notMem hT'
          rcases hdY l hD with e | e
          · rw [e] at hD; exact absurd hD hpD
          · rw [e] at hD; exact absurd hD hqD
        exact famEq_fullY hYall hXnone

/-- The full classification: cut sets are exactly the cuts of valid families. -/
theorem cutset_iff_fam (hn : 4 ≤ n) (T : Finset (V n)) :
    Cutset T ↔ ∃ f : Fam n, FamValid n f ∧ famCut n f = T :=
  ⟨fun h => validFam_of_cutset hn h, fun hf => by
    obtain ⟨f, hv, he⟩ := hf
    rw [← he]; exact cutsetFam_of_valid hn f hv⟩

end CrownV
