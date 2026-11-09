import CrownVCut
import CrownVClass

/-!
Bridge between the path-form cut vertex `VCut` (CrownVClass) and the
component-count form, via the actual component counter `ccnt`
(CrownVCount): for `t ∉ s`, `VCut s t ↔ ccnt (insert t s) < ccnt s`.

Both directions are proved here as kernel theorems (`vcut_ccnt_left`,
`vcut_ccnt_right`, combined in `vcut_ccnt_iff`); neither is definitional.
The key steps: an `insert t s`-path between `s`-points that is not an
`s`-path must pass through `t` (`sameC_ins_split`); the `s`-components
surject onto the `insert t s`-components with the components of the two
`VCut`-witnesses merging, giving the strict count drop; conversely, if
every `insert t s`-path between `s`-points is already an `s`-path, the
`s`-components inject into the `insert t s`-components.
-/

open Classical

namespace CrownV

variable {n : ℕ}

/-! ### Component equality from a path -/

theorem comp_eq {s : Finset (V n)} {a b : V n} (h : SameC s a b) :
    comp s a = comp s b := by
  exact Finset.ext fun x =>
    ⟨fun hx => comp_eq_of_sameC h.symm hx, fun hx => comp_eq_of_sameC h hx⟩

/-- Last-edge decomposition of a path. -/
theorem sameC_last {s : Finset (V n)} {a : V n} :
    ∀ c : V n, SameC s a c → c = a ∨ ∃ w, SEdge s w c ∧ SameC s a w := by
  intro c h
  induction h with
  | refl => exact Or.inl rfl
  | tail h₁ h₂ _ => exact Or.inr ⟨_, h₂, h₁⟩

/-- The second endpoint of an `s`-path from `a ∈ s` lies in `s`. -/
theorem sameC_snd_mem {s : Finset (V n)} {a b : V n} (ha : a ∈ s)
    (h : SameC s a b) : b ∈ s := by
  rcases sameC_last b h with he | ⟨w, hw, _⟩
  · subst he; exact ha
  · exact hw.2.1

/-! ### Transfer: paths inside an `H`-closed block avoid the new vertex -/

/-- If `D ⊆ s` and `D` is closed under `H`-edges (`H = insert t s`), then
every `H`-path ending in `D` reroutes as an `s`-path. -/
theorem sameC_H_to_s {s : Finset (V n)} {t : V n} {D : Finset (V n)} {u : V n}
    (hDsub : ∀ z ∈ D, z ∈ s)
    (hcl : ∀ a ∈ D, ∀ ⦃b : V n⦄, SEdge (insert t s) a b → b ∈ D) :
    ∀ z : V n, SameC (insert t s) u z → z ∈ D → SameC s u z := by
  intro z h
  induction h with
  | refl => intro _; exact .refl
  | tail _ h₂ ih =>
    intro hzD
    have hmD := hcl _ hzD (sEdge_symm h₂)
    exact (ih hmD).trans
      (SameC.single ⟨hDsub _ hmD, hDsub _ hzD, h₂.2.2⟩)

/-- The `H`-component of `u` is `H`-closed. -/
theorem comp_H_closed {s : Finset (V n)} {t : V n} {u a b : V n}
    (ha : a ∈ comp (insert t s) u) (hb : b ∈ insert t s) (hcad : cadj a b) :
    b ∈ comp (insert t s) u := by
  have hau : SameC (insert t s) u a := (Finset.mem_filter.1 ha).2
  have h1 : SameC (insert t s) a b := SameC.single ⟨(Finset.mem_filter.1 ha).1, hb, hcad⟩
  exact Finset.mem_filter.2 ⟨hb, hau.trans h1⟩

/-! ### Split lemma: an `s`-escaping path inside `insert t s` touches `t` -/

theorem sameC_ins_split {s : Finset (V n)} {t x y : V n}
    (ht : t ∉ s) (hx : x ∈ s) (hconn : SameC (insert t s) x y)
    (hdis : ¬ SameC s x y) :
    SameC (insert t s) x t := by
  have key : ∀ z : V n, SameC (insert t s) x z → SameC s x z ∨ SameC (insert t s) x t := by
    intro z h
    induction h with
    | refl => exact Or.inl .refl
    | tail _ h₂ ih =>
      rcases ih with hS | hT
      · have hbS := sameC_snd_mem hx hS
        rcases Finset.mem_insert.1 h₂.2.1 with he | hcS
        · subst he
          exact Or.inr ((sameC_congr_set (Finset.subset_insert _ _) hS).trans'
            (SameC.single h₂))
        · exact Or.inl (hS.trans' (SameC.single ⟨hbS, hcS, h₂.2.2⟩))
      · exact Or.inr hT
  rcases key y hconn with hS | hT
  · exact absurd hS hdis
  · exact hT

/-! ### The component-count bridge -/

open Classical in
/-- A chosen element of a nonempty finset (classical choice).  The junk
value for the empty finset uses `NeZero n`, available in all intended uses
(`n ≥ 4` in the classification). -/
noncomputable def pickElem [NeZero n] (D : Finset (V n)) : V n :=
  if h : D.Nonempty then (show ∃ v, v ∈ D from h).choose
  else Sum.inl ⟨0, Nat.pos_of_ne_zero NeZero.out⟩

theorem pickElem_mem [NeZero n] {D : Finset (V n)} (hD : D.Nonempty) :
    pickElem D ∈ D := by
  simp only [pickElem]
  split
  · rename_i h
    exact Exists.choose_spec (show ∃ v, v ∈ D from h)
  · rename_i hne
    exact absurd hD hne

/-- Cut vertex raises the component count of the survivor set: the path-form
`VCut` implies `ccnt (insert t s) < ccnt s`. -/
theorem vcut_ccnt_left [NeZero n] {s : Finset (V n)} {t : V n} (ht : t ∉ s)
    (hvc : VCut s t) : ccnt (insert t s) < ccnt s := by
  classical
  obtain ⟨x, y, hx, hy, hconn, hdis⟩ := hvc
  have hsub : s ⊆ insert t s := Finset.subset_insert _ _
  have hBmem : comp s y ∈ comps s := comp_mem_comps hy
  have hAB : comp s x ≠ comp s y := notSameC_comp_ne hx hdis
  have hpyin : pickElem (comp s y) ∈ comp s y := pickElem_mem ⟨y, comp_self hy⟩
  have hpyS : SameC s y (pickElem (comp s y)) := (Finset.mem_filter.1 hpyin).2
  have hpyH : SameC (insert t s) y (pickElem (comp s y)) := sameC_congr_set hsub hpyS
  have e_y_pick : comp (insert t s) (pickElem (comp s y)) = comp (insert t s) y :=
    (comp_eq hpyH).symm
  have e_x_y : comp (insert t s) x = comp (insert t s) y := comp_eq hconn
  have e_x_t : comp (insert t s) x = comp (insert t s) t :=
    comp_eq (sameC_ins_split ht hx hconn hdis)
  have hBera : comp s y ∈ Finset.erase (comps s) (comp s x) :=
    Finset.mem_erase.2 ⟨Ne.symm hAB, hBmem⟩
  -- every `insert t s`-component arises from a member of the erased set
  have himg : comps (insert t s) ⊆
      (Finset.erase (comps s) (comp s x)).image
        fun D : Finset (V n) => comp (insert t s) (pickElem D) := by
    intro C hC
    obtain ⟨w, hwH, hCw⟩ := Finset.mem_image.1 hC
    rcases Finset.mem_insert.1 hwH with hwt | hwS
    · refine Finset.mem_image.2 ⟨comp s y, hBera, ?_⟩
      have e4 : comp (insert t s) t = C := by rw [← hCw, hwt]
      exact e_y_pick.trans (e_x_y.symm.trans (e_x_t.trans e4))
    · by_cases hwx : SameC s x w
      · have hwxH : SameC (insert t s) w x := sameC_congr_set hsub (SameC.symm hwx)
        have e3 : comp (insert t s) x = comp (insert t s) w := (comp_eq hwxH).symm
        exact Finset.mem_image.2 ⟨comp s y, hBera,
          e_y_pick.trans (e_x_y.symm.trans (e3.trans hCw))⟩
      · refine Finset.mem_image.2 ⟨comp s w, ?_, ?_⟩
        · have hne : comp s w ≠ comp s x := by
            intro hEq
            apply hwx
            have hxw : x ∈ comp s w := by
              rw [hEq]; exact comp_self hx
            exact SameC.symm (Finset.mem_filter.1 hxw).2
          exact Finset.mem_erase.2 ⟨hne, comp_mem_comps hwS⟩
        · have hpwin : pickElem (comp s w) ∈ comp s w :=
            pickElem_mem ⟨w, comp_self hwS⟩
          have hpw : SameC s w (pickElem (comp s w)) := (Finset.mem_filter.1 hpwin).2
          have hpwH : SameC (insert t s) w (pickElem (comp s w)) :=
            sameC_congr_set hsub hpw
          exact ((comp_eq hpwH).symm).trans hCw
  have hcard : (comps (insert t s)).card ≤
      (Finset.erase (comps s) (comp s x)).card := by
    refine (Finset.card_le_card himg).trans ?_
    exact Finset.card_image_le
  have hAmem : comp s x ∈ comps s := comp_mem_comps hx
  have herase : (Finset.erase (comps s) (comp s x)).card = (comps s).card - 1 :=
    Finset.card_erase_of_mem hAmem
  have hpos : (comps s).card ≠ 0 := by
    intro hcard0
    rw [Finset.card_eq_zero.1 hcard0] at hAmem
    exact Finset.notMem_empty _ hAmem
  have hfinal : (comps (insert t s)).card < (comps s).card := by
    have h1 := hcard; have h2 := herase; have h3 := hpos; omega
  exact hfinal

/-- If adding `t` strictly lowers the component count, `t` is a cut vertex in
the path form: otherwise `s`-components inject into `insert t s`-components. -/
theorem vcut_ccnt_right [NeZero n] {s : Finset (V n)} {t : V n}
    (h : ccnt (insert t s) < ccnt s) : VCut s t := by
  classical
  by_contra hvc
  -- every `insert t s`-connection between `s`-points is an `s`-connection
  have key : ∀ u v : V n, u ∈ s → v ∈ s →
      SameC (insert t s) u v → SameC s u v := by
    intro u v hu hv huv
    by_contra hns
    exact hvc ⟨u, v, hu, hv, huv, hns⟩
  -- the induced map on `s`-components is injective
  have hinj : ∀ D ∈ comps s, ∀ E : Finset (V n), E ∈ comps s →
      comp (insert t s) (pickElem D) = comp (insert t s) (pickElem E) → D = E := by
    intro D hD E hE hEq
    obtain ⟨a, haS, hDa⟩ := Finset.mem_image.1 hD
    obtain ⟨b, hbS, hEb⟩ := Finset.mem_image.1 hE
    have hDne : D.Nonempty := ⟨a, by rw [← hDa]; exact comp_self haS⟩
    have hEne : E.Nonempty := ⟨b, by rw [← hEb]; exact comp_self hbS⟩
    have hpD : pickElem D ∈ D := pickElem_mem hDne
    have hpE : pickElem E ∈ E := pickElem_mem hEne
    have hDsub : ∀ z ∈ D, z ∈ s := by
      intro z hz
      have hz' : z ∈ comp s a := by rw [← hDa] at hz; exact hz
      exact (Finset.mem_filter.1 hz').1
    have hEsub : ∀ z ∈ E, z ∈ s := by
      intro z hz
      have hz' : z ∈ comp s b := by rw [← hEb] at hz; exact hz
      exact (Finset.mem_filter.1 hz').1
    have hpDsub : pickElem D ∈ s := Finset.mem_of_subset hDsub hpD
    have hpEsub : pickElem E ∈ s := Finset.mem_of_subset hEsub hpE
    have hHpath : SameC (insert t s) (pickElem D) (pickElem E) := by
      have h1 : pickElem E ∈ comp (insert t s) (pickElem E) :=
        comp_self (Finset.mem_insert_of_mem hpEsub)
      rw [← hEq] at h1
      exact (Finset.mem_filter.1 h1).2
    have hSpath : SameC s (pickElem D) (pickElem E) :=
      key _ _ hpDsub hpEsub hHpath
    have hDaC : SameC s a (pickElem D) := by
      have hpD' : pickElem D ∈ comp s a := by rw [hDa]; exact hpD
      exact (Finset.mem_filter.1 hpD').2
    have hEbC : SameC s b (pickElem E) := by
      have hpE' : pickElem E ∈ comp s b := by rw [hEb]; exact hpE
      exact (Finset.mem_filter.1 hpE').2
    have hab : SameC s a b := hDaC.trans' (hSpath.trans' (SameC.symm hEbC))
    have hcompEq : comp s a = comp s b := comp_eq hab
    rw [← hDa, ← hEb, hcompEq]
  have hcardcomps : (comps s).card ≤ (comps (insert t s)).card := by
    have hsub1 : (comps s).image
        (fun D : Finset (V n) => comp (insert t s) (pickElem D)) ⊆
        comps (insert t s) := by
      intro C hC
      obtain ⟨D, hDmem, hCD⟩ := Finset.mem_image.1 hC
      obtain ⟨a, haS, hDa⟩ := Finset.mem_image.1 hDmem
      have hDne : D.Nonempty := ⟨a, by rw [← hDa]; exact comp_self haS⟩
      have hpD : pickElem D ∈ D := pickElem_mem hDne
      have hDsub : D ⊆ s := fun z hz => by
        have hz' : z ∈ comp s a := by rw [← hDa] at hz; exact hz
        exact (Finset.mem_filter.1 hz').1
      rw [← hCD]
      exact Finset.mem_image.2 ⟨pickElem D,
        Finset.mem_insert_of_mem (Finset.mem_of_subset hDsub hpD), rfl⟩
    have hinjOn : ∀ D ∈ comps s, ∀ E ∈ comps s,
        (fun D : Finset (V n) => comp (insert t s) (pickElem D)) D =
          (fun D : Finset (V n) => comp (insert t s) (pickElem D)) E → D = E :=
      fun D hD E hE hEq => hinj D hD E hE hEq
    calc (comps s).card
        = ((comps s).image fun D : Finset (V n) =>
            comp (insert t s) (pickElem D)).card :=
          (Finset.card_image_of_injOn hinjOn).symm
      _ ≤ (comps (insert t s)).card := Finset.card_le_card hsub1
  have h' : (comps (insert t s)).card < (comps s).card := h
  have hle := hcardcomps
  omega

/-- The full component-count bridge: for `t ∉ s`, `t` is a path-form cut
vertex of `s ∪ {t}` exactly when it strictly lowers the component count. -/
theorem vcut_ccnt_iff [NeZero n] {s : Finset (V n)} {t : V n} (ht : t ∉ s) :
    VCut s t ↔ ccnt (insert t s) < ccnt s :=
  ⟨vcut_ccnt_left ht, fun h => vcut_ccnt_right h⟩

end CrownV
