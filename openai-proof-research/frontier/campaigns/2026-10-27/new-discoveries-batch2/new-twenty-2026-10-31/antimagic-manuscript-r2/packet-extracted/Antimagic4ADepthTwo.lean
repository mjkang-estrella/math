import Antimagic4ABijection
namespace Antimagic.Round4A
open Round3 Finset

theorem bottom_weight (s : ℕ) (hs : 2 ≤ s) (v : Vertex (2 * s) 2) (hv : depth v = 2) :
    weight (tree (2 * s) 2) (depthTwoLabeling s hs) v = label (2 * s) 2 v.1.val v.2.val := by
  rw [weight_bottom (by omega) (by omega) _ v hv, depthTwoLabeling_label]

theorem root_weight (s : ℕ) (hs : 2 ≤ s) :
    weight (tree (2 * s) 2) (depthTwoLabeling s hs) (root (2 * s) 2) = (2 * s)^2 + 2 * s :=
  literal_depthTwo_root s hs _ (depthTwoLabeling_label s hs)

theorem row_one_weight (s : ℕ) (hs : 2 ≤ s) (v : Vertex (2 * s) 2) (hv : v.1.val = 1) :
    weight (tree (2 * s) 2) (depthTwoLabeling s hs) v =
      if v.2.val = 0 then (2 * s)^2 + 2 else depthTwoConstant s :=
  literal_depthTwo_row_one s hs _ (depthTwoLabeling_label s hs) v hv

theorem label_max_identity (s : ℕ) (hs : 2 ≤ s) :
    4 * s + (2 * s) * (2 * s - 1) = (2 * s)^2 + 2 * s := by
  have : 2 * s - 1 + 1 = 2 * s := by omega
  nlinarith

theorem depthTwo_local (s : ℕ) (hs : 2 ≤ s) :
    IsLocal (tree (2 * s) 2) (depthTwoLabeling s hs) := by
  have hdir (u v : Vertex (2 * s) 2) (h : Child u v) :
      weight (tree (2 * s) 2) (depthTwoLabeling s hs) u ≠
      weight (tree (2 * s) 2) (depthTwoLabeling s hs) v := by
    have hu := u.1.isLt
    have hv := v.1.isLt
    have hh := h.1
    by_cases hz : u.1.val = 0
    · rw [unique_depth_zero u hz, root_weight, row_one_weight s hs v (by omega)]
      have := depthTwoConstant_large s hs
      have := depthTwo_root_special_ne s hs
      split_ifs <;> omega
    · have hu1 : u.1.val = 1 := by omega
      have hv2 : depth v = 2 := by change v.1.val = 2; omega
      rw [row_one_weight s hs u hu1, bottom_weight s hs v hv2]
      by_cases hi : u.2.val = 0
      · simp only [hi, ite_true]
        have hd := h.2
        rw [hi] at hd
        have ht : 0 < 2 * s := by omega
        have hsmall : v.2.val < 2 * s := by have := Nat.div_eq_zero_iff.mp hd; omega
        have he := placeVertex_label s hs (.inl (.inr ⟨v.2.val, hsmall⟩))
        change label (2 * s) 2 2 v.2.val = lowEntry s (.inr ⟨v.2.val, hsmall⟩) at he
        have hr := lowEntry_range s hs (.inr ⟨v.2.val, hsmall⟩)
        change v.1.val = 2 at hv2
        simp only [hv2, he]
        nlinarith
      · simp only [hi, ite_false]
        have hr := formula_range s hs (⟨v, by change 0 < v.1.val; change v.1.val = 2 at hv2; omega⟩)
        rw [label_max_identity s hs] at hr
        have := depthTwoConstant_large s hs
        dsimp only at hr
        omega
  intro u v h
  rcases h with h | h
  · exact hdir u v h
  · exact (hdir v u h).symm

/-- Every high label is attained as a bottom-row incidence weight. -/
theorem high_color (s x : ℕ) (hs : 2 ≤ s)
    (hx : 4 * s < x ∧ x ≤ (2 * s)^2 + 2 * s) :
    ∃ v : Vertex (2 * s) 2, depth v = 2 ∧
      weight (tree (2 * s) 2) (depthTwoLabeling s hs) v = x := by
  rw [← label_max_identity s hs] at hx
  obtain ⟨p, hp, _⟩ := ordinary_label_unique s x hs hx
  let v := (placeVertex s hs (.inr p)).val
  refine ⟨v, rfl, ?_⟩
  rw [bottom_weight s hs v rfl]
  have he := placeVertex_label s hs (.inr p)
  change label (2 * s) 2 2 ((2 * s) * (p.1.val + 1) + p.2.val) = _ at he
  have hl : label (2 * s) 2 2 ((2 * s) * (p.1.val + 1) + p.2.val) =
      depthTwoLabel (2 * s) 2 ((2 * s) * (p.1.val + 1) + p.2.val) := by
    simp only [label, show ¬ (2 = 1) by decide, show ¬ (2 * s = 2) by omega, ite_false, ite_true]
  exact hl.trans hp

theorem depthTwo_colors (s : ℕ) (hs : 2 ≤ s) :
    colorCount (tree (2 * s) 2) (depthTwoLabeling s hs) = (2 * s)^2 + 1 := by
  let w := weight (tree (2 * s) 2) (depthTwoLabeling s hs)
  let leaves := (univ : Finset (Vertex (2 * s) 2)).filter (fun v => depth v = 2)
  have hcard : leaves.card = (2 * s)^2 := by
    change (univ.filter fun v : Vertex (2 * s) 2 => depth v = 2).card = _
    rw [← Fintype.card_subtype, ← Fintype.card_congr (bottomEquiv (2 * s) 2)]
    exact Fintype.card_fin _
  have hcover : univ.image w ⊆ insert (depthTwoConstant s) (leaves.image w) := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := mem_image.mp hx
    have hv := v.1.isLt
    by_cases hb : depth v = 2
    · exact mem_insert_of_mem (mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hb⟩, rfl⟩)
    · by_cases hz : depth v = 0
      · have hw : w v = (2 * s)^2 + 2 * s := by
          rw [unique_depth_zero v hz]; exact root_weight s hs
        obtain ⟨u, hu, huw⟩ := high_color s ((2 * s)^2 + 2 * s) hs (by constructor <;> nlinarith)
        exact mem_insert_of_mem (mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, hu⟩, huw.trans hw.symm⟩)
      · have h1 : v.1.val = 1 := by unfold depth at hz hb; omega
        have hw := row_one_weight s hs v h1
        by_cases hi : v.2.val = 0
        · simp only [hi, ite_true] at hw
          obtain ⟨u, hu, huw⟩ := high_color s ((2 * s)^2 + 2) hs (by constructor <;> nlinarith)
          exact mem_insert_of_mem (mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, hu⟩, huw.trans hw.symm⟩)
        · simp only [hi, ite_false] at hw
          exact mem_insert.mpr (Or.inl hw)
  apply Nat.le_antisymm
  · change (univ.image w).card ≤ _
    calc
      _ ≤ (insert (depthTwoConstant s) (leaves.image w)).card := card_le_card hcover
      _ ≤ (leaves.image w).card + 1 := card_insert_le _ _
      _ ≤ leaves.card + 1 := Nat.add_le_add_right (card_image_le) 1
      _ = _ := by rw [hcard]
  · exact lowerBound (2 * s) 2 (by omega) (by omega) _ (depthTwo_local s hs)


/-- The complete symbolic depth-two construction, including formula fidelity. -/
theorem depthTwo_construction (s : ℕ) (hs : 2 ≤ s) : FormulaConstruction (2 * s) 2 := by
  refine ⟨depthTwoLabeling s hs, ?_, depthTwo_local s hs, depthTwo_colors s hs⟩
  intro u v h
  let a : Nonroot (2 * s) 2 := ⟨v, by have := h.1; unfold depth; omega⟩
  have he : (⟨s(u, v), (tree (2 * s) 2).mem_edgeSet.mpr (Or.inl h)⟩ :
      (tree (2 * s) 2).edgeSet) = incomingEdge (by omega) a := by
    apply Subtype.ext
    change s(u, v) = s(parent (by omega) a, v)
    rw [← child_parent_unique h (by omega : 0 < 2 * s)]
  rw [he]
  exact depthTwoLabeling_label s hs a

/-- Round 3's first open construction Prop is now discharged. -/
theorem depthTwoConstruction : DepthTwoConstruction := by
  intro t ht he
  obtain ⟨s, hs⟩ := he
  have hts : t = 2 * s := by omega
  subst t
  simpa only [two_mul] using depthTwo_construction s (by omega)

#print axioms depthTwo_local
#print axioms depthTwo_colors
#print axioms depthTwo_construction
#print axioms depthTwoConstruction
end Antimagic.Round4A
