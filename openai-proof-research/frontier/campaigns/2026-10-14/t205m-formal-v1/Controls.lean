import T205M

/- Original support controls: Myeongjin Kang, MIT. -/
namespace T205MControls

def chainPrefix : Finset (Fin 4) := {0, 1}

theorem chainPrefix_ideal : T205M.IsIdeal chainPrefix := by
  simp only [T205M.IsIdeal, chainPrefix]
  decide

theorem chainPrefix_unique : ∀ t : Finset (Fin 4),
    T205M.IsIdeal t → t.card = chainPrefix.card → t = chainPrefix := by
  simp only [T205M.IsIdeal, chainPrefix]
  decide

theorem chainPrefix_cross {a b : Fin 4}
    (ha : a ∈ chainPrefix) (hb : b ∉ chainPrefix) : a ≤ b :=
  T205M.unique_rank_cross_comparable chainPrefix_ideal chainPrefix_unique ha hb

theorem product_has_rank_four : ∃ s : Finset (Fin 3 × Fin 3),
    T205M.IsIdeal s ∧ s.card = 4 := by
  have hu : T205M.IsIdeal (Finset.univ : Finset (Fin 3 × Fin 3)) := by
    intro x y _ _
    exact Finset.mem_univ x
  obtain ⟨s, hs, _, _, hc⟩ := T205M.ideal_interval_rank
    T205M.empty_ideal hu (Finset.empty_subset _) (r := 4) (by simp) (by decide)
  exact ⟨s, hs, hc⟩

inductive Two where
  | left
  | right
  deriving DecidableEq

instance : Fintype Two where
  elems := {Two.left, Two.right}
  complete := by intro x; cases x <;> simp

instance : PartialOrder Two where
  le := Eq
  le_refl := Eq.refl
  le_trans := fun _ _ _ h h' => Eq.trans h h'
  le_antisymm := fun _ _ h _ => h

instance : DecidableLE Two := fun _ _ => inferInstanceAs (Decidable (_ = _))

theorem antichain_singleton_ideal : T205M.IsIdeal ({Two.left} : Finset Two) := by
  intro x y hy hxy
  change x = y at hxy
  exact hxy ▸ hy

theorem antichain_noncomparable : ¬Two.left ≤ Two.right := by
  change ¬Two.left = Two.right
  decide

theorem antichain_second_ideal : ∃ t : Finset Two,
    T205M.IsIdeal t ∧ t.card = ({Two.left} : Finset Two).card ∧
      t ≠ {Two.left} :=
  T205M.exists_second_ideal_of_incomparable antichain_singleton_ideal
    (by simp) (by simp) antichain_noncomparable

theorem uniqueness_cannot_be_dropped : ¬(∀ (s : Finset Two), T205M.IsIdeal s →
    ∀ a ∈ s, ∀ b ∉ s, a ≤ b) := by
  intro h
  exact antichain_noncomparable
    (h {Two.left} antichain_singleton_ideal Two.left (by simp) Two.right (by simp))

theorem rank_upper_bound_cannot_be_dropped : ¬(∃ s : Finset (Fin 3),
    T205M.IsIdeal s ∧ s.card = 4) := by
  rintro ⟨s, _, hs⟩
  have h := Finset.card_le_univ s
  simp only [Fintype.card_fin] at h
  omega

end T205MControls
