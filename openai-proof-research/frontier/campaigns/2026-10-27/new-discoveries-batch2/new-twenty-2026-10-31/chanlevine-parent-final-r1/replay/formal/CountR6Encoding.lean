import CountFinal4
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace ChanLevine.Round6
variable {n : ℕ} [NeZero n]

/-- Bounded chips retain exactly the original total-level constraint. -/
abbrev BoundedChips (n m : ℕ) [NeZero n] :=
  {x : ZMod n → Fin (m+1) // ∑ k, (x k).val = m}

def levelEquiv (m : ℕ) : {c : Config n // chipLevel c = m} ≃
    BoundedChips n m × (ZMod n → Bool) where
  toFun c := (⟨fun k => ⟨c.val.x k, chip_bound c.property k⟩, c.property⟩, c.val.q)
  invFun p := ⟨⟨fun k => (p.1.val k).val, p.2⟩, p.1.property⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv p := by rcases p with ⟨⟨x,hx⟩,q⟩; rfl

theorem sum_level_reindex {R : Type*} [AddCommMonoid R] (m : ℕ)
    (f : Config n → R) :
    (∑ c : {c : Config n // chipLevel c = m}, f c.val) =
      ∑ p : BoundedChips n m × (ZMod n → Bool),
        f ⟨fun k => (p.1.val k).val, p.2⟩ := by
  classical
  exact (levelEquiv m).sum_comp (fun p => f ⟨fun k => (p.1.val k).val, p.2⟩)

/-- Selected oriented edges form a cyclic matching; the wrap edge is included. -/
def Matching (s : Finset (ZMod n)) : Prop := ∀ k ∈ s, k+1 ∉ s

def rightEnds (s : Finset (ZMod n)) : Finset (ZMod n) :=
  s.image (fun k => k+1)

omit [NeZero n] in
theorem rightEnds_card (s : Finset (ZMod n)) : (rightEnds s).card = s.card := by
  classical
  exact Finset.card_image_of_injective s (add_left_injective 1)

omit [NeZero n] in
theorem matching_disjoint (s : Finset (ZMod n)) (hs : Matching s) :
    Disjoint s (rightEnds s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hk hr
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hr
  exact hs j hj hk

omit [NeZero n] in
theorem facing_matching (c : Config n) (s : Finset (ZMod n))
    (hs : ∀ k ∈ s, Round5.emptyFacing c k) : Matching s := by
  intro k hk hn
  exact Round5.facing_not_adjacent c k (hs k hk) (hs (k+1) hn)

omit [NeZero n] in
theorem endpoints_card (s : Finset (ZMod n)) (hs : Matching s) :
    (s ∪ rightEnds s).card = 2*s.card := by
  classical
  rw [Finset.card_union_of_disjoint (matching_disjoint s hs), rightEnds_card]
  omega

theorem matching_size (s : Finset (ZMod n)) (hs : Matching s) :
    2*s.card ≤ n := by
  have h := Finset.card_le_card (Finset.subset_univ (s ∪ rightEnds s))
  simpa only [endpoints_card s hs, Finset.card_univ, ZMod.card] using h

omit [NeZero n] in
/-- An impossible selected-edge set vanishes before any character summation. -/
theorem nonmatching_indicator {R : Type*} [CommRing R] (c : Config n)
    (s : Finset (ZMod n)) (hs : ¬ Matching s) :
    (∏ k ∈ s, (if Round5.emptyFacing c k then (1 : R) else 0)) = 0 := by
  classical
  have h : ∃ k ∈ s, ¬ Round5.emptyFacing c k := by
    by_contra h
    push Not at h
    exact hs (facing_matching c s h)
  obtain ⟨k,hk,h⟩ := h
  exact Finset.prod_eq_zero hk (by simp [h])
end ChanLevine.Round6
