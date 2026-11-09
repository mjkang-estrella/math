import LastSplit
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame
attribute [local instance] Classical.propDecidable

-- One-based greatest split position; zero means that there is no split.
noncomputable def lastSplit : List Move → ℕ
  | [] => 0
  | m::v => if lastSplit v = 0 then (if IsSplit m then 1 else 0)
      else lastSplit v + 1

theorem lastSplit_le (w : List Move) : lastSplit w ≤ w.length := by
  induction w with
  | nil => simp [lastSplit]
  | cons m v ih => simp only [lastSplit,List.length_cons]; split <;> split_ifs <;> omega

theorem lastSplit_zero_iff (w : List Move) :
    lastSplit w = 0 ↔ ∀ m ∈ w, ¬ IsSplit m := by
  induction w with
  | nil => simp [lastSplit]
  | cons m v ih =>
    simp only [lastSplit,List.forall_mem_cons]
    by_cases h : lastSplit v = 0
    · simp [h,ih.mp h]
    · have hv : ¬ (∀ m ∈ v, ¬ IsSplit m) := by simpa [← ih] using h
      simp [h,hv]

theorem after_lastSplit (w : List Move) :
    ∀ m ∈ w.drop (lastSplit w), ¬ IsSplit m := by
  induction w with
  | nil => simp
  | cons m v ih =>
    by_cases h : lastSplit v = 0
    · have hv := (lastSplit_zero_iff v).mp h
      by_cases hm : IsSplit m
      · simpa [lastSplit,h,hm] using hv
      · simpa [lastSplit,h,hm] using (show ∀ k ∈ m::v, ¬ IsSplit k by simp [hm,hv])
    · simpa [lastSplit,h,List.drop_succ_cons] using ih

-- Literal complete-word event: q successive full three-move blocks, with
-- high-token starts. Each recursive step consumes exactly three letters.
def BlockEvent (N n : ℕ) (u : List Move) : ℕ → List Move → Prop
  | 0, w => u.IsPrefix w
  | q+1, w => HighPrefix N n u ∧ u.length+3 ≤ w.length ∧
      u.IsPrefix w ∧ ¬ HasSplit ((w.drop u.length).take 3) ∧
      BlockEvent N n (w.take (u.length+3)) q w

noncomputable def eventDomain (N n : ℕ) (u : List Move) (q : ℕ) :=
  (completeDomain N).filter (BlockEvent N n u q)

theorem event_subset_cylinder (N n : ℕ) (u : List Move) (q : ℕ) :
    eventDomain N n u q ⊆ cylinderDomain N u := by
  intro w hw
  obtain ⟨hw,he⟩ := Finset.mem_filter.mp hw
  apply Finset.mem_filter.mpr
  exact ⟨hw,by cases q with | zero => exact he | succ q => exact he.2.2.1⟩

theorem event_step (N n : ℕ) (u : List Move) (q : ℕ) :
    eventDomain N n u (q+1) = if HighPrefix N n u then
      (blockChildren N u).biUnion (fun v => eventDomain N n v q) else ∅ := by
  classical
  ext w
  by_cases hh : HighPrefix N n u
  · simp only [if_pos hh,Finset.mem_biUnion]
    constructor
    · intro hw
      obtain ⟨hw,_,hl,hp,hs,he⟩ := Finset.mem_filter.mp hw
      refine ⟨w.take (u.length+3),?_,Finset.mem_filter.mpr ⟨hw,he⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨w,hw,rfl⟩,by simp [List.length_take, Nat.min_eq_left hl],?_,?_⟩
      · simpa using hp.take (u.length+3)
      · simpa [List.drop_take] using hs
    · rintro ⟨v,hv,hw⟩
      have hwc := event_subset_cylinder N n v q hw
      obtain ⟨hw0,hp⟩ := Finset.mem_filter.mp hwc
      obtain ⟨_,hlen,hu,hs⟩ := Finset.mem_filter.mp hv
      have he := (Finset.mem_filter.mp hw).2
      have ht : w.take (u.length+3)=v := by rw [← hlen]; exact hp.take_eq
      have hl : u.length+3 ≤ w.length := by rw [← hlen]; exact hp.length_le
      apply Finset.mem_filter.mpr
      refine ⟨hw0,hh,hl,hu.trans hp,?_,by rwa [ht]⟩
      have hdrop := congrArg (List.drop u.length) ht
      simpa [List.drop_take] using hdrop ▸ hs
  · simp [eventDomain,BlockEvent,hh]

theorem literal_event_mass (N n : ℕ) (u : List Move) (q : ℕ) :
    (∑ w ∈ eventDomain N n u q, P N w) = blockTreeMass N n u q := by
  classical
  induction q generalizing u with
  | zero => rfl
  | succ q ih =>
    rw [event_step,blockTreeMass]
    by_cases hh : HighPrefix N n u
    · rw [if_pos hh,if_pos hh,Finset.sum_biUnion]
      · exact Finset.sum_congr rfl (by intro v _; exact ih v)
      · intro v hv z hz hne
        exact Finset.disjoint_of_subset (event_subset_cylinder N n v q)
          (event_subset_cylinder N n z q)
          (same_length_cylinders_disjoint N
            ((Finset.mem_filter.mp hv).2.1.trans (Finset.mem_filter.mp hz).2.1.symm) hne)
    · simp [hh]

end LiteralGame
