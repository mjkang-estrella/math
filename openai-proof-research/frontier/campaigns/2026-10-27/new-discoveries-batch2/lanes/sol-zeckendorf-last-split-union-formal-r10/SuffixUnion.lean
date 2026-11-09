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
  | cons m v ih => simp only [lastSplit,List.length_cons]; split_ifs <;> omega

theorem lastSplit_zero_iff (w : List Move) :
    lastSplit w = 0 ↔ ∀ m ∈ w, ¬ IsSplit m := by
  induction w with
  | nil => simp [lastSplit]
  | cons m v ih =>
    simp only [lastSplit,List.forall_mem_cons]
    by_cases h : lastSplit v = 0
    · simp only [h,ite_true]; split_ifs <;> simp_all
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
      · simpa [lastSplit,h,hm] using (show ∀ k ∈ m::v, ¬ IsSplit k by simp only [List.forall_mem_cons]; exact ⟨hm,hv⟩)
    · simpa [lastSplit,h,List.drop_succ_cons] using ih

theorem lastSplit_cut (w : List Move) (r : ℕ) :
    lastSplit w ≤ r ↔ ∀ m ∈ w.drop r, ¬ IsSplit m := by
  induction w generalizing r with
  | nil => simp [lastSplit]
  | cons m v ih =>
    cases r with
    | zero => simpa using lastSplit_zero_iff (m::v)
    | succ r =>
      by_cases h : lastSplit v = 0
      · have hv := (ih r).mp (show lastSplit v ≤ r by omega)
        simp only [lastSplit,h,ite_true,List.drop_succ_cons]
        split_ifs <;> simp_all
      · simpa [lastSplit,h,List.drop_succ_cons] using ih r

theorem split_position_le (u v : List Move) (m : Move) (hm : IsSplit m) :
    u.length+1 ≤ lastSplit (u++m::v) := by
  by_contra h
  have hc := (lastSplit_cut (u++m::v) u.length).mp (by omega)
  exact hc m (by simp) hm

theorem lastSplit_attained (w : List Move) (h : 0 < lastSplit w) :
    ∃ u m v, w=u++m::v ∧ IsSplit m ∧ lastSplit w=u.length+1 := by
  induction w with
  | nil => simp [lastSplit] at h
  | cons m w ih =>
    by_cases hz : lastSplit w=0
    · have hm : IsSplit m := by
        by_contra hn
        simp [lastSplit,hz,hn] at h
      exact ⟨[],m,w,rfl,hm,by simp [lastSplit,hz,hm]⟩
    · obtain ⟨u,k,v,hw,hk,hl⟩ := ih (by omega)
      refine ⟨m::u,k,v,by simp [hw],hk,?_⟩
      simp [lastSplit,hz,hl]

-- Literal complete-word event: q successive full three-move blocks, with
-- high-token starts. Each recursive step consumes exactly three letters.
noncomputable def BlockEvent (N n : ℕ) (u : List Move) : ℕ → List Move → Prop
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
  · simp only [ite_eq_left hh,Finset.mem_biUnion]
    constructor
    · intro hw
      obtain ⟨hw,_,hl,hp,hs,he⟩ := Finset.mem_filter.mp hw
      refine ⟨w.take (u.length+3),?_,Finset.mem_filter.mpr ⟨hw,he⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨w,hw,rfl⟩,by simp [List.length_take, Nat.min_eq_left hl],?_,?_⟩
      · simpa [List.take_of_length_le (show u.length ≤ u.length+3 by omega)] using hp.take (u.length+3)
      · simpa [List.drop_take] using hs
    · rintro ⟨v,hv,hw⟩
      have hwc := event_subset_cylinder N n v q hw
      obtain ⟨hw0,hp⟩ := Finset.mem_filter.mp hwc
      obtain ⟨_,hlen,hu,hs⟩ := Finset.mem_filter.mp hv
      have he := (Finset.mem_filter.mp hw).2
      have ht : w.take (u.length+3)=v := by rw [← hlen]; obtain ⟨z,rfl⟩ := hp; simp
      have hl : u.length+3 ≤ w.length := by rw [← hlen]; exact hp.length_le
      apply Finset.mem_filter.mpr
      refine ⟨hw0,hh,hl,hu.trans hp,?_,by rwa [ht]⟩
      have hdrop := congrArg (List.drop u.length) ht
      rw [List.drop_take] at hdrop
      have hd : (w.drop u.length).take 3 = v.drop u.length := by simpa using hdrop
      rw [hd]; exact hs
  · simp [eventDomain,BlockEvent,hh]

theorem literal_event_mass (N n : ℕ) (u : List Move) (q : ℕ) :
    (∑ w ∈ eventDomain N n u q, P N w) = blockTreeMass N n u q := by
  classical
  induction q generalizing u with
  | zero =>
    have hd : eventDomain N n u 0 = cylinderDomain N u := by
      ext w
      unfold eventDomain cylinderDomain
      rw [Finset.mem_filter,Finset.mem_filter]
      rfl
    rw [hd]; rfl
  | succ q ih =>
    rw [event_step,blockTreeMass]
    by_cases hh : HighPrefix N n u
    · rw [ite_eq_left hh,ite_eq_left hh,Finset.sum_biUnion]
      · exact Finset.sum_congr rfl (by intro v _; exact ih v)
      · intro v hv z hz hne
        apply Finset.disjoint_of_subset_left (event_subset_cylinder N n v q)
          (Finset.disjoint_of_subset_right (event_subset_cylinder N n z q)
          (same_length_cylinders_disjoint N
            ((Finset.mem_filter.mp hv).2.1.trans (Finset.mem_filter.mp hz).2.1.symm) hne))
    · simp [hh]

theorem long_suffix_event {N n : ℕ} {w : List Move}
    (hw : w ∈ completeDomain N) (q r : ℕ) (hr : r ≤ w.length)
    (hs : ∀ m ∈ w.drop r, ¬ IsSplit m)
    (hl : 3*q+n+3 < (w.drop r).length) :
    BlockEvent N n (w.take r) q w := by
  induction q generalizing r with
  | zero => exact List.take_prefix r w
  | succ q ih =>
    have hlen : (w.take r).length = r := by simp [Nat.min_eq_left hr]
    obtain ⟨c,he,_⟩ := (domain_exact N w).mp hw
    obtain ⟨b,hb,hv⟩ := executes_split
      (u:=w.take r) (v:=w.drop r) (by simpa using he)
    obtain ⟨d,hd,hh⟩ := long_combine_suffix_high hv hs hl (show 0≤q+1 by omega)
    have hdb : b=d := by cases (show Executes b [] d by simpa using hd); rfl
    subst d
    have hr3 : r+3 ≤ w.length := by simp only [List.length_drop] at hl; omega
    have hs3 : ∀ m ∈ w.drop (r+3), ¬ IsSplit m := by
      intro m hm
      apply hs m
      exact List.mem_of_mem_drop (by simpa [List.drop_drop] using hm : m ∈ (w.drop r).drop 3)
    have hl3 : 3*q+n+3 < (w.drop (r+3)).length := by
      simp only [List.length_drop] at *; omega
    refine ⟨⟨b,hb,hh⟩,by omega,List.take_prefix r w,?_,?_⟩
    · rintro ⟨m,hm,hm'⟩
      exact hs m (List.mem_of_mem_take (by simpa [hlen] using hm)) hm'
    · simpa [hlen] using ih (r+3) hr3 hs3 hl3

noncomputable def fixedEventDomain (N n r q : ℕ) : Finset (List Move) :=
  (prefixesAt N r).biUnion (fun u => eventDomain N n u q)

theorem fixed_literal_mass (N n r q : ℕ) :
    (∑ w ∈ fixedEventDomain N n r q, P N w) = fixedBlockMass N n r q := by
  classical
  rw [fixedEventDomain,Finset.sum_biUnion]
  · exact Finset.sum_congr rfl (by intro u _; exact literal_event_mass N n u q)
  · intro u hu v hv hne
    apply Finset.disjoint_of_subset_left (event_subset_cylinder N n u q)
      (Finset.disjoint_of_subset_right (event_subset_cylinder N n v q)
      (same_length_cylinders_disjoint N
        ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm) hne))

theorem complete_length_le {N : ℕ} {w : List Move}
    (hw : w ∈ completeDomain N) : w.length ≤ 3*N := by
  by_cases hN : N=0
  · subst N
    have hz : completeDomain 0 = {[]} := completeDomain_zero
    simpa [hz] using hw
  · obtain ⟨b,hb,_⟩ := (domain_exact N w).mp hw
    exact Nat.le_of_lt (all_prefix_length_lt (by omega) hb)

noncomputable def suffixTailDomain (N n q : ℕ) : Finset (List Move) :=
  (completeDomain N).filter (fun w => 3*q+n+3 < w.length-lastSplit w)
noncomputable def suffixTailMass (N n q : ℕ) : ℚ :=
  ∑ w ∈ suffixTailDomain N n q, P N w

theorem suffixTailMass_zero (n q : ℕ) : suffixTailMass 0 n q = 0 := by
  have hd : suffixTailDomain 0 n q = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hw,hl⟩ := Finset.mem_filter.mp hw
    have hw' : w=[] := by simpa [completeDomain_zero] using hw
    subst w
    simp [lastSplit] at hl
  simp [suffixTailMass,hd]

theorem suffix_empty_iff (w : List Move) :
    w.drop (lastSplit w) = [] ↔ lastSplit w = w.length := by
  rw [List.drop_eq_nil_iff]
  have := lastSplit_le w
  omega

theorem short_word_excluded {N n q : ℕ} {w : List Move}
    (h : w.length ≤ 3*q+n+3) : w ∉ suffixTailDomain N n q := by
  intro hw
  have := (Finset.mem_filter.mp hw).2
  omega

theorem suffix_tail_inclusion (N n q : ℕ) :
    suffixTailDomain N n q ⊆ (Finset.range (3*N+1)).biUnion
      (fun r => fixedEventDomain N n r q) := by
  classical
  intro w hw
  obtain ⟨hw,hl⟩ := Finset.mem_filter.mp hw
  have hr := lastSplit_le w
  refine Finset.mem_biUnion.mpr ⟨lastSplit w,Finset.mem_range.mpr
    (by have := complete_length_le hw; omega),?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨w.take (lastSplit w),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨w,hw,rfl⟩,
      by simp [Nat.min_eq_left hr]⟩
  · exact Finset.mem_filter.mpr ⟨hw,long_suffix_event hw q (lastSplit w) hr
      (after_lastSplit w) (by simpa using hl)⟩

theorem mass_union_le (N : ℕ) (s : Finset ℕ) (f : ℕ → Finset (List Move)) :
    (∑ w ∈ s.biUnion f, P N w) ≤ ∑ r ∈ s, ∑ w ∈ f r, P N w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert r s hr ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hr]
    have he : (∑ w ∈ f r ∪ s.biUnion f, P N w) +
        (∑ w ∈ f r ∩ s.biUnion f, P N w) =
        (∑ w ∈ f r, P N w) + (∑ w ∈ s.biUnion f, P N w) := Finset.sum_union_inter
    have hz : 0 ≤ ∑ w ∈ f r ∩ s.biUnion f, P N w :=
      Finset.sum_nonneg (by intro w _; exact P_nonneg N w)
    linarith

theorem suffixTailMass_bound {N n : ℕ} (hn : 1≤n) (hN : N<F (n+1)) (q : ℕ) :
    suffixTailMass N n q ≤ (3*N+1 : ℕ) * (1-blockLower n)^q := by
  classical
  calc
    _ ≤ ∑ w ∈ (Finset.range (3*N+1)).biUnion (fun r => fixedEventDomain N n r q), P N w :=
      Finset.sum_le_sum_of_subset_of_nonneg (suffix_tail_inclusion N n q)
        (by intro w _ _; exact P_nonneg N w)
    _ ≤ ∑ r ∈ Finset.range (3*N+1), ∑ w ∈ fixedEventDomain N n r q, P N w :=
      mass_union_le N _ _
    _ ≤ ∑ _r ∈ Finset.range (3*N+1), (1-blockLower n)^q := by
      apply Finset.sum_le_sum
      intro r _
      rw [fixed_literal_mass]
      exact actual_fixed_deterministic_blocks hn hN r q
    _ = _ := by simp
end LiteralGame
