import Abundance
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame

theorem success_prefix_iff (w : List Move) (j : ℕ) :
    SuccessAt w j ↔ ∃ u, u.length = 3*j ∧ (u ++ [.C1,.C1,C2]).IsPrefix w := by
  constructor
  · rintro ⟨u,v,hl,rfl⟩
    exact ⟨u,hl,v,rfl⟩
  · rintro ⟨u,hl,v,hv⟩
    exact ⟨u,v,hl,hv.symm⟩

theorem success_take_iff (w : List Move) (j L : ℕ) (h : 3*j+3 ≤ L) :
    SuccessAt (w.take L) j ↔ SuccessAt w j := by
  rw [success_prefix_iff,success_prefix_iff]
  constructor
  · rintro ⟨u,hu,hp⟩
    exact ⟨u,hu,hp.trans (List.take_prefix L w)⟩
  · rintro ⟨u,hu,hp⟩
    refine ⟨u,hu,?_⟩
    have hl : (u ++ [.C1,.C1,C2]).length ≤ L := by simp [hu]; omega
    simpa [List.take_of_length_le hl] using hp.take L

theorem slots_take (w : List Move) (j : ℕ) :
    successSlots j (w.take (3*j)) = successSlots j w := by
  classical
  ext k
  simp only [successSlots,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨hk,hs⟩
    exact ⟨hk,(success_take_iff w k (3*j) (by omega)).mp hs⟩
  · rintro ⟨hk,hs⟩
    exact ⟨hk,(success_take_iff w k (3*j) (by omega)).mpr hs⟩

theorem slots_succ (w : List Move) (j : ℕ) :
    (successSlots (j+1) w).card = (successSlots j w).card +
      (if SuccessAt w j then 1 else 0) := by
  classical
  simp only [successSlots,Finset.range_add_one,Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

noncomputable def moment (N j : ℕ) : ℚ :=
  ∑ w ∈ completeDomain N, P N w * (1/2 : ℚ)^(successSlots j w).card

theorem prefix_fiber {N j : ℕ} {u : List Move} (hu : u.length=3*j) :
    (completeDomain N).filter (fun w => w.take (3*j)=u) = cylinderDomain N u := by
  classical
  ext w
  simp only [Finset.mem_filter,cylinderDomain]
  constructor
  · rintro ⟨hw,he⟩
    exact ⟨hw,he ▸ List.take_prefix (3*j) w⟩
  · rintro ⟨hw,v,rfl⟩
    exact ⟨hw,by simp [← hu]⟩

theorem moment_partition (N j : ℕ) :
    moment N j = ∑ u ∈ (completeDomain N).image (List.take (3*j)),
      ∑ w ∈ (completeDomain N).filter (fun w => w.take (3*j)=u),
        P N w * (1/2 : ℚ)^(successSlots j w).card := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (fun w hw => Finset.mem_image_of_mem (List.take (3*j)) hw) _).symm

end LiteralGame
