import Abundance
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame
attribute [local instance] Classical.propDecidable

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
    · simp
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

theorem cylinder_success {N j : ℕ} {u : List Move} (hu : u.length=3*j) :
    (cylinderDomain N u).filter (fun w => SuccessAt w j) =
      cylinderDomain N (u ++ [.C1,.C1,C2]) := by
  classical
  ext w
  simp only [cylinderDomain,Finset.mem_filter]
  constructor
  · rintro ⟨⟨hw,hp⟩,v,z,hv,he⟩
    have ht : w.take (3*j)=u := by obtain ⟨z,rfl⟩ := hp; simp [← hu]
    have ht' : w.take (3*j)=v := by rw [he,← hv]; simp [List.append_assoc]
    have : v=u := ht'.symm.trans ht
    rw [this] at he
    exact ⟨hw,z,he.symm⟩
  · rintro ⟨hw,z,he⟩
    have he' : w=u ++ [.C1,.C1,C2] ++ z := he.symm
    refine ⟨⟨hw,?_⟩,u,z,hu,he'⟩
    exact ⟨[.C1,.C1,C2] ++ z,by simpa [List.append_assoc] using he⟩

theorem cylinder_step {N n j : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) (hl : u.length=3*j)
    (hn : 1≤n) (hN : N < F (n+1)) (hj : j<N/6) :
    (∑ w ∈ cylinderDomain N u,
      P N w * (1/2 : ℚ)^(successSlots (j+1) w).card) ≤
      (∑ w ∈ cylinderDomain N u,
        P N w * (1/2 : ℚ)^(successSlots j w).card) * (1-blockLower n/2) := by
  classical
  let a : ℚ := (1/2 : ℚ)^(successSlots j u).card
  have hc (w : List Move) (hw : w ∈ cylinderDomain N u) :
      (1/2 : ℚ)^(successSlots j w).card = a := by
    have ht : w.take (3*j)=u := by
      obtain ⟨_,v,rfl⟩ := Finset.mem_filter.mp hw
      simp [← hl]
    dsimp [a]
    rw [← slots_take w j,ht]
  have he : (∑ w ∈ cylinderDomain N u,
      P N w * (1/2 : ℚ)^(successSlots (j+1) w).card) =
      a * (cylinderMass N u - cylinderMass N (u ++ [.C1,.C1,C2])/2) := by
    calc
      _ = ∑ w ∈ cylinderDomain N u,
          (a * P N w - (if SuccessAt w j then a * P N w / 2 else 0)) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [slots_succ,pow_add,hc w hw]
        split_ifs <;> norm_num <;> ring
      _ = _ := by
        rw [Finset.sum_sub_distrib,← Finset.mul_sum]
        simp only [← Finset.sum_filter]
        rw [cylinder_success hl]
        simp only [div_eq_mul_inv,← Finset.sum_mul,← Finset.mul_sum]
        simp only [cylinderMass]
        ring
  have he0 : (∑ w ∈ cylinderDomain N u,
      P N w * (1/2 : ℚ)^(successSlots j w).card) = a*cylinderMass N u := by
    calc
      _ = ∑ w ∈ cylinderDomain N u, P N w * a := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [hc w hw]
      _ = _ := by rw [← Finset.sum_mul]; simp [cylinderMass,mul_comm]
  have hp := (actual_early_success_lower hu hn hN hl hj).2.2
  have hpos := actual_prefix_positive hu
  have hmul : blockLower n * cylinderMass N u ≤ cylinderMass N (u ++ [.C1,.C1,C2]) :=
    (le_div_iff₀ hpos).mp hp
  rw [he,he0]
  have ha : 0≤a := by dsimp [a]; positivity
  nlinarith

end LiteralGame
