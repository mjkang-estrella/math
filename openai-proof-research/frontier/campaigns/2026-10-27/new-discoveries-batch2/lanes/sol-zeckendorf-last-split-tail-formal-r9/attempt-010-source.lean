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

theorem actual_regroup (N j : ℕ) (f : List Move → ℚ) :
    (∑ w ∈ completeDomain N, f w) =
      ∑ u ∈ (completeDomain N).image (List.take (3*j)),
        ∑ w ∈ (completeDomain N).filter (fun w => w.take (3*j)=u), f w := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (fun w hw => Finset.mem_image_of_mem (List.take (3*j)) hw) f).symm

theorem moment_step {N n j : ℕ} (hn : 1≤n) (hN : N<F (n+1)) (hj : j<N/6) :
    moment N (j+1) ≤ moment N j * (1-blockLower n/2) := by
  classical
  unfold moment
  rw [actual_regroup N j,actual_regroup N j,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro u hu
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hu
  have hlen := complete_length_blocks ((domain_exact N w).mp hw)
  have hl : (w.take (3*j)).length=3*j := by
    rw [List.length_take,Nat.min_eq_left]; omega
  obtain ⟨c,he,_⟩ := (domain_exact N w).mp hw
  obtain ⟨b,hb,_⟩ := executes_split
    (u:=w.take (3*j)) (v:=w.drop (3*j)) (by simpa using he)
  rw [prefix_fiber hl]
  exact cylinder_step hb hl hn hN hj

theorem blockLower_bounds {n : ℕ} (hn : 1≤n) : 0≤blockLower n ∧ blockLower n≤1 := by
  have h : (1 : ℚ) ≤ ((2*n : ℕ) : ℚ) := by exact_mod_cast (show 1≤2*n by omega)
  have hi : (0 : ℚ) ≤ ((2*n : ℕ) : ℚ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hi1 : (((2*n : ℕ) : ℚ)⁻¹) ≤ 1 := by
    have hx : (0 : ℚ) < ((2*n : ℕ) : ℚ) := by linarith
    simpa using (inv_le_inv₀ hx (by norm_num : (0:ℚ)<1)).mpr h
  constructor
  · dsimp [blockLower]; positivity
  · dsimp [blockLower]
    calc
      _ ≤ (1 : ℚ)^3 := pow_le_pow_left₀ hi hi1 _
      _ = 1 := by norm_num

theorem moment_zero (N : ℕ) : moment N 0 = 1 := by
  simpa [moment,successSlots] using P_normalized N

theorem actual_finite_moment {N n : ℕ} (hn : 1≤n) (hN : N<F (n+1)) :
    (∑ w ∈ completeDomain N, P N w *
      (1/2 : ℚ)^(successSlots (N/6) w).card) ≤ (1-blockLower n/2)^(N/6) := by
  have hc : 0≤1-blockLower n/2 := by have := blockLower_bounds hn; linarith
  have hind : ∀ j, j≤N/6 → moment N j ≤ (1-blockLower n/2)^j := by
    intro j
    induction j with
    | zero => intro _; simp [moment_zero]
    | succ j ih =>
      intro hj
      calc
        _ ≤ moment N j * (1-blockLower n/2) := moment_step hn hN (by omega)
        _ ≤ (1-blockLower n/2)^j * (1-blockLower n/2) :=
          mul_le_mul_of_nonneg_right (ih (by omega)) hc
        _ = _ := (pow_succ _ _).symm
  exact hind (N/6) (le_refl _)

theorem dyadic_indicator (k t : ℕ) (h : k<t) :
    (1 : ℚ) ≤ 2^t * (1/2 : ℚ)^k := by
  have hp : (2 : ℚ)^k ≤ 2^t := pow_le_pow_right₀ (by norm_num) (by omega)
  have hi : (0 : ℚ) < (1/2 : ℚ)^k := by positivity
  have he : (2 : ℚ)^k * (1/2 : ℚ)^k = 1 := by rw [← mul_pow]; norm_num
  nlinarith

theorem bad_success_markov (N t : ℕ) : badSuccessMass N t ≤ 2^t * moment N (N/6) := by
  classical
  calc
    _ ≤ ∑ w ∈ (completeDomain N).filter (fun w => (successSlots (N/6) w).card<t),
        (2^t * (P N w * (1/2 : ℚ)^(successSlots (N/6) w).card)) := by
      apply Finset.sum_le_sum
      intro w hw
      have hd := dyadic_indicator _ t (Finset.mem_filter.mp hw).2
      have hp := P_nonneg N w
      nlinarith
    _ ≤ ∑ w ∈ completeDomain N,
        (2^t * (P N w * (1/2 : ℚ)^(successSlots (N/6) w).card)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro w _ _
      exact mul_nonneg (by positivity) (mul_nonneg (P_nonneg N w) (by positivity))
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem actual_finite_tail {N n : ℕ} (hn : 1≤n) (hN : N<F (n+1)) (t : ℕ) :
    badMarksMass N t ≤ (2 : ℚ)^t * (1-blockLower n/2)^(N/6) := by
  calc
    _ ≤ badSuccessMass N t := actual_bad_marks_le_bad_success N t
    _ ≤ (2 : ℚ)^t * moment N (N/6) := bad_success_markov N t
    _ ≤ _ := mul_le_mul_of_nonneg_left (actual_finite_moment hn hN) (by positivity)

theorem tail_threshold_zero (N : ℕ) :
    badMarksMass N 0 = 0 ∧ badSuccessMass N 0 = 0 := bad_threshold_zero N

theorem moment_zero_input :
    (∑ w ∈ completeDomain 0, P 0 w *
      (1/2 : ℚ)^(successSlots (0/6) w).card) = 1 := moment_zero 0

theorem tail_zero_input (n t : ℕ) :
    badMarksMass 0 t ≤ (2 : ℚ)^t * (1-blockLower n/2)^(0/6) := by
  rw [zero_input_bad_mass]
  simp only [Nat.zero_div,pow_zero,mul_one]
  split_ifs
  · simpa using (pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (Nat.zero_le t))
  · positivity

theorem zero_weight_term {N : ℕ} {w : List Move} (hw : P N w=0) (j : ℕ) :
    P N w * (1/2 : ℚ)^(successSlots j w).card = 0 := by rw [hw,zero_mul]

end LiteralGame
