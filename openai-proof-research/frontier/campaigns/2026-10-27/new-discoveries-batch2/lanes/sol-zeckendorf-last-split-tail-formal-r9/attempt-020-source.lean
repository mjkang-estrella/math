import Assembly
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame
attribute [local instance] Classical.propDecidable

def IsSplit (m : Move) : Prop := combine m = 0
def HasSplit (v : List Move) : Prop := ∃ m ∈ v, IsSplit m

theorem higher_duplicate_or_four {b : Board} {n : ℕ} (hn : 1 ≤ n)
    (hp : Positive b) (hv : value b < F (n+1)) (hh : n+2 < b.card) :
    (∃ i, 2 ≤ i ∧ 2 ≤ b.count i) ∨ 4 ≤ b.count 1 := by
  classical
  by_cases hd : ∃ i, 2 ≤ i ∧ 2 ≤ b.count i
  · exact Or.inl hd
  right
  have hb : b ≤ Multiset.replicate (b.count 1) 1 + (Finset.Icc 2 n).val := by
    apply Multiset.le_iff_count.mpr
    intro i
    by_cases hi : i=1
    · subst i; simp
    by_cases hm : i ∈ b
    · have hlo := hp i hm
      have hhi := index_bound hv hm
      have hcount : b.count i ≤ 1 := by
        by_contra hc
        exact hd ⟨i,by omega,by omega⟩
      have hm' : i ∈ Finset.Icc 2 n := by simp; omega
      have hc' := Multiset.count_eq_one_of_mem (Finset.Icc 2 n).nodup hm'
      simpa [hi,Ne.symm hi,Multiset.count_replicate,hc'] using hcount
    · simp [Multiset.count_eq_zero.mpr hm]
  have hc := Multiset.card_le_card hb
  simp only [Multiset.card_add,Multiset.card_replicate] at hc
  change b.card ≤ b.count 1 + (Finset.Icc 2 n).card at hc
  rw [Nat.card_Icc] at hc
  omega

theorem duplicate_split {b : Board} {i : ℕ} (hi : 2 ≤ i) (hc : 2 ≤ b.count i) :
    ∃ m, m ∈ legalTypes b ∧ IsSplit m := by
  have hdup : ({i,i} : Board) ≤ b := by
    apply Multiset.le_iff_count.mpr
    intro k
    by_cases hk : k=i
    · subst k; simpa using hc
    · simp [hk]
  cases i with
  | zero => omega
  | succ i =>
    cases i with
    | zero => omega
    | succ i =>
      cases i with
      | zero => exact ⟨.S2,(mem_legalTypes _ _).mpr
          ((has_step_iff _ _).mpr hdup),rfl⟩
      | succ k => exact ⟨.Sk k,(mem_legalTypes _ _).mpr
          ((has_step_iff _ _).mpr hdup),rfl⟩

theorem four_split_path {b : Board} (h : 4≤b.count 1) :
    ∃ c d e, Step b .C1 c ∧ Step c .C1 d ∧ Step d .S2 e := by
  have h1 := next_step (C1_legal (b:=b) (by omega))
  have ho := step_ones h1
  have h2 := next_step (C1_legal (b:=next b .C1) (by omega))
  have ht := two_C1_twos h1 h2
  have hm : .S2 ∈ legalTypes (next (next b .C1) .C1) := by
    apply (mem_legalTypes _ _).mpr
    apply (has_step_iff _ _).mpr
    apply Multiset.le_iff_count.mpr
    intro i
    by_cases hi : i=2
    · subst i; simpa [input] using ht
    · simp [input,hi]
  exact ⟨_,_,_,h1,h2,next_step hm⟩

theorem reachable_split_path {N n : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) (hn : 1 ≤ n) (hN : N<F (n+1)) (hh : n+2<b.card) :
    ∃ v c, Executes b v c ∧ 1≤v.length ∧ v.length≤3 ∧ HasSplit v := by
  have hv : value b < F (n+1) := by rw [← executes_value hu,initial_value]; exact hN
  rcases higher_duplicate_or_four hn (executes_positive hu (initial_positive N)) hv hh with hd | hf
  · obtain ⟨i,hi,hc⟩ := hd
    obtain ⟨m,hm,hs⟩ := duplicate_split hi hc
    exact ⟨[m],_,Executes.cons (next_step hm) (Executes.nil _),by simp,by simp,
      m,by simp,hs⟩
  · obtain ⟨c,d,e,h1,h2,h3⟩ := four_split_path hf
    exact ⟨[.C1,.C1,.S2],e,Executes.cons h1 (Executes.cons h2
      (Executes.cons h3 (Executes.nil _))),by simp,by simp,.S2,by simp,rfl⟩

theorem short_execution_lower {N n : ℕ} {u v : List Move} {b c : Board}
    (hu : Executes (initial N) u b) (hn : 1≤n) (hN : N<F (n+1))
    (hv : Executes b v c) (hl : v.length≤3) :
    blockLower n ≤ reciprocalProduct b v := by
  have hz : (0:ℚ) ≤ ((2*n:ℕ):ℚ)⁻¹ := by positivity
  have hone : (((2*n:ℕ):ℚ)⁻¹) ≤ 1 := by
    apply (inv_le_one₀ (by positivity)).mpr
    exact_mod_cast (show 1≤2*n by omega)
  have hpow : ((2*n:ℕ):ℚ)⁻¹ ^ v.length ≤ reciprocalProduct b v := by
    induction hv generalizing u with
    | nil => simp [reciprocalProduct]
    | @cons a d c m vs hs he ih =>
      have hm := (mem_legalTypes _ _).mpr ⟨d,hs⟩
      have hd := step_deterministic (next_step hm) hs
      have hr := ih (executes_append hu (Executes.cons hs (Executes.nil _))) (by simp only [List.length_cons] at hl; omega)
      have hb := branch_reciprocal_lower hm hn (reachable_types_le hu hn hN)
      simp only [reciprocalProduct,ite_eq_left hm,hd,List.length_cons,pow_succ]
      simpa only [mul_comm] using mul_le_mul hb hr (pow_nonneg hz _) (le_trans hz hb)
  exact le_trans (pow_le_pow_of_le_one hz hone hl) hpow

-- The successful cylinder may have length ONE or THREE. Its exact mass is used.
theorem actual_local_split_cylinder {N n : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) (hn : 1≤n) (hN : N<F (n+1))
    (hh : n+2<b.card) :
    ∃ v c, Executes b v c ∧ 1≤v.length ∧ v.length≤3 ∧ HasSplit v ∧
      blockLower n ≤ cylinderMass N (u++v) / cylinderMass N u := by
  obtain ⟨v,c,hv,h1,h3,hs⟩ := reachable_split_path hu hn hN hh
  refine ⟨v,c,hv,h1,h3,hs,?_⟩
  rw [actual_prefix_continuation hu hv]
  exact short_execution_lower hu hn hN hv h3

def SplitSoon (u w : List Move) : Prop := HasSplit ((w.drop u.length).take 3)
noncomputable def splitSoonMass (N : ℕ) (u : List Move) : ℚ := by
  classical
  exact ∑ w ∈ (cylinderDomain N u).filter (SplitSoon u), P N w
noncomputable def noSplitSoonMass (N : ℕ) (u : List Move) : ℚ := by
  classical
  exact ∑ w ∈ (cylinderDomain N u).filter (fun w => ¬ SplitSoon u w), P N w

theorem success_cylinder_subset {N : ℕ} {u v : List Move}
    (hl : v.length ≤ 3) (hs : HasSplit v) :
    cylinderDomain N (u++v) ⊆ (cylinderDomain N u).filter (SplitSoon u) := by
  classical
  intro w hw
  obtain ⟨hw,z,hz⟩ := Finset.mem_filter.mp hw
  subst w
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨hw,by simp [List.append_assoc]⟩
  · dsimp [SplitSoon]
    simp only [List.append_assoc,List.drop_left']
    obtain ⟨m,hm,hs⟩ := hs
    refine ⟨m,?_,hs⟩
    have hp : v.IsPrefix ((v++z).take 3) := by
      have h := (List.prefix_append v z).take 3
      simpa [List.take_of_length_le hl] using h
    exact hp.mem hm

theorem actual_split_within_three {N n : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) (hn : 1≤n) (hN : N<F (n+1))
    (hh : n+2<b.card) :
    blockLower n * cylinderMass N u ≤ splitSoonMass N u := by
  classical
  obtain ⟨v,c,_,_,hl,hs,hp⟩ := actual_local_split_cylinder hu hn hN hh
  have hmul := (le_div_iff₀ (actual_prefix_positive hu)).mp hp
  apply hmul.trans
  exact Finset.sum_le_sum_of_subset_of_nonneg (success_cylinder_subset hl hs)
    (by intro w _ _; exact P_nonneg N w)

theorem actual_no_split_one_block {N n : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) (hn : 1≤n) (hN : N<F (n+1))
    (hh : n+2<b.card) :
    noSplitSoonMass N u ≤ cylinderMass N u * (1-blockLower n) := by
  classical
  have hp := actual_split_within_three hu hn hN hh
  have he : splitSoonMass N u + noSplitSoonMass N u = cylinderMass N u := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  nlinarith

theorem all_combines_tokens {a c : Board} {v : List Move}
    (hv : Executes a v c) (hs : ∀ m ∈ v, ¬ IsSplit m) :
    a.card = c.card + v.length := by
  have he := executes_tokens hv
  have hm : (v.map combine).sum = v.length := by
    clear hv he
    induction v with
    | nil => simp
    | cons m v ih =>
      have h := hs m (by simp)
      have hc : combine m = 1 := by cases m <;> simp_all [IsSplit,combine]
      simp only [List.map_cons,List.sum_cons,List.length_cons,hc]
      rw [ih (by intro k hk; exact hs k (by simp [hk]))]
      omega
  rwa [hm] at he

-- Position is deterministic. No probability or stopping-time assertion here.
theorem long_combine_suffix_high {b c : Board} {v : List Move} {n q j : ℕ}
    (hv : Executes b v c) (hs : ∀ m ∈ v, ¬ IsSplit m)
    (hl : 3*q+n+3 < v.length) (hj : j≤q) :
    ∃ d, Executes b (v.take (3*j)) d ∧ n+2<d.card := by
  obtain ⟨d,hd,hr⟩ := executes_split (u:=v.take (3*j)) (v:=v.drop (3*j))
    (by simpa using hv)
  have ht := all_combines_tokens hr (by intro m hm; exact hs m (List.mem_of_mem_drop hm))
  have hlen : (v.drop (3*j)).length = v.length-3*j := List.length_drop
  exact ⟨d,hd,by omega⟩
end LiteralGame
