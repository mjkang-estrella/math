import Assembly
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame

def IsSplit (m : Move) : Prop := combine m = 0
def HasSplit (v : List Move) : Prop := ∃ m ∈ v, IsSplit m

theorem higher_duplicate_or_four {b : Board} {n : ℕ}
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
    (hu : Executes (initial N) u b) (hN : N<F (n+1)) (hh : n+2<b.card) :
    ∃ v c, Executes b v c ∧ 1≤v.length ∧ v.length≤3 ∧ HasSplit v := by
  have hv : value b < F (n+1) := by rw [← executes_value hu,initial_value]; exact hN
  rcases higher_duplicate_or_four (executes_positive hu (initial_positive N)) hv hh with hd | hf
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
  obtain ⟨v,c,hv,h1,h3,hs⟩ := reachable_split_path hu hN hh
  refine ⟨v,c,hv,h1,h3,hs,?_⟩
  rw [actual_prefix_continuation hu hv]
  exact short_execution_lower hu hn hN hv h3
end LiteralGame
