import Marks
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame
theorem F_le_value {b : Board} {i : ℕ} (hi : i ∈ b) : F i ≤ value b := by
  induction b using Multiset.induction_on with
  | empty => simp at hi
  | @cons k b ih =>
    simp only [Multiset.mem_cons] at hi
    simp only [value,Multiset.map_cons,Multiset.sum_cons]
    rcases hi with rfl | hi
    · omega
    · have h := ih hi; dsimp [value] at h; omega

theorem index_bound {b : Board} {n i : ℕ} (hv : value b < F (n+1))
    (hi : i ∈ b) : i ≤ n := by
  have h := F_le_value hi
  by_contra hn
  have hf : F (n+1) ≤ F i := Nat.fib_mono (by omega)
  omega

noncomputable def boundedTypes (n : ℕ) : Finset Move :=
  { .C1,.S2 } ∪ (Finset.range (n-1)).image Move.Ck ∪
    (Finset.range (n-2)).image Move.Sk

theorem legalTypes_bounded {b : Board} {n : ℕ} (hv : value b < F (n+1)) :
    legalTypes b ⊆ boundedTypes n := by
  classical
  intro m hm
  have hl := (has_step_iff b m).mp ((mem_legalTypes b m).mp hm)
  cases m with
  | C1 => simp [boundedTypes]
  | S2 => simp [boundedTypes]
  | Ck k =>
    have hi : k+2 ∈ b := Multiset.mem_of_le hl (by simp [input])
    have hk := index_bound hv hi
    simp only [boundedTypes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image,Finset.mem_range]
    exact Or.inl (Or.inr ⟨k,by omega,rfl⟩)
  | Sk k =>
    have hi : k+3 ∈ b := Multiset.mem_of_le hl (by simp [input])
    have hk := index_bound hv hi
    simp only [boundedTypes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image,Finset.mem_range]
    exact Or.inr ⟨k,by omega,rfl⟩

theorem legalTypes_le_two_n {b : Board} {n : ℕ} (hn : 1 ≤ n)
    (hv : value b < F (n+1)) : (legalTypes b).card ≤ 2*n := by
  classical
  have h := Finset.card_le_card (legalTypes_bounded hv)
  have h1 := Finset.card_union_le ({Move.C1,Move.S2} ∪
    (Finset.range (n-1)).image Move.Ck) ((Finset.range (n-2)).image Move.Sk)
  have h2 := Finset.card_union_le ({Move.C1,Move.S2} : Finset Move)
    ((Finset.range (n-1)).image Move.Ck)
  have h3 := Finset.card_image_le (s:=Finset.range (n-1)) (f:=Move.Ck)
  have h4 := Finset.card_image_le (s:=Finset.range (n-2)) (f:=Move.Sk)
  simp only [Finset.card_range] at h3 h4
  have hc : ({Move.C1,Move.S2} : Finset Move).card = 2 := by decide
  dsimp [boundedTypes] at h
  omega

theorem reachable_types_le {N n : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) (hn : 1 ≤ n) (hN : N < F (n+1)) :
    (legalTypes b).card ≤ 2*n := by
  apply legalTypes_le_two_n hn
  have hv := executes_value hu
  rw [initial_value] at hv
  omega

theorem input_ones_le (m : Move) : (input m).count 1 ≤ 2 := by
  cases m <;> simp [input,Multiset.count_cons,Multiset.count_singleton]
  split_ifs <;> omega

theorem step_ones {a b : Board} {m : Move} (hs : Step a m b) :
    a.count 1 ≤ b.count 1 + 2 := by
  obtain ⟨r,ha,hb⟩ := hs
  have hi := input_ones_le m
  simp only [ha,hb,Multiset.count_add]
  omega

theorem executes_ones {a b : Board} {u : List Move} (hu : Executes a u b) :
    a.count 1 ≤ b.count 1 + 2*u.length := by
  induction hu with
  | nil => simp
  | cons hs _ ih => have h := step_ones hs; simp only [List.length_cons]; omega

theorem early_block_six {N j : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) (hlen : u.length=3*j) (hj : j<N/6) :
    6 ≤ b.count 1 := by
  have h := executes_ones hu
  simp only [initial,Multiset.count_replicate_self] at h
  omega

theorem C1_legal {b : Board} (h : 2 ≤ b.count 1) : .C1 ∈ legalTypes b := by
  apply (mem_legalTypes b .C1).mpr
  apply (has_step_iff b .C1).mpr
  apply Multiset.le_iff_count.mpr
  intro i
  by_cases hi : i=1
  · subst i; simpa [input] using h
  · simp [input,hi]

theorem six_not_terminal {b : Board} (h : 6 ≤ b.count 1) : ¬ Terminal b := by
  intro ht
  exact ht _ _ (next_step (C1_legal (by omega)))

theorem six_triple {b : Board} (h : 6 ≤ b.count 1) :
    ∃ c d e, Step b .C1 c ∧ Step c .C1 d ∧ Step d C2 e := by
  have hm := C1_legal (b:=b) (by omega)
  have hs := next_step hm
  have hcount := step_ones hs
  have hm' := C1_legal (b:=next b .C1) (by omega)
  have hs' := next_step hm'
  have hcount' := step_ones hs'
  have ht := two_C1_twos hs hs'
  have hlast : C2 ∈ legalTypes (next (next b .C1) .C1) := by
    apply (mem_legalTypes _ _).mpr
    apply (has_step_iff _ _).mpr
    apply Multiset.le_iff_count.mpr
    intro i
    by_cases h1 : i=1
    · subst i; simp [input]; omega
    by_cases h2 : i=2
    · subst i; simp [input]; omega
    simp [input,h1,h2]
  exact ⟨_,_,_,hs,hs',next_step hlast⟩
end LiteralGame
