import CrownVCutBridge
import CrownVSide
import CrownVFamCutA

/-!
r10 wave 2: the mixed families are cut sets, and every valid family is one.

`mix i j` (with `i ≠ j`) has cut set the complement of the four kept vertices
`mixKeep i j`.  For a cut vertex `t ∉ mixKeep i j` (an `a_k` or `b_k` with
`k ∉ {i, j}`), the two kept vertices of the opposite side are joined through
`t`, while inside `mixKeep i j` each opposite-side kept vertex reaches only
its partner: the two-element block `{t's partner set}` is
`sameC_mem_of_closed`-closed, and the other kept vertex is outside it.

`FamValid` collects the valid families; `cutsetFam_of_valid` combines waves 1
and 2 for every valid family at `4 ≤ n`.  No `sorry`, no new axioms.
-/

namespace CrownV

variable {n : ℕ}

/-! ### Complement-of-complement and mixKeep membership -/

/-- Membership in `univ \ (univ \ K)` is membership in `K`. -/
theorem mem_sdiff_univ_sdiff {K : Finset (V n)} {x : V n} :
    x ∈ Finset.univ \ (Finset.univ \ K) ↔ x ∈ K := by
  constructor
  · intro h
    by_contra hx
    exact (Finset.mem_sdiff.1 h).2 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx⟩)
  · intro h
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h' => (Finset.mem_sdiff.1 h').2 h⟩

/-- An `a_m` in `mixKeep i j` has index `i` or `j`. -/
theorem inl_idx_mixKeep {m i j : Fin n} (h : Sum.inl m ∈ mixKeep i j) :
    m = i ∨ m = j := by
  rcases Finset.mem_insert.1 h with h' | h'
  · exact Or.inl (Sum.inl.inj h')
  · rcases Finset.mem_insert.1 h' with h' | h'
    · exact Or.inr (Sum.inl.inj h')
    · exfalso
      rcases Finset.mem_insert.1 h' with h' | h'
      · exact inl_ne_inr h'
      · rcases Finset.mem_insert.1 h' with h' | h'
        · exact inl_ne_inr h'
        · exact Finset.notMem_empty _ h'

/-- A `b_m` in `mixKeep i j` has index `i` or `j`. -/
theorem inr_idx_mixKeep {m i j : Fin n} (h : Sum.inr m ∈ mixKeep i j) :
    m = i ∨ m = j := by
  rcases Finset.mem_insert.1 h with h' | h'
  · exfalso; exact inl_ne_inr h'.symm
  · rcases Finset.mem_insert.1 h' with h' | h'
    · exfalso; exact inl_ne_inr h'.symm
    · rcases Finset.mem_insert.1 h' with h' | h'
      · exact Or.inl (Sum.inr.inj h')
      · rcases Finset.mem_insert.1 h' with h' | h'
        · exact Or.inr (Sum.inr.inj h')
        · exact (Finset.notMem_empty _ h').elim

/-- An `a_a` with `a = i ∨ a = j` lies in `mixKeep i j`. -/
theorem inl_mixKeep_mem {a i j : Fin n} (h : a = i ∨ a = j) :
    Sum.inl a ∈ mixKeep i j := by
  rcases h with hh | hh
  · rw [hh]; exact Finset.mem_insert.2 (Or.inl rfl)
  · rw [hh]; exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inl rfl)))

/-- A `b_a` with `a = i ∨ a = j` lies in `mixKeep i j`. -/
theorem inr_mixKeep_mem {a i j : Fin n} (h : a = i ∨ a = j) :
    Sum.inr a ∈ mixKeep i j := by
  rcases h with hh | hh
  · rw [hh]
    exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inr
      (Finset.mem_insert.2 (Or.inl rfl)))))
  · rw [hh]
    exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inr
      (Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inl rfl)))))))

/-! ### The mixed family -/

theorem cutsetFam_mix {i j : Fin n} (hne : i ≠ j) : Cutset (famCut n (Fam.mix i j)) := by
  rw [famCut_mix]
  refine Or.inr fun t ht => ?_
  cases t with
  | inl k =>
    have hK : Sum.inl k ∉ mixKeep i j := (Finset.mem_sdiff.1 ht).2
    have hki : k ≠ i := by
      intro hh
      refine hK ?_
      rw [hh]
      exact inl_mixKeep_mem (Or.inl rfl)
    have hkj : k ≠ j := by
      intro hh
      refine hK ?_
      rw [hh]
      exact inl_mixKeep_mem (Or.inr rfl)
    have hxS : Sum.inr i ∈ Finset.univ \ (Finset.univ \ mixKeep i j) :=
      mem_sdiff_univ_sdiff.2 (inr_mixKeep_mem (Or.inl rfl))
    have hyS : Sum.inr j ∈ Finset.univ \ (Finset.univ \ mixKeep i j) :=
      mem_sdiff_univ_sdiff.2 (inr_mixKeep_mem (Or.inr rfl))
    have e1 : SEdge (insert (Sum.inl k) (Finset.univ \ (Finset.univ \ mixKeep i j)))
        (Sum.inr i) (Sum.inl k) :=
      ⟨Finset.mem_insert_of_mem hxS, Finset.mem_insert_self (Sum.inl k) _,
        cadj_inr_inl.2 hki⟩
    have e2 : SEdge (insert (Sum.inl k) (Finset.univ \ (Finset.univ \ mixKeep i j)))
        (Sum.inl k) (Sum.inr j) :=
      ⟨Finset.mem_insert_self (Sum.inl k) _, Finset.mem_insert_of_mem hyS,
        cadj_inl_inr.2 hkj⟩
    refine ⟨Sum.inr i, Sum.inr j, hxS, hyS, SameC.two e1 e2, ?_⟩
    intro hcon
    have hcl : ∀ a ∈ insert (Sum.inl j) ({Sum.inr i} : Finset (V n)), ∀ b ∈ Finset.univ \ (Finset.univ \ mixKeep i j),
        cadj a b → b ∈ insert (Sum.inl j) ({Sum.inr i} : Finset (V n)) := by
      intro a ha b hb hc
      have hbK : b ∈ mixKeep i j := mem_sdiff_univ_sdiff.1 hb
      obtain ⟨hneV, hor⟩ := hc
      rcases Finset.mem_insert.1 ha with he | he'
      · subst he
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have h2' : isX b = false := h2
          obtain ⟨m, hmB⟩ := inr_of_isY h2'
          subst hmB
          have hM := inr_idx_mixKeep hbK
          rcases hM with hm | hm
          · rw [hm]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            -- b = inr i after rewrites? see below
          · have heq : vidx (Sum.inl j) = vidx (Sum.inr m) := by
              rw [hm]; exact vidx_inl_eq_inr
            exact absurd heq hneV
        · exact (not_sideY_inl h1).elim
      · have heI : a = Sum.inr i := Finset.mem_singleton.1 he'
        subst heI
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact (not_sideX_inr h1).elim
        · have h2' : isX b = true := h2
          obtain ⟨m, hmB⟩ := inl_of_isX h2'
          subst hmB
          have hM := inl_idx_mixKeep hbK
          rcases hM with hm | hm
          · have heq : vidx (Sum.inr i) = vidx (Sum.inl m) := by
              rw [hm]; exact vidx_inl_eq_inr.symm
            exact absurd heq hneV
          · rw [hm]
            exact Finset.mem_insert.2 (Or.inl rfl)
    have hyD : Sum.inr j ∈ insert (Sum.inl j) ({Sum.inr i} : Finset (V n)) :=
      sameC_mem_of_closed (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 rfl))) hcl
        (Sum.inr j) hcon
    rcases Finset.mem_insert.1 hyD with he | he
    · exact inl_ne_inr he.symm
    · exact hne (Sum.inr.inj (Finset.mem_singleton.1 he)).symm
  | inr k =>
    have hK : Sum.inr k ∉ mixKeep i j := (Finset.mem_sdiff.1 ht).2
    have hki : k ≠ i := by
      intro hh
      refine hK ?_
      rw [hh]
      exact inr_mixKeep_mem (Or.inl rfl)
    have hkj : k ≠ j := by
      intro hh
      refine hK ?_
      rw [hh]
      exact inr_mixKeep_mem (Or.inr rfl)
    have hxS : Sum.inl i ∈ Finset.univ \ (Finset.univ \ mixKeep i j) :=
      mem_sdiff_univ_sdiff.2 (inl_mixKeep_mem (Or.inl rfl))
    have hyS : Sum.inl j ∈ Finset.univ \ (Finset.univ \ mixKeep i j) :=
      mem_sdiff_univ_sdiff.2 (inl_mixKeep_mem (Or.inr rfl))
    have e1 : SEdge (insert (Sum.inr k) (Finset.univ \ (Finset.univ \ mixKeep i j)))
        (Sum.inl i) (Sum.inr k) :=
      ⟨Finset.mem_insert_of_mem hxS, Finset.mem_insert_self (Sum.inr k) _,
        cadj_inl_inr.2 (Ne.symm hki)⟩
    have e2 : SEdge (insert (Sum.inr k) (Finset.univ \ (Finset.univ \ mixKeep i j)))
        (Sum.inr k) (Sum.inl j) :=
      ⟨Finset.mem_insert_self (Sum.inr k) _, Finset.mem_insert_of_mem hyS,
        cadj_inr_inl.2 (Ne.symm hkj)⟩
    refine ⟨Sum.inl i, Sum.inl j, hxS, hyS, SameC.two e1 e2, ?_⟩
    intro hcon
    have hcl : ∀ a ∈ insert (Sum.inr j) ({Sum.inl i} : Finset (V n)), ∀ b ∈ Finset.univ \ (Finset.univ \ mixKeep i j),
        cadj a b → b ∈ insert (Sum.inr j) ({Sum.inl i} : Finset (V n)) := by
      intro a ha b hb hc
      have hbK : b ∈ mixKeep i j := mem_sdiff_univ_sdiff.1 hb
      obtain ⟨hneV, hor⟩ := hc
      rcases Finset.mem_insert.1 ha with he | he'
      · subst he
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact (not_sideX_inr h1).elim
        · have h2' : isX b = true := h2
          obtain ⟨m, hmB⟩ := inl_of_isX h2'
          subst hmB
          have hM := inl_idx_mixKeep hbK
          rcases hM with hm | hm
          · rw [hm]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · have heq : vidx (Sum.inr j) = vidx (Sum.inl m) := by
              rw [hm]; exact vidx_inl_eq_inr.symm
            exact absurd heq hneV
      · have heI : a = Sum.inl i := Finset.mem_singleton.1 he'
        subst heI
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have h2' : isX b = false := h2
          obtain ⟨m, hmB⟩ := inr_of_isY h2'
          subst hmB
          have hM := inr_idx_mixKeep hbK
          rcases hM with hm | hm
          · have heq : vidx (Sum.inl i) = vidx (Sum.inr m) := by
              rw [hm]; exact vidx_inl_eq_inr
            exact absurd heq hneV
          · rw [hm]
            exact Finset.mem_insert.2 (Or.inl rfl)
        · exact (not_sideY_inl h1).elim
    have hyD : Sum.inl j ∈ insert (Sum.inr j) ({Sum.inl i} : Finset (V n)) :=
      sameC_mem_of_closed (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 rfl))) hcl
        (Sum.inl j) hcon
    rcases Finset.mem_insert.1 hyD with he | he
    · exact inl_ne_inr he
    · exact hne (Sum.inl.inj (Finset.mem_singleton.1 he)).symm

/-! ### Validity and the combined statement -/

/-- The valid families: every non-mixed constructor, and `mix i j` only for
`i ≠ j`. -/
def FamValid (n : ℕ) : Fam n → Prop
  | .zero => True
  | .fullX => True
  | .fullY => True
  | .delX _ => True
  | .delY _ => True
  | .mix i j => i ≠ j

/-- Every valid family cut is an actual cut set, for all `4 ≤ n`. -/
theorem cutsetFam_of_valid (hn : 4 ≤ n) (f : Fam n) (hf : FamValid n f) :
    Cutset (famCut n f) := by
  cases f with
  | zero => exact cutsetFam_zero
  | fullX => exact cutsetFam_fullX (by omega)
  | fullY => exact cutsetFam_fullY (by omega)
  | delX i => exact cutsetFam_delX (by omega) i
  | delY i => exact cutsetFam_delY (by omega) i
  | mix i j => exact cutsetFam_mix hf

end CrownV
