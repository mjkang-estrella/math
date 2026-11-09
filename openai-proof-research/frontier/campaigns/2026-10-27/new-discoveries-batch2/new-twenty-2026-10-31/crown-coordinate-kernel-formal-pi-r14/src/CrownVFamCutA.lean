import CrownVCutBridge
import CrownVSide

/-!
r10 wave 1: the non-mixed valid families are actual cut sets.

For every family in {`zero`, `fullX`, `fullY`, `delX i`, `delY i`} the cut set
`famCut` satisfies paper Definition 2.2 (`Cutset`): it is empty, or each of its
vertices is a cut vertex of the graph induced on `(V ∖ T) ∪ {t}` in the path
form of `CrownVClass`.  Every path witness is a genuine two-edge path through
`t` (`SameC.two`); every nonconnectivity refutation goes through
`sameC_eq_of_forall_not_sEdge` on the actual edge relation, using that the
relevant witness is isolated in the smaller graph.  No `sorry`, no new axioms.

The mixed families `mix i j` and the combined statement over all valid
families are wave 2 (`CrownVFamCutB`).
-/

namespace CrownV

variable {n : ℕ}

/-! ### Index availability -/

private theorem natThird (a b : ℕ) : ∃ c : ℕ, c < 3 ∧ c ≠ a ∧ c ≠ b := by
  by_cases h1 : a = 0
  · by_cases h2 : b = 1
    · exact ⟨2, by omega, by omega, by omega⟩
    · exact ⟨1, by omega, by omega, by omega⟩
  · by_cases h3 : a = 1
    · by_cases h4 : b = 0
      · exact ⟨2, by omega, by omega, by omega⟩
      · exact ⟨0, by omega, by omega, by omega⟩
    · by_cases h5 : b = 0
      · exact ⟨1, by omega, by omega, by omega⟩
      · exact ⟨0, by omega, by omega, by omega⟩

private theorem card_le_two {a b : Fin n} (h : ∀ c : Fin n, c = a ∨ c = b) :
    (Finset.univ : Finset (Fin n)).card ≤ 2 := by
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ insert a ({b} : Finset (Fin n)) := by
    intro c _
    rcases h c with hc | hc
    · exact Finset.mem_insert.2 (Or.inl hc)
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 hc))
  have hcard : (insert a ({b} : Finset (Fin n))).card ≤ 2 := by
    refine (Finset.card_insert_le a ({b} : Finset (Fin n))).trans ?_
    rw [Finset.card_singleton]
  exact (Finset.card_le_card hsub).trans hcard

private theorem card_univ_fin (n : ℕ) : (Finset.univ : Finset (Fin n)).card = n := by
  rw [Finset.card_univ]; exact Fintype.card_fin n

/-- A third index distinct from two given ones (whenever `3 ≤ n`). -/
theorem existsFinThird {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  by_contra hex
  have hex' : ∀ c : Fin n, c = a ∨ c = b := by
    intro c
    by_cases h1 : c = a
    · exact Or.inl h1
    · by_cases h2 : c = b
      · exact Or.inr h2
      · exact absurd ⟨c, h1, h2⟩ hex
  have h2 := card_le_two hex'
  have h3 := card_univ_fin n
  omega

/-- Two indices, distinct, both distinct from `a` (whenever `3 ≤ n`). -/
theorem existsFinApart {n : ℕ} (hn : 3 ≤ n) (a : Fin n) :
    ∃ c d : Fin n, c ≠ d ∧ c ≠ a ∧ d ≠ a := by
  have seed : ∃ c : Fin n, c ≠ a := by
    by_contra hs
    have hall : ∀ c : Fin n, c = a := by
      intro c
      by_cases h : c = a
      · exact h
      · exact absurd ⟨c, h⟩ hs
    have h1 : (Finset.univ : Finset (Fin n)).card ≤ ({a} : Finset (Fin n)).card :=
      Finset.card_le_card fun c _ => Finset.mem_singleton.2 (hall c)
    have h2 : ({a} : Finset (Fin n)).card = 1 := Finset.card_singleton a
    have h3 := card_univ_fin n
    omega
  obtain ⟨c, hc⟩ := seed
  have key : ∃ d : Fin n, d ≠ a ∧ d ≠ c := by
    by_contra hk
    have hall : ∀ d : Fin n, d = a ∨ d = c := by
      intro d
      by_cases h1 : d = a
      · exact Or.inl h1
      · by_cases h2 : d = c
        · exact Or.inr h2
        · exact absurd ⟨d, h1, h2⟩ hk
    have h2 := card_le_two hall
    have h3 := card_univ_fin n
    omega
  obtain ⟨d, hd1, hd2⟩ := key
  exact ⟨c, d, Ne.symm hd2, hc, hd1⟩

/-! ### Side impossibilities -/

/-- The X-side of a `b`-vertex is false. -/
theorem not_sideX_inr {m : Fin n} : ¬ sideX (Sum.inr m) := by
  intro h
  have h' : isX (Sum.inr m) = true := h
  rw [isX_inr] at h'
  exact absurd h' (by decide)

/-- The Y-side of an `a`-vertex is false. -/
theorem not_sideY_inl {m : Fin n} : ¬ sideY (Sum.inl m) := by
  intro h
  have h' : isX (Sum.inl m) = false := h
  rw [isX_inl] at h'
  exact absurd h' (by decide)

/-- The two `vidx` values of opposite tags at the same index agree. -/
theorem vidx_inl_eq_inr {i : Fin n} : vidx (Sum.inl i) = vidx (Sum.inr i) := by
  rw [vidx_inl, vidx_inr]

/-! ### The empty and full-side families -/

/-- The empty family cut is a cut set. -/
theorem cutsetFam_zero : Cutset (famCut n Fam.zero) := Or.inl (famCut_zero n)

/-- `Xside` (all `a_i` killed) is a cut set. -/
theorem cutsetFam_fullX (hn : 3 ≤ n) : Cutset (famCut n Fam.fullX) := by
  rw [famCut_fullX]
  refine Or.inr fun t ht => ?_
  obtain ⟨k, hk⟩ := inl_of_isX (mem_Xside.1 ht)
  subst hk
  obtain ⟨a, b, hab, hak, hbk⟩ := existsFinApart hn k
  refine ⟨Sum.inr a, Sum.inr b, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, notMem_Xside_of_isY isX_inr⟩
  · exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, notMem_Xside_of_isY isX_inr⟩
  have e1 : SEdge (insert (Sum.inl k) (Finset.univ \ Xside n)) (Sum.inr a) (Sum.inl k) :=
    ⟨Finset.mem_insert_of_mem
      (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, notMem_Xside_of_isY isX_inr⟩),
      Finset.mem_insert_self (Sum.inl k) _, cadj_inr_inl.2 (Ne.symm hak)⟩
  have e2 : SEdge (insert (Sum.inl k) (Finset.univ \ Xside n)) (Sum.inl k) (Sum.inr b) :=
    ⟨Finset.mem_insert_self (Sum.inl k) _,
      Finset.mem_insert_of_mem
        (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, notMem_Xside_of_isY isX_inr⟩),
      cadj_inl_inr.2 (Ne.symm hbk)⟩
  exact SameC.two e1 e2
  · intro hcon
    have hno : ∀ w : V n, ¬ SEdge (Finset.univ \ Xside n) (Sum.inr a) w := by
      intro w hS
      obtain ⟨_, hws, hc⟩ := hS
      obtain ⟨_, hor⟩ := hc
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact not_sideX_inr h1
      · have h2' : isX w = true := h2
        exact absurd (mem_Xside.2 h2') ((Finset.mem_sdiff.1 hws).2)
    have hEq := sameC_eq_of_forall_not_sEdge hno hcon
    exact hab (Sum.inr.inj hEq)

/-- `Yside` (all `b_i` killed) is a cut set. -/
theorem cutsetFam_fullY (hn : 3 ≤ n) : Cutset (famCut n Fam.fullY) := by
  rw [famCut_fullY]
  refine Or.inr fun t ht => ?_
  obtain ⟨k, hk⟩ := inr_of_isY (mem_Yside.1 ht)
  subst hk
  obtain ⟨a, b, hab, hak, hbk⟩ := existsFinApart hn k
  refine ⟨Sum.inl a, Sum.inl b, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, notMem_Yside_of_isX isX_inl⟩
  · exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, notMem_Yside_of_isX isX_inl⟩
  have e1 : SEdge (insert (Sum.inr k) (Finset.univ \ Yside n)) (Sum.inl a) (Sum.inr k) :=
    ⟨Finset.mem_insert_of_mem
      (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, notMem_Yside_of_isX isX_inl⟩),
      Finset.mem_insert_self (Sum.inr k) _, cadj_inl_inr.2 hak⟩
  have e2 : SEdge (insert (Sum.inr k) (Finset.univ \ Yside n)) (Sum.inr k) (Sum.inl b) :=
    ⟨Finset.mem_insert_self (Sum.inr k) _,
      Finset.mem_insert_of_mem
        (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, notMem_Yside_of_isX isX_inl⟩),
      cadj_inr_inl.2 hbk⟩
  exact SameC.two e1 e2
  · intro hcon
    have hno : ∀ w : V n, ¬ SEdge (Finset.univ \ Yside n) (Sum.inl a) w := by
      intro w hS
      obtain ⟨_, hws, hc⟩ := hS
      obtain ⟨_, hor⟩ := hc
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h2' : isX w = false := h2
        exact absurd (mem_Yside.2 h2') ((Finset.mem_sdiff.1 hws).2)
      · exact not_sideY_inl h1
    have hEq := sameC_eq_of_forall_not_sEdge hno hcon
    exact hab (Sum.inl.inj hEq)

/-! ### One survivor deleted from a side -/

/-- `Xside` with `a_i` kept back is a cut set: `b_i` is isolated in the
complement, so no `b`-witness path survives; the deleted `a_i` is the
complement's only `a`. -/
theorem cutsetFam_delX (hn : 3 ≤ n) (i : Fin n) : Cutset (famCut n (Fam.delX i)) := by
  rw [famCut_delX]
  refine Or.inr fun t ht => ?_
  obtain ⟨hne1, htX⟩ := Finset.mem_erase.1 ht
  obtain ⟨k, hk⟩ := inl_of_isX (mem_Xside.1 htX)
  subst hk
  have hki : k ≠ i := fun hh => hne1 (by rw [hh])
  obtain ⟨l, hl1, hl2⟩ := existsFinThird hn i k
  refine ⟨Sum.inr i, Sum.inr l, ?_, ?_, ?_, ?_⟩
  · refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    exact notMem_Xside_of_isY isX_inr (Finset.mem_erase.1 hmem).2
  · refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    exact notMem_Xside_of_isY isX_inr (Finset.mem_erase.1 hmem).2
  have e1 : SEdge (insert (Sum.inl k) (Finset.univ \ (Xside n).erase (Sum.inl i)))
      (Sum.inr i) (Sum.inl k) :=
    ⟨Finset.mem_insert_of_mem
      (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hmem =>
        notMem_Xside_of_isY isX_inr (Finset.mem_erase.1 hmem).2⟩),
      Finset.mem_insert_self (Sum.inl k) _, cadj_inr_inl.2 hki⟩
  have e2 : SEdge (insert (Sum.inl k) (Finset.univ \ (Xside n).erase (Sum.inl i)))
      (Sum.inl k) (Sum.inr l) :=
    ⟨Finset.mem_insert_self (Sum.inl k) _,
      Finset.mem_insert_of_mem
        (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hmem =>
          notMem_Xside_of_isY isX_inr (Finset.mem_erase.1 hmem).2⟩),
      cadj_inl_inr.2 (Ne.symm hl2)⟩
  exact SameC.two e1 e2
  · intro hcon
    have hno : ∀ w : V n,
        ¬ SEdge (Finset.univ \ (Xside n).erase (Sum.inl i)) (Sum.inr i) w := by
      intro w hS
      obtain ⟨_, hws, hc⟩ := hS
      obtain ⟨hneV, hor⟩ := hc
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact not_sideX_inr h1
      · have h2' : isX w = true := h2
        obtain ⟨m, hm⟩ := inl_of_isX h2'
        rw [hm] at hws hneV
        have hXm : Sum.inl m ∈ Xside n := inl_mem_Xside m
        have hmi : m = i := by
          by_contra hmi'
          exact (Finset.mem_sdiff.1 hws).2
            (Finset.mem_erase.2 ⟨fun he => hmi' (Sum.inl.inj he), hXm⟩)
        have heq : vidx (Sum.inl m) = vidx (Sum.inl i) := by rw [hmi]
        exact hneV (vidx_inl_eq_inr.trans heq.symm)
    have hEq := sameC_eq_of_forall_not_sEdge hno hcon
    exact hl1 (Sum.inr.inj hEq).symm

/-- `Yside` with `b_i` kept back is a cut set, mirror of `cutsetFam_delX`. -/
theorem cutsetFam_delY (hn : 3 ≤ n) (i : Fin n) : Cutset (famCut n (Fam.delY i)) := by
  rw [famCut_delY]
  refine Or.inr fun t ht => ?_
  obtain ⟨hne1, htY⟩ := Finset.mem_erase.1 ht
  obtain ⟨k, hk⟩ := inr_of_isY (mem_Yside.1 htY)
  subst hk
  have hki : k ≠ i := fun hh => hne1 (by rw [hh])
  obtain ⟨l, hl1, hl2⟩ := existsFinThird hn i k
  refine ⟨Sum.inl i, Sum.inl l, ?_, ?_, ?_, ?_⟩
  · refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    exact notMem_Yside_of_isX isX_inl (Finset.mem_erase.1 hmem).2
  · refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    exact notMem_Yside_of_isX isX_inl (Finset.mem_erase.1 hmem).2
  have e1 : SEdge (insert (Sum.inr k) (Finset.univ \ (Yside n).erase (Sum.inr i)))
      (Sum.inl i) (Sum.inr k) :=
    ⟨Finset.mem_insert_of_mem
      (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hmem =>
        notMem_Yside_of_isX isX_inl (Finset.mem_erase.1 hmem).2⟩),
      Finset.mem_insert_self (Sum.inr k) _, cadj_inl_inr.2 (Ne.symm hki)⟩
  have e2 : SEdge (insert (Sum.inr k) (Finset.univ \ (Yside n).erase (Sum.inr i)))
      (Sum.inr k) (Sum.inl l) :=
    ⟨Finset.mem_insert_self (Sum.inr k) _,
      Finset.mem_insert_of_mem
        (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hmem =>
          notMem_Yside_of_isX isX_inl (Finset.mem_erase.1 hmem).2⟩),
      cadj_inr_inl.2 hl2⟩
  exact SameC.two e1 e2
  · intro hcon
    have hno : ∀ w : V n,
        ¬ SEdge (Finset.univ \ (Yside n).erase (Sum.inr i)) (Sum.inl i) w := by
      intro w hS
      obtain ⟨_, hws, hc⟩ := hS
      obtain ⟨hneV, hor⟩ := hc
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h2' : isX w = false := h2
        obtain ⟨m, hm⟩ := inr_of_isY h2'
        rw [hm] at hws hneV
        have hYm : Sum.inr m ∈ Yside n := inr_mem_Yside m
        have hmi : m = i := by
          by_contra hmi'
          exact (Finset.mem_sdiff.1 hws).2
            (Finset.mem_erase.2 ⟨fun he => hmi' (Sum.inr.inj he), hYm⟩)
        have heq : vidx (Sum.inr m) = vidx (Sum.inr i) := by rw [hmi]
        exact hneV (vidx_inl_eq_inr.trans heq.symm)
      · exact not_sideY_inl h1
    have hEq := sameC_eq_of_forall_not_sEdge hno hcon
    exact hl1 (Sum.inl.inj hEq).symm

end CrownV
