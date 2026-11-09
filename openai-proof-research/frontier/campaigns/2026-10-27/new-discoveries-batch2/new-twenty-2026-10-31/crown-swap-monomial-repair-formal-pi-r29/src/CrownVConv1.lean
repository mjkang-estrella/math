import CrownVCutBridge

/-!
Converse-classification tools.  `cutWitness` extracts the two `univ \ T`-neighbors
of a cut vertex promised by `vcut_witness`.  A nonconnected pair of same-side
vertices has no common opposite-side neighbor in `D` (one would be a 2-path);
this is the only constraint used from `¬ SameC`.  `sameC_refuteX`/`sameC_refuteY`
are the four-step rerouting paths that connect two same-side vertices when two
opposite-side survivors and a third index are available.
-/

namespace CrownV

variable {n : ℕ}

/-- `t ∈ T` with `Cutset T` and `T ≠ ∅` has two `(univ \ T)`-neighbors that are
not connected inside `univ \ T`. -/
theorem cutWitness {T : Finset (V n)} {t : V n} (hT : Cutset T) (htT : t ∈ T)
    (hne : T ≠ ∅) :
    ∃ b c : V n, b ∈ (Finset.univ : Finset (V n)) \ T ∧ c ∈ Finset.univ \ T ∧
      cadj t b ∧ cadj t c ∧ ¬ SameC (Finset.univ \ T) b c := by
  rcases hT with hE | hall
  · exact absurd hE hne
  · exact (vcut_witness (D := Finset.univ \ T) (t := t)
      (fun h => absurd htT (Finset.mem_sdiff.1 h).2)).1 (hall t htT)

/-- A `cadj` edge out of an X vertex lands on a Y vertex. -/
theorem sideY_of_cadj_inl {i : Fin n} {v : V n} (h : cadj (Sum.inl i) v) : sideY v := by
  rcases h.2 with ⟨_, hs⟩ | ⟨hs, _⟩
  · exact hs
  · have h1 : isX (Sum.inl i) = false := hs
    rw [isX_inl] at h1
    exact absurd h1 (by decide)

/-- A `cadj` edge out of a Y vertex lands on an X vertex. -/
theorem sideX_of_cadj_inr {j : Fin n} {v : V n} (h : cadj (Sum.inr j) v) : sideX v := by
  rcases h.2 with ⟨h1, _⟩ | ⟨_, hs⟩
  · have h2 : isX (Sum.inr j) = true := h1
    rw [isX_inr] at h2
    exact absurd h2 (by decide)
  · exact hs

/-- A nonconnected Y pair has no common X neighbor: any `X` survivor has the
index of one of the pair. -/
theorem notSameC_Xcommon {D : Finset (V n)} {k m : Fin n}
    (hkD : Sum.inr k ∈ D) (hmD : Sum.inr m ∈ D)
    (hdis : ¬ SameC D (Sum.inr k) (Sum.inr m)) {l : Fin n} (hl : Sum.inl l ∈ D) :
    l = k ∨ l = m := by
  rcases eq_or_ne l k with e1 | e1
  · exact Or.inl e1
  rcases eq_or_ne l m with e2 | e2
  · exact Or.inr e2
  refine absurd ?_ hdis
  have f1 : SEdge D (Sum.inr k) (Sum.inl l) := ⟨hkD, hl, cadj_inr_inl.2 e1⟩
  have f2 : SEdge D (Sum.inl l) (Sum.inr m) := ⟨hl, hmD, cadj_inl_inr.2 e2⟩
  exact (SameC.single f1).tail f2

/-- A nonconnected X pair has no common Y neighbor: any `Y` survivor has the
index of one of the pair. -/
theorem notSameC_Ycommon {D : Finset (V n)} {k m : Fin n}
    (hkD : Sum.inl k ∈ D) (hmD : Sum.inl m ∈ D)
    (hdis : ¬ SameC D (Sum.inl k) (Sum.inl m)) {l : Fin n} (hl : Sum.inr l ∈ D) :
    l = k ∨ l = m := by
  rcases eq_or_ne l k with e1 | e1
  · exact Or.inl e1
  rcases eq_or_ne l m with e2 | e2
  · exact Or.inr e2
  refine absurd ?_ hdis
  have f1 : SEdge D (Sum.inl k) (Sum.inr l) := ⟨hkD, hl, cadj_inl_inr.2 (Ne.symm e1)⟩
  have f2 : SEdge D (Sum.inr l) (Sum.inl m) := ⟨hl, hmD, cadj_inr_inl.2 (Ne.symm e2)⟩
  exact (SameC.single f1).tail f2

/-- A third index distinct from two distinct given ones (here `n ≥ 3`). -/
theorem exists_third {u v : Fin n} (_huv : u ≠ v) (hn : 3 ≤ n) :
    ∃ r : Fin n, r ≠ u ∧ r ≠ v := by
  by_contra hno
  have hall : ∀ r : Fin n, r = u ∨ r = v := by
    intro r
    by_contra hr
    exact hno ⟨r, fun e => hr (Or.inl e), fun e => hr (Or.inr e)⟩
  have hsub : (Finset.univ : Finset (Fin n)) ⊆
      insert u (insert v (∅ : Finset (Fin n))) := by
    intro r _
    rcases hall r with e | e
    · rw [e]; exact Finset.mem_insert_self u _
    · rw [e]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have h1 : (Finset.univ : Finset (Fin n)).card ≤
      (insert u (insert v (∅ : Finset (Fin n)))).card := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le u (insert v (∅ : Finset (Fin n)))
  have h3 := Finset.card_insert_le v (∅ : Finset (Fin n))
  have h4 : (∅ : Finset (Fin n)).card = 0 := rfl
  have h5 : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  omega

/-- With two X survivors of distinct indices and all Y present, any Y pair is
connected: `b k - a m - b r - a k - b m`. -/
theorem sameC_refuteX {D : Finset (V n)} {k m : Fin n} (hkm : k ≠ m)
    (hkD : Sum.inl k ∈ D) (hmD : Sum.inl m ∈ D) (hY : ∀ j : Fin n, Sum.inr j ∈ D)
    (hn : 4 ≤ n) : SameC D (Sum.inr k) (Sum.inr m) := by
  obtain ⟨r, hrk, hrm⟩ := exists_third hkm (by omega)
  have e1 : SEdge D (Sum.inr k) (Sum.inl m) := ⟨hY k, hmD, cadj_inr_inl.2 (Ne.symm hkm)⟩
  have e2 : SEdge D (Sum.inl m) (Sum.inr r) := ⟨hmD, hY r, cadj_inl_inr.2 (Ne.symm hrm)⟩
  have e3 : SEdge D (Sum.inr r) (Sum.inl k) := ⟨hY r, hkD, cadj_inr_inl.2 (Ne.symm hrk)⟩
  have e4 : SEdge D (Sum.inl k) (Sum.inr m) := ⟨hkD, hY m, cadj_inl_inr.2 hkm⟩
  exact (((SameC.single e1).tail e2).tail e3).tail e4

/-- With two Y survivors of distinct indices and all X present, any X pair is
connected: `a k - b m - a r - b k - a m`. -/
theorem sameC_refuteY {D : Finset (V n)} {k m : Fin n} (hkm : k ≠ m)
    (hkD : Sum.inr k ∈ D) (hmD : Sum.inr m ∈ D) (hX : ∀ l : Fin n, Sum.inl l ∈ D)
    (hn : 4 ≤ n) : SameC D (Sum.inl k) (Sum.inl m) := by
  obtain ⟨r, hrk, hrm⟩ := exists_third hkm (by omega)
  have e1 : SEdge D (Sum.inl k) (Sum.inr m) := ⟨hX k, hmD, cadj_inl_inr.2 hkm⟩
  have e2 : SEdge D (Sum.inr m) (Sum.inl r) := ⟨hmD, hX r, cadj_inr_inl.2 hrm⟩
  have e3 : SEdge D (Sum.inl r) (Sum.inr k) := ⟨hX r, hkD, cadj_inl_inr.2 hrk⟩
  have e4 : SEdge D (Sum.inr k) (Sum.inl m) := ⟨hkD, hX m, cadj_inr_inl.2 (Ne.symm hkm)⟩
  exact (((SameC.single e1).tail e2).tail e3).tail e4

end CrownV
