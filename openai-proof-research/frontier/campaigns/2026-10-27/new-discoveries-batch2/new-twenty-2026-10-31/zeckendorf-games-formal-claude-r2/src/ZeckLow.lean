/-
  Part (b) of MathDB 347063: the split at the pool, low moves, the insertion cascade.
-/
import ZeckWindow

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

/-- `S_p` for `p = q + 2 ≥ 4`. -/
lemma Tr_Sp {z : Pos} {q : ℕ} (hq2 : 2 ≤ q) (hq : q % 2 = 0) (hz : Zk z q) (c1 c3 : ℕ) :
    Tr (z + W q 0 (c1 + 2) 0 c3 0 0) 1 1 (z + single q 1 + W q 0 c1 1 c3 0 0) := by
  have hL := hz.lowQ
  have hl : legalSplit (z + W q 0 (c1 + 2) 0 c3 0 0) (q + 2) := by
    refine ⟨by omega, ?_⟩
    rw [Finsupp.add_apply, W_at2]; omega
  have hmin : ∀ k < q + 2, ¬ legalSplit (z + W q 0 (c1 + 2) 0 c3 0 0) k := by
    rintro k hk ⟨_, h2⟩
    rw [Finsupp.add_apply] at h2
    by_cases hk' : k ≤ q
    · rw [W_below hk'] at h2
      have := hz.one k
      omega
    · have e : k = q + 1 := by omega
      subst e
      rw [W_at1, hz.top _ (by omega)] at h2
      omega
  refine Tr.ofSplit (not_A1 hL (Or.inl (by omega))) (not_cons_quiet hL _ _ _) hl hmin ?_ ?_
  · have e0 : doSplit (z + W q 0 (c1 + 2) 0 c3 0 0) (q + 2)
        = doSplitG (z + W q 0 (c1 + 2) 0 c3 0 0) (q + 2) := by
      have h1 : q + 2 ≠ 1 := by omega
      have h2 : q + 2 ≠ 2 := by omega
      simp [doSplit, h1, h2, show q ≠ 0 by omega]
    have e : z + W q 0 (c1 + 2) 0 c3 0 0 = (z + W q 0 c1 0 c3 0 0) + single (q + 2) 2 := by
      simp only [W, Finsupp.single_add]
      abel
    rw [e0, e, doSplitG_add (z + W q 0 c1 0 c3 0 0) (i := q + 2) (i' := q) rfl (by omega)]
    simp only [W, Finsupp.single_add, show q + 2 + 1 = q + 3 from rfl, Finsupp.single_zero,
      add_zero]
    abel
  · have hd : d q + d (q + 3) = 2 * d (q + 2) + 1 := by
      have := d_split (q := q + 2) (by omega) (by omega)
      simpa using this
    simp only [D_add, D_W, D_single]
    nlinarith [hd]

/-- `S_2`, the first split of level `p = 2`. -/
lemma Tr_S2 (c1 c3 : ℕ) :
    Tr (0 + W 0 0 (c1 + 2) 0 c3 0 0) 1 1 (0 + W 0 1 c1 1 c3 0 0) := by
  have hL : LowQ (0 : Pos) 0 := ⟨fun i => Or.inl rfl, by simp, by simp, fun _ _ => rfl⟩
  have h2 : W 0 0 (c1 + 2) 0 c3 0 0 2 = c1 + 2 := by
    rw [W_apply]; split_ifs <;> omega
  have h1 : W 0 0 (c1 + 2) 0 c3 0 0 1 = 0 := by
    rw [W_apply]; split_ifs <;> omega
  have hl : legalSplit (0 + W 0 0 (c1 + 2) 0 c3 0 0) 2 := by
    refine ⟨le_refl 2, ?_⟩
    rw [Finsupp.add_apply, h2]; simp
  have hmin : ∀ k < 2, ¬ legalSplit (0 + W 0 0 (c1 + 2) 0 c3 0 0) k := by
    rintro k hk ⟨h2', _⟩
    omega
  refine Tr.ofSplit (not_A1 hL (Or.inr (by omega))) (not_cons_quiet hL _ _ _) hl hmin ?_ ?_
  · have e0 : doSplit (0 + W 0 0 (c1 + 2) 0 c3 0 0) 2
        = doSplit2 (0 + W 0 0 (c1 + 2) 0 c3 0 0) := by simp [doSplit]
    have e : (0 : Pos) + W 0 0 (c1 + 2) 0 c3 0 0 = W 0 0 c1 0 c3 0 0 + single 2 2 := by
      simp only [W, zero_add, Finsupp.single_add]
      abel
    rw [e0, e, doSplit2_add]
    simp only [W, zero_add, Finsupp.single_add, Finsupp.single_zero, add_zero]
    abel
  · have hd := d_split2
    simp only [D_add, D_W, D_single, zero_add]
    nlinarith [hd]

/-- `A1`, the first phase. -/
lemma Tr_A1 (c0 c1 c2 c3 c4 c5 : ℕ) :
    Tr (W 0 (c0 + 2) c1 c2 c3 c4 c5) 1 0 (W 0 c0 (c1 + 1) c2 c3 c4 c5) := by
  have h1 : W 0 (c0 + 2) c1 c2 c3 c4 c5 1 = c0 + 2 := by
    rw [W_apply]; split_ifs <;> omega
  have hA : legalA1 (W 0 (c0 + 2) c1 c2 c3 c4 c5) := by
    show 2 ≤ W 0 (c0 + 2) c1 c2 c3 c4 c5 1
    rw [h1]; omega
  refine Tr.ofA1 hA ?_ ?_
  · have e : W 0 (c0 + 2) c1 c2 c3 c4 c5 = W 0 c0 c1 c2 c3 c4 c5 + single 1 2 := by
      simp only [W, zero_add, Finsupp.single_add]
      abel
    rw [e, doA1_add]
    simp only [W, zero_add, Finsupp.single_add]
    abel
  · have d1 : d 1 = 0 := by decide
    have d2 : d 2 = 0 := by decide
    simp only [D_W, zero_add, d1, d2]
    ring

/-! ### Low moves -/

/-- A combine in the low state. -/
lemma Tr_low_cons {z H : Pos} {q : ℕ} (hq2 : 2 ≤ q) (hq : q % 2 = 0) (hz : Zk z q)
    (h1 : z (q - 1) = 1) (hH : ∀ i, i ≤ q → H i = 0) :
    Tr (z + single q 1 + H) 1 1 (z.update (q - 1) 0 + single (q + 1) 1 + H) := by
  have ev : ∀ x, (z + single q 1 + H : Pos) x = z x + (if q = x then 1 else 0) + H x := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  have hA : ¬ legalA1 (z + single q 1 + H) := by
    intro h
    have h' : 2 ≤ (z + single q 1 + H : Pos) 1 := h
    rw [ev, hH 1 (by omega)] at h'
    have h3 := hz.one 1
    have hne : ¬ q = 1 := by omega
    simp [hne] at h'
    omega
  have hl : legalCons (z + single q 1 + H) q := by
    refine ⟨hq2, ?_, ?_⟩
    · rw [ev, h1]; omega
    · rw [ev]
      simp
      omega
  have hmin : ∀ j < q, ¬ legalCons (z + single q 1 + H) j := by
    rintro j hj ⟨hj2, h3, h4⟩
    rw [ev, hH (j - 1) (by omega)] at h3
    rw [ev, hH j (by omega)] at h4
    have hadj := hz.adj (j - 1)
    rw [show j - 1 + 1 = j by omega] at hadj
    have hne1 : ¬ q = j - 1 := by omega
    have hne2 : ¬ q = j := by omega
    simp [hne1] at h3
    simp [hne2] at h4
    omega
  refine Tr.ofCons hA hl hmin ?_ ?_
  · have e : z + single q 1 + H
        = (z.update (q - 1) 0 + H) + single (q - 1) 1 + single q 1 := by
      conv_lhs => rw [decompose_at z (q - 1) h1]
      abel
    rw [e, doCons_add (z.update (q - 1) 0 + H) (i := q) (i' := q - 1) (by omega) hq2]
    abel
  · have hDz : D z = D (z.update (q - 1) 0) + d (q - 1) := by
      conv_lhs => rw [decompose_at z (q - 1) h1]
      rw [D_add, D_single, one_mul]
    have hd := d_cons_even hq hq2
    simp only [D_add, D_single]
    omega

/-- When `z q = 1`, adjacency only occurs among `H` if at all. -/
lemma not_cons_splitpos {z H : Pos} {q : ℕ} (hq2 : 2 ≤ q) (hz : Zk z q) (h1 : z q = 1)
    (hH0 : ∀ i, i ≤ q + 1 → H i = 0) (hadj : ∀ i, H i = 0 ∨ H (i + 1) = 0) (k : ℕ) :
    ¬ legalCons (z + single q 1 + H) k := by
  have ev : ∀ x, (z + single q 1 + H : Pos) x = z x + (if q = x then 1 else 0) + H x := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  rintro ⟨hk2, h3, h4⟩
  rw [ev] at h3 h4
  have hzq1 : z (q - 1) = 0 := by
    have := hz.adj (q - 1)
    rw [show q - 1 + 1 = q by omega] at this
    omega
  by_cases hk : k < q
  · rw [hH0 (k - 1) (by omega)] at h3
    rw [hH0 k (by omega)] at h4
    have hne1 : ¬ q = k - 1 := by omega
    have hne2 : ¬ q = k := by omega
    simp [hne1] at h3
    simp [hne2] at h4
    have ha := hz.adj (k - 1)
    rw [show k - 1 + 1 = k by omega] at ha
    omega
  · by_cases hk1 : k = q
    · subst hk1
      rw [hH0 (k - 1) (by omega), hzq1] at h3
      have hne1 : ¬ k = k - 1 := by omega
      simp [hne1] at h3
    · by_cases hk2' : k = q + 1
      · subst hk2'
        rw [hH0 (q + 1) (by omega), hz.top (q + 1) (by omega)] at h4
        have hne : ¬ q = q + 1 := by omega
        simp [hne] at h4
      · by_cases hk3 : k = q + 2
        · subst hk3
          rw [show q + 2 - 1 = q + 1 by omega, hH0 (q + 1) (by omega),
            hz.top (q + 1) (by omega)] at h3
          have hne : ¬ q = q + 1 := by omega
          simp [hne] at h3
        · rw [hz.top (k - 1) (by omega)] at h3
          rw [hz.top k (by omega)] at h4
          have hne1 : ¬ q = k - 1 := by omega
          have hne2 : ¬ q = k := by omega
          simp [hne1] at h3
          simp [hne2] at h4
          have ha := hadj (k - 1)
          rw [show k - 1 + 1 = k by omega] at ha
          omega

/-- A split in the low state, at an index `≥ 4`. -/
lemma Tr_low_split {z H : Pos} {q : ℕ} (hq4 : 4 ≤ q) (hq : q % 2 = 0) (hz : Zk z q)
    (h1 : z q = 1) (hH0 : ∀ i, i ≤ q + 1 → H i = 0) (hadj : ∀ i, H i = 0 ∨ H (i + 1) = 0) :
    Tr (z + single q 1 + H) 1 1 (z.update q 0 + single (q - 2) 1 + single (q + 1) 1 + H) := by
  have ev : ∀ x, (z + single q 1 + H : Pos) x = z x + (if q = x then 1 else 0) + H x := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  have hA : ¬ legalA1 (z + single q 1 + H) := by
    intro h
    have h' : 2 ≤ (z + single q 1 + H : Pos) 1 := h
    rw [ev, hH0 1 (by omega)] at h'
    have h3 := hz.one 1
    have hne : ¬ q = 1 := by omega
    simp [hne] at h'
    omega
  have hl : legalSplit (z + single q 1 + H) q := by
    refine ⟨by omega, ?_⟩
    rw [ev, h1]
    simp
  have hmin : ∀ j < q, ¬ legalSplit (z + single q 1 + H) j := by
    rintro j hj ⟨hj2, h3⟩
    rw [ev, hH0 j (by omega)] at h3
    have hne : ¬ q = j := by omega
    simp [hne] at h3
    have := hz.one j
    omega
  refine Tr.ofSplit hA (not_cons_splitpos (by omega) hz h1 hH0 hadj) hl hmin ?_ ?_
  · have e0 : doSplit (z + single q 1 + H) q = doSplitG (z + single q 1 + H) q := by
      have h1 : q ≠ 1 := by omega
      have h2 : q ≠ 2 := by omega
      simp [doSplit, h1, h2]
    have e2 : (single q 2 : Pos) = single q 1 + single q 1 := Finsupp.single_add q 1 1
    have e : z + single q 1 + H = (z.update q 0 + H) + single q 2 := by
      rw [e2]
      conv_lhs => rw [decompose_at z q h1]
      abel
    rw [e0, e, doSplitG_add (z.update q 0 + H) (i := q) (i' := q - 2) (by omega) (by omega)]
    abel
  · have hDz : D z = D (z.update q 0) + d q := by
      conv_lhs => rw [decompose_at z q h1]
      rw [D_add, D_single, one_mul]
    have hd := d_split hq hq4
    simp only [D_add, D_single]
    omega

/-- `S_2` in the low state. -/
lemma Tr_low_split2 {z H : Pos} (hz : Zk z 2) (h1 : z 2 = 1)
    (hH0 : ∀ i, i ≤ 2 + 1 → H i = 0) (hadj : ∀ i, H i = 0 ∨ H (i + 1) = 0) :
    Tr (z + single 2 1 + H) 1 1 (z.update 2 0 + single 1 1 + single 3 1 + H) := by
  have ev : ∀ x, (z + single 2 1 + H : Pos) x = z x + (if 2 = x then 1 else 0) + H x := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  have hA : ¬ legalA1 (z + single 2 1 + H) := by
    intro h
    have h' : 2 ≤ (z + single 2 1 + H : Pos) 1 := h
    rw [ev, hH0 1 (by omega)] at h'
    have h3 := hz.one 1
    norm_num at h'
    omega
  have hl : legalSplit (z + single 2 1 + H) 2 := by
    refine ⟨le_refl 2, ?_⟩
    rw [ev, h1]
    simp
  have hmin : ∀ j < 2, ¬ legalSplit (z + single 2 1 + H) j := by
    rintro j hj ⟨hj2, _⟩
    omega
  refine Tr.ofSplit hA (not_cons_splitpos (le_refl 2) hz h1 hH0 hadj) hl hmin ?_ ?_
  · have e0 : doSplit (z + single 2 1 + H) 2 = doSplit2 (z + single 2 1 + H) := by simp [doSplit]
    have e2 : (single 2 2 : Pos) = single 2 1 + single 2 1 := Finsupp.single_add 2 1 1
    have e : z + single 2 1 + H = (z.update 2 0 + H) + single 2 2 := by
      rw [e2]
      conv_lhs => rw [decompose_at z 2 h1]
      abel
    rw [e0, e, doSplit2_add]
    abel
  · have hDz : D z = D (z.update 2 0) + d 2 := by
      conv_lhs => rw [decompose_at z 2 h1]
      rw [D_add, D_single, one_mul]
    have hd := d_split2
    simp only [D_add, D_single]
    omega

/-! ### The quiet insertion cascade -/

/-- The high part is out of reach of the insertion at `q`. -/
structure Inert (H : Pos) (q : ℕ) : Prop where
  low : ∀ i, i ≤ q + 2 → H i = 0
  adj : ∀ i, H i = 0 ∨ H (i + 1) = 0

lemma Inert.zero1 {H : Pos} {q : ℕ} (h : Inert H q) : ∀ i, i ≤ q + 1 → H i = 0 :=
  fun i hi => h.low i (by omega)

/-- Insertion of one chip at the even index `q` in a Zeckendorf low state, with a frozen
high part. All moves are even-index moves, so the counter records every move. -/
theorem cascade : ∀ (q : ℕ), q % 2 = 0 → 2 ≤ q → ∀ (z H : Pos), Zk z q → Inert H q →
    ∃ z' k, Zk z' (q + 1) ∧ Tr (z + single q 1 + H) k k (z' + H) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq hq2 z H hz hH
    by_cases hz1 : z q = 1
    · -- Case (iii): a repeat at `q`.
      have hq1 : z (q - 1) = 0 := by
        have := hz.adj (q - 1)
        rw [show q - 1 + 1 = q by omega] at this
        omega
      by_cases hq3 : q = 2
      · subst hq3
        have h2 := Tr_low_split2 hz hz1 hH.zero1 hH.adj
        refine ⟨z.update 2 0 + single 1 1 + single 3 1, 1, ?_, h2⟩
        have ha : Zk (z.update 2 0) 0 := by
          refine hz.erase 2 0 ?_
          intro x hx hx2
          have hx3 : x = 1 ∨ 3 ≤ x := by omega
          rcases hx3 with rfl | hx3
          · exact hq1
          · exact hz.top x (by omega)
        have hb : Zk (z.update 2 0 + single 1 1) 2 := by
          refine ha.addAt (le_refl 1) ?_ ?_ ?_ (by omega) (by omega)
          · exact ha.top 1 (by omega)
          · exact ha.zero
          · exact ha.top 2 (by omega)
        refine hb.addAt (by omega) ?_ ?_ ?_ (by omega) (le_refl 3)
        · exact hb.top 3 (by omega)
        · simp [Finsupp.add_apply, Finsupp.single_apply, Finsupp.update_apply]
        · exact hb.top 4 (by omega)
      · have hq4 : 4 ≤ q := by omega
        have ha : Zk (z.update q 0) (q - 2) := by
          refine hz.erase q (q - 2) ?_
          intro x hx hx2
          have hx3 : x = q - 1 ∨ q < x := by omega
          rcases hx3 with rfl | hx3
          · exact hq1
          · exact hz.top x hx3
        have hH' : Inert (single (q + 1) 1 + H) (q - 2) := by
          constructor
          · intro i hi
            have hne : ¬ q + 1 = i := by omega
            rw [Finsupp.add_apply, hH.low i (by omega)]
            simp [Finsupp.single_apply, hne]
          · intro i
            by_cases h1 : i = q + 1
            · subst h1
              refine Or.inr ?_
              have hne : ¬ q + 1 = q + 1 + 1 := by omega
              rw [Finsupp.add_apply, hH.low (q + 1 + 1) (by omega)]
              simp [Finsupp.single_apply, hne]
            · by_cases h2 : i = q
              · subst h2
                refine Or.inl ?_
                have hne : ¬ i + 1 = i := by omega
                rw [Finsupp.add_apply, hH.low i (by omega)]
                simp [Finsupp.single_apply, hne]
              · have hne1 : ¬ q + 1 = i := by omega
                have hne2 : ¬ q + 1 = i + 1 := by omega
                simp only [Finsupp.add_apply, Finsupp.single_apply, hne1, hne2, ite_false,
                  zero_add]
                exact hH.adj i
        obtain ⟨z'', k, hz'', hTr⟩ := ih (q - 2) (by omega) (by omega) (by omega) _ _ ha hH'
        refine ⟨z'' + single (q + 1) 1, 1 + k, ?_, ?_⟩
        · refine hz''.addAt (by omega) ?_ ?_ ?_ (by omega) (le_refl _)
          · exact hz''.top _ (by omega)
          · exact hz''.top _ (by omega)
          · exact hz''.top _ (by omega)
        · have h1' := Tr_low_split hq4 hq hz hz1 hH.zero1 hH.adj
          have e : z.update q 0 + single (q - 2) 1 + single (q + 1) 1 + H
              = z.update q 0 + single (q - 2) 1 + (single (q + 1) 1 + H) := by abel
          rw [e] at h1'
          have h2' := h1'.trans hTr
          have e2 : z'' + (single (q + 1) 1 + H) = z'' + single (q + 1) 1 + H := by abel
          rw [e2] at h2'
          exact h2'
    · have hz0 : z q = 0 := by
        have := hz.one q
        omega
      by_cases h1 : z (q - 1) = 1
      · -- Case (ii): the combine at `q` fires.
        have h2 := Tr_low_cons hq2 hq hz h1 (fun i hi => hH.low i (by omega))
        refine ⟨z.update (q - 1) 0 + single (q + 1) 1, 1, ?_, h2⟩
        have ha : Zk (z.update (q - 1) 0) q := by
          refine hz.erase (q - 1) q ?_
          intro x hx _
          exact hz.top x hx
        refine ha.addAt (by omega) ?_ ?_ ?_ (by omega) (le_refl _)
        · have hne : q + 1 ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne]
          exact hz.top _ (by omega)
        · rw [show q + 1 - 1 = q by omega]
          have hne : q ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne, hz0]
        · have hne : q + 1 + 1 ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne]
          exact hz.top _ (by omega)
      · -- Case (i): nothing to do.
        have h0 : z (q - 1) = 0 := by
          have := hz.one (q - 1)
          omega
        refine ⟨z + single q 1, 0, ?_, Tr.refl _⟩
        exact hz.addAt (by omega) hz0 h0 (hz.top _ (by omega)) (by omega) (by omega)

/-- The window with no pending low interaction is inert for lower insertions. -/
lemma W_quiet_adj (q c1 c3 c5 x : ℕ) :
    W q 0 c1 0 c3 0 c5 x = 0 ∨ W q 0 c1 0 c3 0 c5 (x + 1) = 0 := by
  by_cases h2 : x = q + 2
  · subst h2
    exact Or.inr W_at3
  · by_cases h4 : x = q + 4
    · subst h4
      exact Or.inr W_at5
    · by_cases h6 : x = q + 6
      · subst h6
        exact Or.inr (W_above (by omega))
      · refine Or.inl ?_
        rw [W_apply]
        split_ifs <;> omega

lemma Inert_W {q' q : ℕ} (h : q' + 2 ≤ q) (c1 c3 c5 : ℕ) : Inert (W q 0 c1 0 c3 0 c5) q' :=
  ⟨fun i hi => W_below (by omega), fun x => W_quiet_adj q c1 c3 c5 x⟩

lemma Inert_W0 (q c3 c5 : ℕ) : Inert (W q 0 0 0 c3 0 c5) q := by
  constructor
  · intro i hi
    by_cases h : i ≤ q
    · exact W_below h
    · have e : i = q + 1 ∨ i = q + 2 := by omega
      rcases e with rfl | rfl
      · exact W_at1
      · exact W_at2
  · intro x
    exact W_quiet_adj q 0 c3 c5 x

/-- A chip added at `q` to a Zeckendorf part keeps non-adjacency when `z (q-1) = 0`. -/
lemma Zk.lowQ_add {z : Pos} {q : ℕ} (hq2 : 2 ≤ q) (hz : Zk z q) (h1 : z (q - 1) = 0) :
    LowQ (z + single q 1) q := by
  have ev : ∀ x, (z + single q 1 : Pos) x = z x + (if q = x then 1 else 0) := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [ev, ev]
    by_cases hx : x = q
    · subst hx
      refine Or.inr ?_
      have hne : ¬ x = x + 1 := by omega
      simp [hne, hz.top (x + 1) (by omega)]
    · by_cases hx2 : x + 1 = q
      · refine Or.inl ?_
        have e : x = q - 1 := by omega
        rw [e]
        have hne : ¬ q = q - 1 := by omega
        simp [hne, h1]
      · have hne1 : ¬ q = x := by omega
        have hne2 : ¬ q = x + 1 := by omega
        simp only [hne1, hne2, ite_false, add_zero]
        exact hz.adj x
  · rw [ev]
    have hne : ¬ q = 1 := by omega
    simp [hne, hz.one 1]
  · rw [ev]
    have hne : ¬ q = 0 := by omega
    simp [hne, hz.zero]
  · intro x hx
    rw [ev]
    have hne : ¬ q = x := by omega
    simp [hne, hz.top x hx]

lemma LowQ.mono {L : Pos} {t t' : ℕ} (h : LowQ L t) (ht : t ≤ t') : LowQ L t' :=
  ⟨h.adj, h.one1, h.zero, fun i hi => h.top i (by omega)⟩

/-- A pending high transition around a low insertion at `q`. -/
theorem pending {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) {y H0 H1 : Pos} {r e : ℕ}
    (hy : Zk y q) (hH1 : Inert H1 q) (hH0 : ∀ i, i ≤ q → H0 i = 0)
    (hhigh : ∀ L, LowQ L (q + 1) → Tr (L + H0) r e (L + H1)) :
    ∃ z' k', Zk z' (q + 1) ∧ Tr (y + single q 1 + H0) (k' + r) (k' + e) (z' + H1) := by
  by_cases h1 : y (q - 1) = 1
  · have hy0 : y q = 0 := by
      have := hy.adj (q - 1)
      rw [show q - 1 + 1 = q by omega] at this
      omega
    have h2 := Tr_low_cons hq2 hq hy h1 hH0
    have hz' : Zk (y.update (q - 1) 0 + single (q + 1) 1) (q + 1) := by
      have ha : Zk (y.update (q - 1) 0) q :=
        hy.erase (q - 1) q (fun x hx _ => hy.top x hx)
      refine ha.addAt (by omega) ?_ ?_ ?_ (by omega) (le_refl _)
      · have hne : q + 1 ≠ q - 1 := by omega
        simp [Finsupp.update_apply, hne]
        exact hy.top _ (by omega)
      · rw [show q + 1 - 1 = q by omega]
        have hne : q ≠ q - 1 := by omega
        simp [Finsupp.update_apply, hne, hy0]
      · have hne : q + 1 + 1 ≠ q - 1 := by omega
        simp [Finsupp.update_apply, hne]
        exact hy.top _ (by omega)
    have h3 := hhigh _ hz'.lowQ
    exact ⟨_, 1, hz', h2.trans h3⟩
  · have h0 : y (q - 1) = 0 := by
      have := hy.one (q - 1)
      omega
    have h3 := hhigh (y + single q 1) ((hy.lowQ_add hq2 h0).mono (by omega))
    obtain ⟨z', k, hz', h4⟩ := cascade q hq hq2 y H1 hy hH1
    refine ⟨z', k, hz', ?_⟩
    have h5 := h3.trans h4
    rwa [Nat.add_comm r, Nat.add_comm e] at h5

end Zeck
