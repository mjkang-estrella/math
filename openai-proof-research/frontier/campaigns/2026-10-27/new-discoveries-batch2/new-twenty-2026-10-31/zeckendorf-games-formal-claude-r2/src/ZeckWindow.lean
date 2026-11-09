/-
  Part (b) of MathDB 347063: window positions and the atomic Combine Smallest moves.

  A position is a low part plus six consecutive counts at indices `q+1, …, q+6`.  The pool of the
  level `p = q + 2` sits at index `q+2`.
-/
import ZeckMoves

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

/-- A low part with no two adjacent indices and no pending `A1`. -/
structure LowQ (L : Pos) (t : ℕ) : Prop where
  adj : ∀ i, L i = 0 ∨ L (i + 1) = 0
  one1 : L 1 ≤ 1
  zero : L 0 = 0
  top : ∀ i, t < i → L i = 0

/-- A Zeckendorf low part of top index at most `t`. -/
structure Zk (z : Pos) (t : ℕ) : Prop where
  one : ∀ i, z i ≤ 1
  adj : ∀ i, z i = 0 ∨ z (i + 1) = 0
  zero : z 0 = 0
  top : ∀ i, t < i → z i = 0

lemma Zk.lowQ {z : Pos} {t : ℕ} (h : Zk z t) : LowQ z t :=
  ⟨h.adj, h.one 1, h.zero, h.top⟩

lemma Zk.mono {z : Pos} {t t' : ℕ} (h : Zk z t) (ht : t ≤ t') : Zk z t' :=
  ⟨h.one, h.adj, h.zero, fun i hi => h.top i (by omega)⟩

lemma decompose_at (z : Pos) (i : ℕ) (h : z i = 1) : z = z.update i 0 + single i 1 := by
  ext t
  simp only [Finsupp.update_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h1 : t = i
  · subst h1; simp [h]
  · simp [h1, Ne.symm h1]

lemma Zk.erase {z : Pos} {t : ℕ} (hz : Zk z t) (i t' : ℕ)
    (h : ∀ x, t' < x → x ≠ i → z x = 0) : Zk (z.update i 0) t' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [Finsupp.update_apply]
    split_ifs
    · omega
    · exact hz.one x
  · intro x
    rw [Finsupp.update_apply, Finsupp.update_apply]
    split_ifs with h1 h2
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact hz.adj x
  · rw [Finsupp.update_apply]
    split_ifs
    · rfl
    · exact hz.zero
  · intro x hx
    rw [Finsupp.update_apply]
    split_ifs with h1
    · rfl
    · exact h x hx h1

lemma Zk.addAt {z : Pos} {t t' i : ℕ} (hz : Zk z t) (hi : 1 ≤ i) (h0 : z i = 0)
    (h1 : z (i - 1) = 0) (h2 : z (i + 1) = 0) (ht : t ≤ t') (hit : i ≤ t') :
    Zk (z + single i 1) t' := by
  have ev : ∀ x, (z + single i 1 : Pos) x = z x + (if i = x then 1 else 0) := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [ev]
    have := hz.one x
    by_cases hx : i = x
    · subst hx; simp [h0]
    · simp [hx]; omega
  · intro x
    rw [ev, ev]
    by_cases hx : i = x
    · subst hx
      refine Or.inr ?_
      have : ¬ i = i + 1 := by omega
      simp [this, h2]
    · by_cases hx1 : i = x + 1
      · refine Or.inl ?_
        have e : x = i - 1 := by omega
        rw [e]
        have : ¬ i = i - 1 := by omega
        simp [this, h1]
      · simp only [hx, hx1, ite_false, add_zero]
        exact hz.adj x
  · rw [ev]
    have : ¬ i = 0 := by omega
    simp [this, hz.zero]
  · intro x hx
    rw [ev]
    have hne : ¬ i = x := by omega
    simp [hne]
    exact hz.top x (by omega)

/-! ### Window -/

/-- Six consecutive chip counts at indices `q+1, …, q+6`. -/
noncomputable def W (q c0 c1 c2 c3 c4 c5 : ℕ) : Pos :=
  single (q + 1) c0 + single (q + 2) c1 + single (q + 3) c2 + single (q + 4) c3
    + single (q + 5) c4 + single (q + 6) c5

lemma W_apply (q c0 c1 c2 c3 c4 c5 t : ℕ) :
    W q c0 c1 c2 c3 c4 c5 t =
      (if q + 1 = t then c0 else 0) + (if q + 2 = t then c1 else 0)
      + (if q + 3 = t then c2 else 0) + (if q + 4 = t then c3 else 0)
      + (if q + 5 = t then c4 else 0) + (if q + 6 = t then c5 else 0) := by
  simp only [W, Finsupp.add_apply, Finsupp.single_apply]

lemma W_below {q c0 c1 c2 c3 c4 c5 t : ℕ} (h : t ≤ q) : W q c0 c1 c2 c3 c4 c5 t = 0 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_above {q c0 c1 c2 c3 c4 c5 t : ℕ} (h : q + 6 < t) : W q c0 c1 c2 c3 c4 c5 t = 0 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at1 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 1) = c0 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at2 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 2) = c1 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at3 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 3) = c2 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at4 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 4) = c3 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at5 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 5) = c4 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at6 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 6) = c5 := by
  rw [W_apply]; split_ifs <;> omega

lemma D_W (q c0 c1 c2 c3 c4 c5 : ℕ) :
    D (W q c0 c1 c2 c3 c4 c5) = c0 * d (q + 1) + c1 * d (q + 2) + c2 * d (q + 3)
      + c3 * d (q + 4) + c4 * d (q + 5) + c5 * d (q + 6) := by
  simp only [W, D_add, D_single]

lemma val_W (q c0 c1 c2 c3 c4 c5 : ℕ) :
    val (W q c0 c1 c2 c3 c4 c5) = c0 * F (q + 1) + c1 * F (q + 2) + c2 * F (q + 3)
      + c3 * F (q + 4) + c4 * F (q + 5) + c5 * F (q + 6) := by
  simp only [W, val_add, val_single]

lemma chips_W (q c0 c1 c2 c3 c4 c5 : ℕ) :
    chips (W q c0 c1 c2 c3 c4 c5) = c0 + c1 + c2 + c3 + c4 + c5 := by
  simp only [W, chips_add, chips_single]

/-- Shifting the window up two indices once the two lowest counts vanish. -/
lemma W_shift (q c2 c3 c4 c5 : ℕ) :
    W q 0 0 c2 c3 c4 c5 = W (q + 2) c2 c3 c4 c5 0 0 := by
  ext t
  simp only [W_apply]
  split_ifs <;> omega

/-! ### Legality helpers -/

lemma legalCons_mk (a : Pos) {i i' : ℕ} (hi : i' + 1 = i) (h2 : 2 ≤ i) (h1 : 1 ≤ a i')
    (h0 : 1 ≤ a i) : legalCons a i := by
  subst hi
  refine ⟨h2, ?_, h0⟩
  simpa using h1

lemma not_cons_of_zero (a : Pos) {i i' : ℕ} (hi : i' + 1 = i) (h : a i' = 0 ∨ a i = 0) :
    ¬ legalCons a i := by
  subst hi
  rintro ⟨_, h1, h0⟩
  have e : i' + 1 - 1 = i' := by omega
  rw [e] at h1
  omega

lemma not_A1 {L : Pos} {q c0 c1 c2 c3 c4 c5 : ℕ} (hL : LowQ L q) (h : 1 ≤ q ∨ c0 ≤ 1) :
    ¬ legalA1 (L + W q c0 c1 c2 c3 c4 c5) := by
  intro hh
  have hh' : 2 ≤ (L + W q c0 c1 c2 c3 c4 c5 : Pos) 1 := hh
  rw [Finsupp.add_apply] at hh'
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hL1 : L 1 = 0 := hL.top 1 (by omega)
    have hW : W 0 c0 c1 c2 c3 c4 c5 1 = c0 := by
      rw [W_apply]; split_ifs <;> omega
    rw [hL1, hW] at hh'
    omega
  · rw [W_below (show 1 ≤ q by omega)] at hh'
    have := hL.one1
    omega

lemma not_cons_low {L : Pos} {q : ℕ} (hL : LowQ L q) (c0 c1 c2 c3 c4 c5 : ℕ)
    (h : L q = 0 ∨ c0 = 0) {k : ℕ} (hk : k ≤ q + 1) :
    ¬ legalCons (L + W q c0 c1 c2 c3 c4 c5) k := by
  rintro ⟨hk2, h1, h0⟩
  rw [Finsupp.add_apply] at h1 h0
  rw [W_below (show k - 1 ≤ q by omega)] at h1
  have hadj := hL.adj (k - 1)
  rw [show k - 1 + 1 = k by omega] at hadj
  by_cases hk' : k ≤ q
  · rw [W_below hk'] at h0
    omega
  · have hk1 : k = q + 1 := by omega
    subst hk1
    rw [show q + 1 - 1 = q by omega] at h1
    rw [hL.top (q + 1) (by omega), W_at1] at h0
    omega

/-- All non-adjacency checks for a quiet window. -/
lemma not_cons_quiet {L : Pos} {q : ℕ} (hL : LowQ L q) (c1 c3 c5 : ℕ) (k : ℕ) :
    ¬ legalCons (L + W q 0 c1 0 c3 0 c5) k := by
  by_cases hk : k ≤ q + 1
  · exact not_cons_low hL _ _ _ _ _ _ (Or.inr rfl) hk
  · have top : ∀ x, q < x → L x = 0 := hL.top
    by_cases hk2 : k = q + 2
    · subst hk2
      refine not_cons_of_zero _ (i' := q + 1) rfl (Or.inl ?_)
      rw [Finsupp.add_apply, W_at1, top _ (by omega)]
    · by_cases hk3 : k = q + 3
      · subst hk3
        refine not_cons_of_zero _ (i' := q + 2) rfl (Or.inr ?_)
        rw [Finsupp.add_apply, W_at3, top _ (by omega)]
      · by_cases hk4 : k = q + 4
        · subst hk4
          refine not_cons_of_zero _ (i' := q + 3) rfl (Or.inl ?_)
          rw [Finsupp.add_apply, W_at3, top _ (by omega)]
        · by_cases hk5 : k = q + 5
          · subst hk5
            refine not_cons_of_zero _ (i' := q + 4) rfl (Or.inr ?_)
            rw [Finsupp.add_apply, W_at5, top _ (by omega)]
          · by_cases hk6 : k = q + 6
            · subst hk6
              refine not_cons_of_zero _ (i' := q + 5) rfl (Or.inl ?_)
              rw [Finsupp.add_apply, W_at5, top _ (by omega)]
            · refine not_cons_of_zero _ (i' := k - 1) (by omega) (Or.inr ?_)
              rw [Finsupp.add_apply, W_above (by omega), top _ (by omega)]

theorem Tr.ofCons {a b : Pos} {i e : ℕ} (hA : ¬ legalA1 a) (hl : legalCons a i)
    (hmin : ∀ j < i, ¬ legalCons a j) (hdo : doCons a i = b) (hd : D b = D a + e) :
    Tr a 1 e b :=
  Tr.ofStep (Or.inr (Or.inl ⟨i, hl⟩)) ((stepCS_cons a hA hl hmin).trans hdo) hd

theorem Tr.ofSplit {a b : Pos} {i e : ℕ} (hA : ¬ legalA1 a) (hc : ∀ j, ¬ legalCons a j)
    (hl : legalSplit a i) (hmin : ∀ j < i, ¬ legalSplit a j) (hdo : doSplit a i = b)
    (hd : D b = D a + e) : Tr a 1 e b :=
  Tr.ofStep (Or.inr (Or.inr ⟨i, hl⟩)) ((stepCS_split a hA hc hl hmin).trans hdo) hd

theorem Tr.ofA1 {a b : Pos} {e : ℕ} (hA : legalA1 a) (hdo : doA1 a = b)
    (hd : D b = D a + e) : Tr a 1 e b :=
  Tr.ofStep (Or.inl hA) ((stepCS_A1 a hA).trans hdo) hd

/-! ### The four window combines -/

/-- `C_p`: the chip at `p-1` meets the pool. Counter `+1`. -/
lemma Tr_Cp {L : Pos} {q : ℕ} (hL : LowQ L q) (hL0 : L q = 0) (hq : q % 2 = 0)
    (c0 c1 c2 c3 c4 c5 : ℕ) (hA : 1 ≤ q ∨ c0 = 0) :
    Tr (L + W q (c0 + 1) (c1 + 1) c2 c3 c4 c5) 1 1 (L + W q c0 c1 (c2 + 1) c3 c4 c5) := by
  have hl : legalCons (L + W q (c0 + 1) (c1 + 1) c2 c3 c4 c5) (q + 2) := by
    refine legalCons_mk _ (i' := q + 1) rfl (by omega) ?_ ?_
    · rw [Finsupp.add_apply, W_at1]; omega
    · rw [Finsupp.add_apply, W_at2]; omega
  have hmin : ∀ k < q + 2, ¬ legalCons (L + W q (c0 + 1) (c1 + 1) c2 c3 c4 c5) k := by
    intro k hk
    exact not_cons_low hL _ _ _ _ _ _ (Or.inl hL0) (by omega)
  refine Tr.ofCons (not_A1 hL ?_) hl hmin ?_ ?_
  · rcases hA with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · have e : L + W q (c0 + 1) (c1 + 1) c2 c3 c4 c5
        = (L + W q c0 c1 c2 c3 c4 c5) + single (q + 1) 1 + single (q + 2) 1 := by
      simp only [W, Finsupp.single_add]
      abel
    rw [e, doCons_add (L + W q c0 c1 c2 c3 c4 c5) (i := q + 2) (i' := q + 1) rfl (by omega)]
    simp only [W, Finsupp.single_add, show q + 2 + 1 = q + 3 from rfl]
    abel
  · have hd : d (q + 3) = d (q + 2) + d (q + 1) + 1 := by
      have := d_cons_even (q := q + 2) (by omega) (by omega)
      simpa using this
    rw [D_add, D_add, D_W, D_W, hd]
    ring

/-- `C_{p+1}`: the output combine. Counter unchanged. -/
lemma Tr_Cp1 {L : Pos} {q : ℕ} (hL : LowQ L q) (hq : q % 2 = 0)
    (c1 c2 c3 c4 c5 : ℕ) :
    Tr (L + W q 0 (c1 + 1) (c2 + 1) c3 c4 c5) 1 0 (L + W q 0 c1 c2 (c3 + 1) c4 c5) := by
  have top : ∀ x, q < x → L x = 0 := hL.top
  have hl : legalCons (L + W q 0 (c1 + 1) (c2 + 1) c3 c4 c5) (q + 3) := by
    refine legalCons_mk _ (i' := q + 2) rfl (by omega) ?_ ?_
    · rw [Finsupp.add_apply, W_at2]; omega
    · rw [Finsupp.add_apply, W_at3]; omega
  have hmin : ∀ k < q + 3, ¬ legalCons (L + W q 0 (c1 + 1) (c2 + 1) c3 c4 c5) k := by
    intro k hk
    by_cases hk' : k ≤ q + 1
    · exact not_cons_low hL _ _ _ _ _ _ (Or.inr rfl) hk'
    · have e : k = q + 2 := by omega
      subst e
      refine not_cons_of_zero _ (i' := q + 1) rfl (Or.inl ?_)
      rw [Finsupp.add_apply, W_at1, top _ (by omega)]
  refine Tr.ofCons (not_A1 hL (Or.inr (by omega))) hl hmin ?_ ?_
  · have e : L + W q 0 (c1 + 1) (c2 + 1) c3 c4 c5
        = (L + W q 0 c1 c2 c3 c4 c5) + single (q + 2) 1 + single (q + 3) 1 := by
      simp only [W, Finsupp.single_add]
      abel
    rw [e, doCons_add (L + W q 0 c1 c2 c3 c4 c5) (i := q + 3) (i' := q + 2) rfl (by omega)]
    simp only [W, Finsupp.single_add, show q + 3 + 1 = q + 4 from rfl]
    abel
  · have hd : d (q + 4) = d (q + 3) + d (q + 2) := by
      have := d_cons_odd (q := q + 3) (by omega) (by omega)
      simpa using this
    rw [D_add, D_add, D_W, D_W, hd]
    ring

/-- `C_{p+2}`: the chip at `p+1` meets the output pile. Counter `+1`. -/
lemma Tr_Cp2 {L : Pos} {q : ℕ} (hL : LowQ L q) (hq : q % 2 = 0)
    (c2 c3 c4 c5 : ℕ) :
    Tr (L + W q 0 0 (c2 + 1) (c3 + 1) c4 c5) 1 1 (L + W q 0 0 c2 c3 (c4 + 1) c5) := by
  have top : ∀ x, q < x → L x = 0 := hL.top
  have hl : legalCons (L + W q 0 0 (c2 + 1) (c3 + 1) c4 c5) (q + 4) := by
    refine legalCons_mk _ (i' := q + 3) rfl (by omega) ?_ ?_
    · rw [Finsupp.add_apply, W_at3]; omega
    · rw [Finsupp.add_apply, W_at4]; omega
  have hmin : ∀ k < q + 4, ¬ legalCons (L + W q 0 0 (c2 + 1) (c3 + 1) c4 c5) k := by
    intro k hk
    by_cases hk' : k ≤ q + 1
    · exact not_cons_low hL _ _ _ _ _ _ (Or.inr rfl) hk'
    · by_cases hk2 : k = q + 2
      · subst hk2
        refine not_cons_of_zero _ (i' := q + 1) rfl (Or.inl ?_)
        rw [Finsupp.add_apply, W_at1, top _ (by omega)]
      · have e : k = q + 3 := by omega
        subst e
        refine not_cons_of_zero _ (i' := q + 2) rfl (Or.inl ?_)
        rw [Finsupp.add_apply, W_at2, top _ (by omega)]
  refine Tr.ofCons (not_A1 hL (Or.inr (by omega))) hl hmin ?_ ?_
  · have e : L + W q 0 0 (c2 + 1) (c3 + 1) c4 c5
        = (L + W q 0 0 c2 c3 c4 c5) + single (q + 3) 1 + single (q + 4) 1 := by
      simp only [W, Finsupp.single_add]
      abel
    rw [e, doCons_add (L + W q 0 0 c2 c3 c4 c5) (i := q + 4) (i' := q + 3) rfl (by omega)]
    simp only [W, Finsupp.single_add, show q + 4 + 1 = q + 5 from rfl]
    abel
  · have hd : d (q + 5) = d (q + 4) + d (q + 3) + 1 := by
      have := d_cons_even (q := q + 4) (by omega) (by omega)
      simpa using this
    rw [D_add, D_add, D_W, D_W, hd]
    ring

/-- `C_{p+3}`: the second output combine. Counter unchanged. -/
lemma Tr_Cp3 {L : Pos} {q : ℕ} (hL : LowQ L q) (hq : q % 2 = 0)
    (c3 c4 c5 : ℕ) :
    Tr (L + W q 0 0 0 (c3 + 1) (c4 + 1) c5) 1 0 (L + W q 0 0 0 c3 c4 (c5 + 1)) := by
  have top : ∀ x, q < x → L x = 0 := hL.top
  have hl : legalCons (L + W q 0 0 0 (c3 + 1) (c4 + 1) c5) (q + 5) := by
    refine legalCons_mk _ (i' := q + 4) rfl (by omega) ?_ ?_
    · rw [Finsupp.add_apply, W_at4]; omega
    · rw [Finsupp.add_apply, W_at5]; omega
  have hmin : ∀ k < q + 5, ¬ legalCons (L + W q 0 0 0 (c3 + 1) (c4 + 1) c5) k := by
    intro k hk
    by_cases hk' : k ≤ q + 1
    · exact not_cons_low hL _ _ _ _ _ _ (Or.inr rfl) hk'
    · by_cases hk2 : k = q + 2
      · subst hk2
        refine not_cons_of_zero _ (i' := q + 1) rfl (Or.inl ?_)
        rw [Finsupp.add_apply, W_at1, top _ (by omega)]
      · by_cases hk3 : k = q + 3
        · subst hk3
          refine not_cons_of_zero _ (i' := q + 2) rfl (Or.inl ?_)
          rw [Finsupp.add_apply, W_at2, top _ (by omega)]
        · have e : k = q + 4 := by omega
          subst e
          refine not_cons_of_zero _ (i' := q + 3) rfl (Or.inl ?_)
          rw [Finsupp.add_apply, W_at3, top _ (by omega)]
  refine Tr.ofCons (not_A1 hL (Or.inr (by omega))) hl hmin ?_ ?_
  · have e : L + W q 0 0 0 (c3 + 1) (c4 + 1) c5
        = (L + W q 0 0 0 c3 c4 c5) + single (q + 4) 1 + single (q + 5) 1 := by
      simp only [W, Finsupp.single_add]
      abel
    rw [e, doCons_add (L + W q 0 0 0 c3 c4 c5) (i := q + 5) (i' := q + 4) rfl (by omega)]
    simp only [W, Finsupp.single_add, show q + 5 + 1 = q + 6 from rfl]
    abel
  · have hd : d (q + 6) = d (q + 5) + d (q + 4) := by
      have := d_cons_odd (q := q + 5) (by omega) (by omega)
      simpa using this
    rw [D_add, D_add, D_W, D_W, hd]
    ring

end Zeck
