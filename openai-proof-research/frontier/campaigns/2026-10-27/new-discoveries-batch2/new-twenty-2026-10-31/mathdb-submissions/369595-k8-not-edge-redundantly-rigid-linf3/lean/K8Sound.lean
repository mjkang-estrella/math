import K8Comb
import K8Patterns
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Soundness of the propositional instance

For a placement `p : Fin 8 → Fin 3 → ℝ` the assignment `assign p` gives the
colour variables and sign variables their geometric meaning.  If `p` is `Good`
and `Anchored` then `assign p` satisfies every clause of every valid provenance
record (`base_of_good`).
-/

set_option linter.unusedSimpArgs false

namespace K8

open Rup

/-- The placement extended by `0` to all natural-number indices. -/
noncomputable def P (p : Fin 8 → Fin 3 → ℝ) (x c : ℕ) : ℝ :=
  if h : x < 8 ∧ c < 3 then p ⟨x, h.1⟩ ⟨c, h.2⟩ else 0

/-- Dominance of colour `c` on the pair `(u, v)`, natural-number version. -/
def DomN (p : Fin 8 → Fin 3 → ℝ) (u v c : ℕ) : Prop :=
  ∀ j, j < 3 → j ≠ c → |P p v j - P p u j| < |P p v c - P p u c|

open Classical in
/-- The assignment induced by a placement. -/
noncomputable def assign (p : Fin 8 → Fin 3 → ℝ) (x : ℕ) : Bool :=
  if 1 ≤ x ∧ x ≤ 84 then
    decide (DomN p (pairs.getD ((x - 1) / 3) (0, 0)).1 (pairs.getD ((x - 1) / 3) (0, 0)).2
      ((x - 1) % 3))
  else if 85 ≤ x ∧ x ≤ 112 then
    decide (∃ c, c < 3 ∧ DomN p (pairs.getD (x - 85) (0, 0)).1 (pairs.getD (x - 85) (0, 0)).2 c ∧
      P p (pairs.getD (x - 85) (0, 0)).1 c < P p (pairs.getD (x - 85) (0, 0)).2 c)
  else false

/-! ### Finite facts about the numbering, checked by kernel evaluation -/

theorem pairs_edgeIdx_fin : ∀ u v : Fin 8, u < v →
    pairs.getD (edgeIdx u v) (0, 0) = (u.val, v.val) ∧ edgeIdx u v < 28 := by
  decide +kernel

theorem pairs_edgeIdx_aux {u v : ℕ} (hu : u < 8) (hv : v < 8) (huv : u < v) :
    pairs.getD (edgeIdx u v) (0, 0) = (u, v) ∧ edgeIdx u v < 28 :=
  pairs_edgeIdx_fin ⟨u, hu⟩ ⟨v, hv⟩ huv

theorem mem_pairs_fin : ∀ u v : Fin 8, u < v → (u.val, v.val) ∈ pairs := by
  decide +kernel

theorem testBit_some_fin : ∀ S : Fin 256, 0 < S.val → ∃ a : Fin 8, S.val.testBit a = true := by
  decide +kernel

theorem testBit_none_fin : ∀ S : Fin 255, ∃ a : Fin 8, S.val.testBit a = false := by
  decide +kernel

theorem perms3_fin : ∀ (t : Fin 6) (c c' : Fin 3),
    (perms3.getD t []).getD c 0 < 3 ∧
      ((perms3.getD t []).getD c 0 = (perms3.getD t []).getD c' 0 → c = c') := by
  decide +kernel

theorem perms3_aux {t c c' : ℕ} (ht : t < 6) (hc : c < 3) (hc' : c' < 3) :
    (perms3.getD t []).getD c 0 < 3 ∧
      ((perms3.getD t []).getD c 0 = (perms3.getD t []).getD c' 0 → c = c') := by
  have := perms3_fin ⟨t, ht⟩ ⟨c, hc⟩ ⟨c', hc'⟩
  simpa [Fin.ext_iff] using this

theorem reps_fin : ∀ r : Fin 7, ∀ e ∈ reps.getD r [], e.1 < 6 ∧ e.2.1 < 3 := by
  decide +kernel

theorem e4_fin : ∀ i : Fin 6, (e4.getD i (0, 0)).1 < 4 ∧ (e4.getD i (0, 0)).2 < 4 ∧
    (e4.getD i (0, 0)).1 ≠ (e4.getD i (0, 0)).2 := by
  decide +kernel

/-! ### Literals -/

theorem litVal_pos (α : ℕ → Bool) (x : ℕ) : litVal α (pos x) = α x := by
  unfold litVal pos
  have h1 : (2 * x) >>> 1 = x := by rw [Nat.shiftRight_one]; omega
  have h2 : (2 * x).testBit 0 = false := by rw [Nat.testBit_zero]; simp
  rw [h1, h2, Bool.xor_false]

theorem litVal_neg' (α : ℕ → Bool) (x : ℕ) : litVal α (neg x) = !α x := by
  unfold litVal neg
  have h1 : (2 * x + 1) >>> 1 = x := by rw [Nat.shiftRight_one]; omega
  have h2 : (2 * x + 1).testBit 0 = true := by rw [Nat.testBit_zero]; simp
  rw [h1, h2, Bool.xor_true]

theorem sat_of_mem {α : ℕ → Bool} {C : Clause} {l : ℕ} (hl : l ∈ C) (hv : litVal α l = true) :
    Sat α C := List.any_eq_true.mpr ⟨l, hl, hv⟩

theorem colVar_comm (u v c : ℕ) : colVar u v c = colVar v u c := by
  unfold colVar; rw [min_comm, max_comm]

theorem sgnVar_comm (u v : ℕ) : sgnVar u v = sgnVar v u := by
  unfold sgnVar; rw [min_comm, max_comm]

theorem colVar_minmax (a b c : ℕ) : colVar (min a b) (max a b) c = colVar a b c := by
  rcases le_total a b with h | h
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right h, Nat.max_eq_left h, colVar_comm]

/-! ### The induced assignment on colour and sign variables -/

variable {p : Fin 8 → Fin 3 → ℝ}

theorem DomN.symm {u v c : ℕ} (h : DomN p u v c) : DomN p v u c := by
  intro j hj hjc
  rw [abs_sub_comm (P p u j), abs_sub_comm (P p u c)]
  exact h j hj hjc

theorem DomN.unique {u v c c' : ℕ} (h : DomN p u v c) (h' : DomN p u v c') (hc : c < 3)
    (hc' : c' < 3) : c = c' := by
  by_contra hne
  have h1 := h c' hc' (Ne.symm hne)
  have h2 := h' c hc hne
  linarith

theorem DomN.ne {u v c : ℕ} (h : DomN p u v c) : P p v c - P p u c ≠ 0 := by
  intro h0
  have := h (if c = 0 then 1 else 0) (by split <;> omega) (by split <;> omega)
  rw [h0, abs_zero] at this
  exact absurd this (not_lt.mpr (abs_nonneg _))

theorem assign_col {u v c : ℕ} (huv : u < v) (hv : v < 8) (hc : c < 3) :
    assign p (colVar u v c) = true ↔ DomN p u v c := by
  obtain ⟨hp, hlt⟩ := pairs_edgeIdx_aux (by omega) hv huv
  have hmin : min u v = u := by omega
  have hmax : max u v = v := by omega
  unfold assign colVar
  rw [hmin, hmax]
  have h1 : 1 ≤ 1 + 3 * edgeIdx u v + c ∧ 1 + 3 * edgeIdx u v + c ≤ 84 := by omega
  have h2 : (1 + 3 * edgeIdx u v + c - 1) / 3 = edgeIdx u v := by omega
  have h3 : (1 + 3 * edgeIdx u v + c - 1) % 3 = c := by omega
  rw [ite_eq_left h1, h2, h3, hp]
  simp only [decide_eq_true_eq]

theorem assign_col' {u v c : ℕ} (huv : u ≠ v) (hu : u < 8) (hv : v < 8) (hc : c < 3) :
    assign p (colVar u v c) = true ↔ DomN p u v c := by
  rcases Nat.lt_or_gt_of_ne huv with h | h
  · exact assign_col h hv hc
  · rw [colVar_comm, assign_col h hu hc]
    exact ⟨DomN.symm, DomN.symm⟩

theorem assign_sgn {u v : ℕ} (huv : u < v) (hv : v < 8) :
    assign p (sgnVar u v) = true ↔ ∃ c, c < 3 ∧ DomN p u v c ∧ P p u c < P p v c := by
  obtain ⟨hp, hlt⟩ := pairs_edgeIdx_aux (by omega) hv huv
  have hmin : min u v = u := by omega
  have hmax : max u v = v := by omega
  unfold assign sgnVar
  rw [hmin, hmax]
  have h0 : ¬ (1 ≤ 85 + edgeIdx u v ∧ 85 + edgeIdx u v ≤ 84) := by omega
  have h1 : 85 ≤ 85 + edgeIdx u v ∧ 85 + edgeIdx u v ≤ 112 := by omega
  have h2 : 85 + edgeIdx u v - 85 = edgeIdx u v := by omega
  rw [ite_eq_right h0, ite_eq_left h1, h2, hp]
  simp only [decide_eq_true_eq]

/-- Positive orientation of the edge `{u, v}` (`u < v`) in colour `c`. -/
theorem assign_sgn_col {u v c : ℕ} (huv : u < v) (hv : v < 8) (hc : c < 3) (hd : DomN p u v c) :
    assign p (sgnVar u v) = true ↔ 0 < P p v c - P p u c := by
  rw [assign_sgn huv hv]
  constructor
  · rintro ⟨c', hc', hd', hlt⟩
    rw [DomN.unique hd hd' hc hc']; linarith
  · intro hpos; exact ⟨c, hc, hd, by linarith⟩

theorem sgnR_true : sgnR true = 1 := rfl
theorem sgnR_false : sgnR false = -1 := rfl

/-- If the sign variable of `{x, y}` has the value `s xor (y < x)` then
`sgnR s * (P y c - P x c) > 0`. -/
theorem sgn_meaning {x y c : ℕ} (hxy : x ≠ y) (hx : x < 8) (hy : y < 8) (hc : c < 3)
    (hd : DomN p x y c) (s : Bool) (hs : assign p (sgnVar x y) = (s ^^ decide (y < x))) :
    0 < sgnR s * (P p y c - P p x c) := by
  have hne := DomN.ne hd
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · have hn : decide (y < x) = false := decide_eq_false (by omega)
    rw [hn, Bool.xor_false] at hs
    have key := assign_sgn_col h hy hc hd
    cases s
    · rw [sgnR_false]
      have : ¬ 0 < P p y c - P p x c := fun hp => by rw [← key, hs] at hp; cases hp
      rcases lt_or_eq_of_le (not_lt.mp this) with h' | h'
      · linarith
      · exact absurd h' hne
    · rw [sgnR_true, one_mul]; exact key.mp hs
  · have hn : decide (y < x) = true := decide_eq_true h
    rw [hn, Bool.xor_true, sgnVar_comm] at hs
    have key := assign_sgn_col h hx hc hd.symm
    cases s
    · rw [sgnR_false]
      have := key.mp hs
      linarith
    · rw [sgnR_true, one_mul]
      have : ¬ 0 < P p x c - P p y c := fun hp => by rw [← key, hs] at hp; cases hp
      rcases lt_or_eq_of_le (not_lt.mp this) with h' | h'
      · linarith
      · exact absurd (by linarith) hne

/-! ### From `Fin` dominance to the natural-number version -/

theorem P_fin (u : Fin 8) (c : Fin 3) : P p u c = p u c := by
  unfold P; rw [dite_eq_left ⟨u.isLt, c.isLt⟩]

theorem domN_of_dom {u v : Fin 8} {k : Fin 3} (h : Dom (p v - p u) k) : DomN p u v k := by
  intro j hj hjk
  have := h ⟨j, hj⟩ (fun e => hjk (by rw [← e]))
  simp only [Pi.sub_apply] at this
  rw [show P p v j = p v ⟨j, hj⟩ from P_fin v ⟨j, hj⟩, show P p u j = p u ⟨j, hj⟩ from P_fin u ⟨j, hj⟩,
    P_fin, P_fin]
  exact this

/-! ### Soundness of each clause family -/

theorem sound_alo (hg : Good p) {u v : ℕ} (huv : u < v) (hv : v < 8) :
    Sat (assign p) (Prov.alo u v).clause := by
  obtain ⟨k, hk⟩ := hg.dom ⟨u, by omega⟩ ⟨v, hv⟩ (fun e => by simp [Fin.ext_iff] at e; omega)
  have hd := domN_of_dom hk
  apply sat_of_mem (l := pos (colVar u v k))
  · simp only [Prov.clause]
    fin_cases k <;> simp
  · rw [litVal_pos, assign_col huv hv k.isLt]; exact hd

theorem sound_amo {u v a b : ℕ} (huv : u < v) (hv : v < 8) (hab : a < b) (hb : b < 3) :
    Sat (assign p) (Prov.amo u v a b).clause := by
  simp only [Prov.clause]
  by_cases ha' : DomN p u v a
  · apply sat_of_mem (l := neg (colVar u v b)) (by simp)
    rw [litVal_neg', Bool.not_eq_true', ← Bool.not_eq_true, assign_col huv hv hb]
    intro hb'
    exact absurd (DomN.unique ha' hb' (by omega) hb) (by omega)
  · apply sat_of_mem (l := neg (colVar u v a)) (by simp)
    rw [litVal_neg', Bool.not_eq_true', ← Bool.not_eq_true, assign_col huv hv (by omega)]
    exact ha'

theorem sound_cut (hg : Good p) {S k u v : ℕ} (hS0 : 0 < S) (hS : S < 255) (hk : k < 3)
    (huv : u < v) (hv : v < 8) : Sat (assign p) (Prov.cut S k u v).clause := by
  obtain ⟨⟨a0, ha0⟩, hSa⟩ := testBit_some_fin ⟨S, by omega⟩ hS0
  obtain ⟨⟨b0, hb0⟩, hSb⟩ := testBit_none_fin ⟨S, hS⟩
  let T : Finset (Fin 8) := Finset.univ.filter fun a => S.testBit a.val = true
  obtain ⟨a, haT, b, hbT, hn1, hn2, hd⟩ := hg.cut ⟨u, by omega⟩ ⟨v, hv⟩
    (fun e => by simp [Fin.ext_iff] at e; omega) T ⟨k, hk⟩
    ⟨⟨a0, ha0⟩, by simpa [T] using hSa⟩ ⟨⟨b0, hb0⟩, by simpa [T] using hSb⟩
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at haT hbT
  have hab : a.val ≠ b.val := fun e => by rw [Fin.ext e] at haT; rw [haT] at hbT; cases hbT
  have hdN : DomN p a b k := domN_of_dom hd
  simp only [Fin.ext_iff] at hn1 hn2
  apply sat_of_mem (l := pos (colVar (min a.val b.val) (max a.val b.val) k))
  · simp only [Prov.clause, List.mem_map, List.mem_filter]
    refine ⟨(min a.val b.val, max a.val b.val), ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.lt_or_gt_of_ne hab with h | h
      · rw [Nat.min_eq_left h.le, Nat.max_eq_right h.le]; exact mem_pairs_fin a b h
      · rw [Nat.min_eq_right h.le, Nat.max_eq_left h.le]; exact mem_pairs_fin b a h
    · rcases Nat.lt_or_gt_of_ne hab with h | h
      · rw [Nat.min_eq_left h.le, Nat.max_eq_right h.le]
        simp [haT, hbT]; omega
      · rw [Nat.min_eq_right h.le, Nat.max_eq_left h.le]
        simp [haT, hbT]; omega
  · rw [litVal_pos, colVar_minmax, assign_col' hab a.isLt b.isLt hk]
    exact hdN

theorem sound_anchor (ha : Anchored p) {j : ℕ} (hj : j < 11) :
    Sat (assign p) (Prov.anchor j).clause := by
  have col : ∀ (c : Fin 8) (k : Fin 3), 0 < c.val → Dom (p c - p 0) k →
      litVal (assign p) (pos (colVar 0 c k)) = true := by
    intro c k hlt hd
    rw [litVal_pos, assign_col hlt c.isLt k.isLt]
    exact domN_of_dom hd
  have sg : ∀ (c : Fin 8) (k : Fin 3), 0 < c.val → Dom (p c - p 0) k → p 0 k < p c k →
      litVal (assign p) (pos (sgnVar 0 c)) = true := by
    intro c k hc hd hlt
    rw [litVal_pos, assign_sgn hc c.isLt]
    refine ⟨k, k.isLt, domN_of_dom hd, ?_⟩
    rw [show P p 0 k = p 0 k from P_fin 0 k, P_fin]; exact hlt
  simp only [Prov.clause]
  interval_cases j
  · exact sat_of_mem (List.mem_singleton_self _) (col 1 0 (by decide) ha.c1)
  · exact sat_of_mem (List.mem_singleton_self _) (col 2 0 (by decide) ha.c2)
  · exact sat_of_mem (List.mem_singleton_self _) (col 3 0 (by decide) ha.c3)
  · exact sat_of_mem (List.mem_singleton_self _) (col 4 1 (by decide) ha.c4)
  · exact sat_of_mem (List.mem_singleton_self _) (col 5 1 (by decide) ha.c5)
  · exact sat_of_mem (List.mem_singleton_self _) (col 6 2 (by decide) ha.c6)
  · exact sat_of_mem (List.mem_singleton_self _) (col 7 2 (by decide) ha.c7)
  · exact sat_of_mem (List.mem_singleton_self _) (sg 1 0 (by decide) ha.c1 ha.s1)
  · exact sat_of_mem (List.mem_singleton_self _) (sg 2 0 (by decide) ha.c2 ha.s2)
  · exact sat_of_mem (List.mem_singleton_self _) (sg 4 1 (by decide) ha.c4 ha.s4)
  · exact sat_of_mem (List.mem_singleton_self _) (sg 6 2 (by decide) ha.c6 ha.s6)

/-! ### Patterns -/

theorem sgnR_mul (s b : Bool) : sgnR s * sgnR (!b) = sgnR (s ^^ b) := by
  cases s <;> cases b <;> simp [sgnR]

theorem abs_sgnR (b : Bool) : |sgnR b| = 1 := by
  cases b <;> simp [sgnR]

theorem getD_ne_of_nodup {f : List ℕ} (hl : f.length = 4) (hn : f.Nodup) {a b : ℕ} (ha : a < 4)
    (hb : b < 4) (hab : a ≠ b) : f.getD a 0 ≠ f.getD b 0 := by
  rw [← List.getElem_eq_getD (l := f) (i := a) (h := by omega) 0,
    ← List.getElem_eq_getD (l := f) (i := b) (h := by omega) 0]
  intro e
  exact hab ((List.Nodup.getElem_inj hn).mp e)

theorem getD_lt {f : List ℕ} (hl : f.length = 4) (hall : f.all (fun x => decide (x < 8)) = true)
    {a : ℕ} (ha : a < 4) : f.getD a 0 < 8 := by
  rw [← List.getElem_eq_getD (l := f) (i := a) (h := by omega) 0]
  have := List.all_eq_true.mp hall _ (List.getElem_mem (show a < f.length by omega))
  simpa using this

theorem sound_pat {r : ℕ} {f : List ℕ} {t eps : ℕ} (hr : r < 7) (ht : t < 6)
    (hl : f.length = 4) (hall : f.all (fun x => decide (x < 8)) = true) (hn : f.Nodup) :
    Sat (assign p) (Prov.pat r f t eps).clause := by
  unfold Sat
  by_contra hno
  rw [Bool.not_eq_true, List.any_eq_false] at hno
  let τ := perms3.getD t []
  let Q : ℕ → ℕ → ℝ := fun x c => sgnR (!eps.testBit c) * P p (f.getD x 0) (τ.getD c 0)
  apply rep_infeasible r hr Q
  intro e he
  obtain ⟨hi, hc⟩ := reps_fin ⟨r, hr⟩ e he
  obtain ⟨ha4, hb4, hab⟩ := e4_fin ⟨e.1, hi⟩
  simp only [Fin.val_mk] at ha4 hb4 hab
  set a := (e4.getD e.1 (0, 0)).1 with hA
  set b := (e4.getD e.1 (0, 0)).2 with hB
  set x := f.getD a 0 with hX
  set y := f.getD b 0 with hY
  set c' := τ.getD e.2.1 0 with hC
  set s' := e.2.2 ^^ eps.testBit e.2.1 with hS
  have hpe : patEntry f τ eps e = [neg (colVar x y c'),
      if (s' ^^ decide (y < x)) then neg (sgnVar x y) else pos (sgnVar x y)] := rfl
  have hmem : ∀ l ∈ patEntry f τ eps e, l ∈ (Prov.pat r f t eps).clause := by
    intro l hl'
    simp only [Prov.clause, List.mem_flatMap]
    exact ⟨e, he, hl'⟩
  have hcol := hno (neg (colVar x y c')) (hmem _ (by rw [hpe]; exact List.mem_cons_self))
  have hsgn := hno _ (hmem _ (by rw [hpe]; exact List.mem_cons_of_mem _ List.mem_cons_self))
  have hxy : x ≠ y := getD_ne_of_nodup hl hn ha4 hb4 hab
  have hx8 : x < 8 := getD_lt hl hall ha4
  have hy8 : y < 8 := getD_lt hl hall hb4
  have hc'3 : c' < 3 := (perms3_aux ht hc (c' := 0) (by omega)).1
  rw [litVal_neg', Bool.not_eq_true', Bool.not_eq_false, assign_col' hxy hx8 hy8 hc'3] at hcol
  have hd : DomN p x y c' := hcol
  have hsv : assign p (sgnVar x y) = (s' ^^ decide (y < x)) := by
    revert hsgn
    cases hsv' : (s' ^^ decide (y < x))
    · simp [litVal_pos]
    · simp [litVal_neg']
  have hpos := sgn_meaning hxy hx8 hy8 hc'3 hd _ hsv
  have habs : |P p y c' - P p x c'| = sgnR s' * (P p y c' - P p x c') := by
    have h2 : |sgnR s' * (P p y c' - P p x c')| = |P p y c' - P p x c'| := by
      rw [abs_mul, abs_sgnR, one_mul]
    rw [← h2, abs_of_pos hpos]
  -- now the entry's inequalities
  intro j hj hjc
  have hτj : τ.getD j 0 < 3 ∧ τ.getD j 0 ≠ c' := by
    refine ⟨(perms3_aux ht hj (c' := 0) (by omega)).1, fun h => hjc ?_⟩
    exact (perms3_aux ht hj hc).2 h
  have hdj := hd _ hτj.1 hτj.2
  show |Q b j - Q a j| < sgnR e.2.2 * (Q b e.2.1 - Q a e.2.1)
  have hQj : Q b j - Q a j = sgnR (!eps.testBit j) * (P p y (τ.getD j 0) - P p x (τ.getD j 0)) := by
    simp only [Q]; ring
  have hQc : sgnR e.2.2 * (Q b e.2.1 - Q a e.2.1) = sgnR s' * (P p y c' - P p x c') := by
    simp only [Q]; rw [hS, ← sgnR_mul]; ring
  rw [hQj, hQc, abs_mul, abs_sgnR, one_mul, ← habs]
  exact hdj

/-- Every clause of the instance holds under the induced assignment. -/
theorem base_of_good (hg : Good p) (ha : Anchored p) : Base (assign p) := by
  intro π hv
  cases π with
  | alo u v =>
    simp only [Prov.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact sound_alo hg hv.1 hv.2
  | amo u v a b =>
    simp only [Prov.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact sound_amo hv.1.1.1 hv.1.1.2 hv.1.2 hv.2
  | cut S k u v =>
    simp only [Prov.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact sound_cut hg hv.1.1.1.1 hv.1.1.1.2 hv.1.1.2 hv.1.2 hv.2
  | pat r f t eps =>
    simp only [Prov.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    exact sound_pat hv.1.1.1.1.1 hv.1.1.1.1.2 hv.1.1.2 hv.1.2 hv.2
  | anchor j =>
    simp only [Prov.valid, decide_eq_true_eq] at hv
    exact sound_anchor ha hv

end K8
