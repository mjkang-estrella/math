import C374966Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# MathDB 374966 — the corolla preorder `τ = t₃` and its lattice-point poset `P_τ`

Ground set `E = Fin 3`; vertex `0` is the root, above the two incomparable leaves `1, 2`.
`Q_τ = {x ≥ 0, ∑_{e ∈ I} x_e ≤ |I| for all order ideals I}`; `P_τ` = its integer points,
ordered componentwise, ranked by coordinate sum.
-/

namespace C374966

open Finset MvPolynomial

/-- The corolla preorder: `cor i j` means `i ≤_τ j`. -/
abbrev cor (i j : Fin 3) : Prop := i = j ∨ j = 0

theorem cor_refl (i : Fin 3) : cor i i := Or.inl rfl
theorem cor_trans : ∀ i j k : Fin 3, cor i j → cor j k → cor i k := by decide
theorem cor_antisymm : ∀ i j : Fin 3, cor i j → cor j i → i = j := by decide
theorem cor_shape : cor 1 0 ∧ cor 2 0 ∧ ¬ cor 1 2 ∧ ¬ cor 2 1 ∧ ¬ cor 0 1 ∧ ¬ cor 0 2 := by
  decide

/-- Order ideals of a preorder (source §2.2): `b ∈ I`, `a ≤ b` imply `a ∈ I`. -/
abbrev IsIdeal (I : Finset (Fin 3)) : Prop := ∀ b ∈ I, ∀ a : Fin 3, cor a b → a ∈ I

theorem ideals_iff : ∀ I : Finset (Fin 3),
    IsIdeal I ↔ I = ∅ ∨ I = {1} ∨ I = {2} ∨ I = {1, 2} ∨ I = Finset.univ := by
  decide

theorem ideal_one : IsIdeal {1} := by decide
theorem ideal_two : IsIdeal {2} := by decide
theorem ideal_univ : IsIdeal Finset.univ := by decide

/-- Literal integer points of the preorder polytope `Q_τ`. -/
def Qcor (v : Fin 3 → ℤ) : Prop :=
  (∀ e, 0 ≤ v e) ∧ ∀ I : Finset (Fin 3), IsIdeal I → ∑ e ∈ I, v e ≤ (I.card : ℤ)

/-- The lattice-point poset `P_τ` (subtype order of the componentwise order on `ℤ^3`). -/
abbrev P := {v : Fin 3 → ℤ // Qcor v}

theorem Qcor_iff (v : Fin 3 → ℤ) :
    Qcor v ↔ 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ 0 ≤ v 2 ∧ v 1 ≤ 1 ∧ v 2 ≤ 1 ∧ v 0 + v 1 + v 2 ≤ 3 := by
  constructor
  · rintro ⟨hnn, hI⟩
    have h1 := hI {1} ideal_one
    have h2 := hI {2} ideal_two
    have h3 := hI Finset.univ ideal_univ
    rw [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one] at h1 h2
    rw [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin] at h3
    exact ⟨hnn 0, hnn 1, hnn 2, h1, h2, by exact_mod_cast h3⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    refine ⟨fun e => ?_, fun I hI => ?_⟩
    · fin_cases e
      · exact h0
      · exact h1
      · exact h2
    · rcases (ideals_iff I).1 hI with rfl | rfl | rfl | rfl | rfl
      · simp
      · rw [Finset.sum_singleton, Finset.card_singleton]; omega
      · rw [Finset.sum_singleton, Finset.card_singleton]; omega
      · have hc : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
        rw [Finset.sum_pair (by decide), hc]; omega
      · rw [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin]; omega

/-- The twelve points (coordinates: root, leaf 1, leaf 2). -/
def ptsL : List (Fin 3 → ℤ) :=
  [![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![2, 0, 0], ![1, 1, 0], ![1, 0, 1],
   ![0, 1, 1], ![3, 0, 0], ![2, 1, 0], ![2, 0, 1], ![1, 1, 1]]

def pts : Finset (Fin 3 → ℤ) := ⟨ptsL, Multiset.coe_nodup.2 (by decide)⟩

theorem pts_sound : ∀ v ∈ pts,
    0 ≤ v 0 ∧ 0 ≤ v 1 ∧ 0 ≤ v 2 ∧ v 1 ≤ 1 ∧ v 2 ≤ 1 ∧ v 0 + v 1 + v 2 ≤ 3 := by
  decide

/-- The executable twelve-point finset is exactly the literal ideal-inequality domain. -/
theorem mem_pts (v : Fin 3 → ℤ) : v ∈ pts ↔ Qcor v := by
  rw [Qcor_iff]
  constructor
  · exact pts_sound v
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c : ℤ, v = ![a, b, c] :=
      ⟨v 0, v 1, v 2, by funext i; fin_cases i <;> rfl⟩
    change 0 ≤ a at h0
    change 0 ≤ b at h1
    change 0 ≤ c at h2
    change b ≤ 1 at h3
    change c ≤ 1 at h4
    change a + b + c ≤ 3 at h5
    have ha : a ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> first | decide | omega

instance instFintypeP : Fintype P := Fintype.subtype pts mem_pts

instance instDecLEP : DecidableLE P := fun a b =>
  decidable_of_iff (∀ i, a.1 i ≤ b.1 i) Iff.rfl

noncomputable instance instDecLTP : DecidableLT P := fun _ _ => Classical.dec _

noncomputable instance instLFOP : LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder

theorem card_P : Fintype.card P = 12 :=
  (Fintype.card_of_subtype pts mem_pts).trans (by decide)

/-- Rank on the executable side: coordinate sum. -/
def rkz (v : Fin 3 → ℤ) : ℕ := (v 0 + v 1 + v 2).toNat

/-- The rank function of `P_τ`: coordinate sum. -/
def rk (a : P) : ℕ := rkz a.1

abbrev le3 (v w : Fin 3 → ℤ) : Prop := v 0 ≤ w 0 ∧ v 1 ≤ w 1 ∧ v 2 ≤ w 2

/-- The order of `P_τ` is the componentwise order. -/
theorem le_iff (a b : P) : a ≤ b ↔ le3 a.1 b.1 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

/-- `P_τ` is down-closed between its points: the box between two points lies in `Q_τ`. -/
theorem down_closed (a b : P) (w : Fin 3 → ℤ) (h : ∀ i, a.1 i ≤ w i ∧ w i ≤ b.1 i) :
    Qcor w := by
  have ha := (Qcor_iff a.1).1 a.2
  have hb := (Qcor_iff b.1).1 b.2
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  exact (Qcor_iff w).2 ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Every interval of `P_τ` is the product of its coordinate chains. -/
def intervalIso (a b : P) : Set.Icc a b ≃o ((i : Fin 3) → Set.Icc (a.1 i) (b.1 i)) where
  toFun z i := ⟨z.1.1 i, z.2.1 i, z.2.2 i⟩
  invFun w := ⟨⟨fun i => (w i).1, down_closed a b _ fun i => ⟨(w i).2.1, (w i).2.2⟩⟩,
    fun i => (w i).2.1, fun i => (w i).2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The bottom point `000`. -/
def botP : P := ⟨![0, 0, 0], (mem_pts _).1 (by decide)⟩

theorem botP_le (a : P) : botP ≤ a := by
  have ha := (Qcor_iff a.1).1 a.2
  exact (le_iff _ _).2 (show (0 : ℤ) ≤ a.1 0 ∧ (0 : ℤ) ≤ a.1 1 ∧ (0 : ℤ) ≤ a.1 2 by omega)

theorem rk_botP : rk botP = 0 := rfl

theorem rk_lt_four (a : P) : rk a < 4 := by
  have h := (Qcor_iff a.1).1 a.2
  unfold rk rkz
  omega

theorem rk_strictMono : StrictMono rk := by
  intro a b hab
  have hle := (le_iff a b).1 hab.le
  have hne : a.1 ≠ b.1 := fun h => hab.ne (Subtype.ext h)
  have ha := (Qcor_iff a.1).1 a.2
  have hb := (Qcor_iff b.1).1 b.2
  have hd : a.1 0 ≠ b.1 0 ∨ a.1 1 ≠ b.1 1 ∨ a.1 2 ≠ b.1 2 := by
    by_contra hc
    apply hne
    funext i
    fin_cases i
    · by_contra h; exact hc (Or.inl h)
    · by_contra h; exact hc (Or.inr (Or.inl h))
    · by_contra h; exact hc (Or.inr (Or.inr h))
  unfold rk rkz
  omega

theorem exists_between {a b : P} (hab : a ≤ b) (hr : rk a + 2 ≤ rk b) :
    ∃ c : P, a < c ∧ c < b := by
  have hle : le3 a.1 b.1 := (le_iff a b).1 hab
  have ha := (Qcor_iff a.1).1 a.2
  have hb := (Qcor_iff b.1).1 b.2
  have hr' : (a.1 0 + a.1 1 + a.1 2).toNat + 2 ≤ (b.1 0 + b.1 1 + b.1 2).toNat := hr
  have key : ∀ x y z : ℤ, a.1 0 ≤ x ∧ a.1 1 ≤ y ∧ a.1 2 ≤ z →
      x ≤ b.1 0 ∧ y ≤ b.1 1 ∧ z ≤ b.1 2 →
      x + y + z = a.1 0 + a.1 1 + a.1 2 + 1 → ∃ c : P, a < c ∧ c < b := by
    intro x y z k1 k2 hs
    have hz : ∀ i, a.1 i ≤ ![x, y, z] i ∧ ![x, y, z] i ≤ b.1 i := by
      intro i
      fin_cases i
      · exact ⟨k1.1, k2.1⟩
      · exact ⟨k1.2.1, k2.2.1⟩
      · exact ⟨k1.2.2, k2.2.2⟩
    refine ⟨⟨![x, y, z], down_closed a b _ hz⟩, lt_of_le_of_ne ?_ ?_, lt_of_le_of_ne ?_ ?_⟩
    · exact (le_iff _ _).2 k1
    · intro h
      have e0 := congrFun (congrArg Subtype.val h) 0
      have e1 := congrFun (congrArg Subtype.val h) 1
      have e2 := congrFun (congrArg Subtype.val h) 2
      change a.1 0 = x at e0
      change a.1 1 = y at e1
      change a.1 2 = z at e2
      omega
    · exact (le_iff _ _).2 k2
    · intro h
      have e0 := congrFun (congrArg Subtype.val h) 0
      have e1 := congrFun (congrArg Subtype.val h) 1
      have e2 := congrFun (congrArg Subtype.val h) 2
      change x = b.1 0 at e0
      change y = b.1 1 at e1
      change z = b.1 2 at e2
      omega
  obtain ⟨h0, h1, h2⟩ := hle
  by_cases c0 : a.1 0 < b.1 0
  · exact key (a.1 0 + 1) (a.1 1) (a.1 2) ⟨by omega, le_refl _, le_refl _⟩
      ⟨by omega, h1, h2⟩ (by omega)
  · by_cases c1 : a.1 1 < b.1 1
    · exact key (a.1 0) (a.1 1 + 1) (a.1 2) ⟨le_refl _, by omega, le_refl _⟩
        ⟨h0, by omega, h2⟩ (by omega)
    · by_cases c2 : a.1 2 < b.1 2
      · exact key (a.1 0) (a.1 1) (a.1 2 + 1) ⟨le_refl _, le_refl _, by omega⟩
          ⟨h0, h1, by omega⟩ (by omega)
      · exfalso
        omega

/-- Grading: covers raise the rank by exactly one. -/
theorem rk_covBy {a b : P} (h : a ⋖ b) : rk b = rk a + 1 := by
  have h1 := rk_strictMono h.lt
  by_contra hne
  obtain ⟨c, hac, hcb⟩ := exists_between h.lt.le (by omega)
  exact h.2 hac hcb

/-- Grading: every maximal element of `P_τ` has rank `3`. -/
theorem rk_of_maximal (a : P) (hmax : ∀ b : P, a ≤ b → b = a) : rk a = 3 := by
  have ha := (Qcor_iff a.1).1 a.2
  by_contra hne
  have hne' : ¬ (a.1 0 + a.1 1 + a.1 2).toNat = 3 := hne
  have hq : Qcor ![a.1 0 + 1, a.1 1, a.1 2] := by
    rw [Qcor_iff]
    show 0 ≤ a.1 0 + 1 ∧ 0 ≤ a.1 1 ∧ 0 ≤ a.1 2 ∧ a.1 1 ≤ 1 ∧ a.1 2 ≤ 1 ∧
      a.1 0 + 1 + a.1 1 + a.1 2 ≤ 3
    omega
  have hb := hmax ⟨_, hq⟩ ((le_iff _ _).2
    (show a.1 0 ≤ a.1 0 + 1 ∧ a.1 1 ≤ a.1 1 ∧ a.1 2 ≤ a.1 2 by omega))
  have e0 := congrFun (congrArg Subtype.val hb) 0
  change a.1 0 + 1 = a.1 0 at e0
  omega

/-! ### Möbius function of `P_τ` (box formula) -/

/-- One-dimensional chain Möbius values. -/
def gz (t : ℤ) : ℤ := if t = 0 then 1 else if t = 1 then -1 else 0

def fz (v w : Fin 3 → ℤ) : ℤ := gz (w 0 - v 0) * gz (w 1 - v 1) * gz (w 2 - v 2)

/-- Candidate Möbius function: product of coordinate chain Möbius values. -/
def fP (a b : P) : ℚ := ∏ i : Fin 3, ((gz (b.1 i - a.1 i) : ℤ) : ℚ)

theorem fP_cast (a b : P) : fP a b = (fz a.1 b.1 : ℚ) := by
  simp only [fP, Fin.prod_univ_three, fz, Int.cast_mul]

theorem fP_self (a : P) : fP a a = 1 := by
  simp [fP, gz]

theorem sum1 (a b : ℤ) (h : a ≤ b) :
    ∑ t ∈ Finset.Icc a b, ((gz (t - a) : ℤ) : ℚ) = if a = b then 1 else 0 := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · rw [Finset.Icc_self, Finset.sum_singleton, sub_self, ite_eq_left rfl]
    norm_num [gz]
  · rw [ite_eq_right (ne_of_lt hlt)]
    rw [Finset.sum_eq_add a (a + 1) (by omega)]
    · rw [sub_self, add_sub_cancel_left]
      norm_num [gz]
    · intro c hc hca
      rw [Finset.mem_Icc] at hc
      obtain ⟨hc1, hc2⟩ := hca
      have e1 : ¬ (c - a = 0) := by omega
      have e2 : ¬ (c - a = 1) := by omega
      rw [gz, ite_eq_right e1, ite_eq_right e2, Int.cast_zero]
    · intro ha
      exact absurd (Finset.mem_Icc.2 ⟨le_refl a, h⟩) ha
    · intro hb
      exact absurd (Finset.mem_Icc.2 ⟨by omega, by omega⟩) hb

theorem sum_Icc_P (a b : P) (F : (Fin 3 → ℤ) → ℚ) :
    ∑ z ∈ Finset.Icc a b, F z.1
      = ∑ w ∈ Fintype.piFinset (fun i => Finset.Icc (a.1 i) (b.1 i)), F w := by
  have hmap : (Finset.Icc a b).map (Function.Embedding.subtype Qcor)
      = Fintype.piFinset (fun i => Finset.Icc (a.1 i) (b.1 i)) := by
    ext w
    simp only [Finset.mem_map, Finset.mem_Icc, Fintype.mem_piFinset]
    constructor
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩ i
      exact ⟨h1 i, h2 i⟩
    · intro h
      exact ⟨⟨w, down_closed a b w h⟩, ⟨fun i => (h i).1, fun i => (h i).2⟩, rfl⟩
  rw [← hmap]
  exact (Finset.sum_map (Finset.Icc a b) (Function.Embedding.subtype Qcor) F).symm

theorem fP_sum (a b : P) (hab : a < b) : ∑ z ∈ Finset.Icc a b, fP a z = 0 := by
  have h1 : ∑ z ∈ Finset.Icc a b, fP a z
      = ∑ w ∈ Fintype.piFinset (fun i => Finset.Icc (a.1 i) (b.1 i)),
          ∏ i, ((gz (w i - a.1 i) : ℤ) : ℚ) :=
    sum_Icc_P a b (fun w => ∏ i, ((gz (w i - a.1 i) : ℤ) : ℚ))
  have h2 := (Finset.prod_univ_sum (fun i => Finset.Icc (a.1 i) (b.1 i))
      (fun i t => ((gz (t - a.1 i) : ℤ) : ℚ))).symm
  rw [h1, h2]
  have hle : ∀ i, a.1 i ≤ b.1 i := fun i => hab.le i
  obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
    by_contra hcon
    exact hab.ne (Subtype.ext (funext fun i => by by_contra h; exact hcon ⟨i, h⟩))
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [sum1 _ _ (hle i), ite_eq_right hi]

/-- The Möbius function of `P_τ` (pinned Mathlib `IncidenceAlgebra.mu`) is the box formula. -/
theorem mu_P (a b : P) (hab : a ≤ b) : IncidenceAlgebra.mu ℚ a b = (fz a.1 b.1 : ℚ) := by
  rw [mu_eq_of_sum fP fP_self fP_sum a b hab, fP_cast]

/-! ### The M-triangle of `P_τ` -/

theorem sum_P_pts (F : (Fin 3 → ℤ) → (Fin 3 → ℤ) → ℚ) :
    ∑ a : P, ∑ b : P, F a.1 b.1 = ∑ v ∈ pts, ∑ w ∈ pts, F v w := by
  rw [Finset.sum_subtype (F := instFintypeP) pts mem_pts]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_subtype (F := instFintypeP) pts mem_pts]

/-- Explicit integer coefficient sums over the twelve points. -/
def Tz (i j : ℕ) : ℤ := ∑ v ∈ pts, ∑ w ∈ pts,
  if rkz v = i ∧ rkz w = j then (if le3 v w then fz v w else 0) else 0

def tableP : List (List ℤ) := [[1, -3, 3, -1], [0, 3, -7, 5], [0, 0, 4, -8], [0, 0, 0, 4]]

def tPz (i j : ℕ) : ℤ := (tableP.getD i []).getD j 0

def tPq (i j : ℕ) : ℚ := (tPz i j : ℚ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem Tz_table : ∀ i j : Fin 4, Tz i j = tPz i j := by
  decide

theorem Tab_P (i j : ℕ) : Tab P rk i j = (Tz i j : ℚ) := by
  have hmu : ∀ a b : P,
      (if rk a = i ∧ rk b = j then (if a ≤ b then IncidenceAlgebra.mu ℚ a b else 0) else 0)
        = (((if rkz a.1 = i ∧ rkz b.1 = j then (if le3 a.1 b.1 then fz a.1 b.1 else 0)
            else 0 : ℤ)) : ℚ) := by
    intro a b
    by_cases h1 : rkz a.1 = i ∧ rkz b.1 = j
    · rw [ite_eq_left (show rk a = i ∧ rk b = j from h1), ite_eq_left h1]
      by_cases h2 : le3 a.1 b.1
      · have hab : a ≤ b := (le_iff a b).2 h2
        rw [ite_eq_left hab, ite_eq_left h2, mu_P a b hab]
      · rw [ite_eq_right (fun h => h2 ((le_iff a b).1 h)), ite_eq_right h2, Int.cast_zero]
    · rw [ite_eq_right (show ¬ (rk a = i ∧ rk b = j) from h1), ite_eq_right h1, Int.cast_zero]
  unfold Tab
  simp only [hmu]
  rw [sum_P_pts (fun v w => (((if rkz v = i ∧ rkz w = j then (if le3 v w then fz v w else 0)
      else 0 : ℤ)) : ℚ))]
  simp only [Tz, Int.cast_sum]

/-- `M_{P_τ}` equals the polynomial with the computed coefficient table. -/
theorem MP_eq_tab : Mtri P rk = tab tPq := by
  rw [Mtri_eq, ← regroup rk rk_lt_four
    (fun a b => if a ≤ b then IncidenceAlgebra.mu ℚ a b else 0)]
  apply tab_congr
  intro i hi j hj
  have hT : Tz i j = tPz i j := Tz_table ⟨i, hi⟩ ⟨j, hj⟩
  show Tab P rk i j = tPq i j
  rw [Tab_P, hT, tPq]

theorem tPz_vals : tPz 0 0 = 1 ∧ tPz 0 1 = -3 ∧ tPz 0 2 = 3 ∧ tPz 0 3 = -1 ∧
    tPz 1 0 = 0 ∧ tPz 1 1 = 3 ∧ tPz 1 2 = -7 ∧ tPz 1 3 = 5 ∧
    tPz 2 0 = 0 ∧ tPz 2 1 = 0 ∧ tPz 2 2 = 4 ∧ tPz 2 3 = -8 ∧
    tPz 3 0 = 0 ∧ tPz 3 1 = 0 ∧ tPz 3 2 = 0 ∧ tPz 3 3 = 4 := by
  decide

/-- `1 - 3y + 3y² - y³ + 3xy - 7xy² + 5xy³ + 4x²y² - 8x²y³ + 4x³y³`. -/
noncomputable def MP_lit : Pxy :=
  1 - 3 * X 1 + 3 * X 1 ^ 2 - X 1 ^ 3 + 3 * X 0 * X 1 - 7 * X 0 * X 1 ^ 2
    + 5 * X 0 * X 1 ^ 3 + 4 * X 0 ^ 2 * X 1 ^ 2 - 8 * X 0 ^ 2 * X 1 ^ 3 + 4 * X 0 ^ 3 * X 1 ^ 3

theorem tab_P_lit : tab tPq = MP_lit := by
  obtain ⟨e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33⟩ :=
    tPz_vals
  simp only [tab, tPq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33,
    Int.cast_zero, Int.cast_one, Int.cast_neg, Int.cast_ofNat,
    map_zero, map_one, map_neg, map_ofNat, MP_lit]
  ring

/-- The actual M-triangle of `P_τ`. -/
theorem Mtri_P_lit : Mtri P rk = MP_lit := MP_eq_tab.trans tab_P_lit

end C374966
