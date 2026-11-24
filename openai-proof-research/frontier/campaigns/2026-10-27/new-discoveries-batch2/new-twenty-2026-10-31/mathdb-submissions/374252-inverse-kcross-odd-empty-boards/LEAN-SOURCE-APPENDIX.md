# Lean source appendix for MathDB 374252

### `InverseKCross.lean`

```lean
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Choose
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Tauto
import Mathlib.Data.Nat.Find

namespace OddInverseKCross

open Finset

/-- The unmarked cells hit every interval of k board cells. -/
def Legal (k n : ℕ) (S : Finset ℕ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → a + k ≤ n + 1 → ∃ x ∈ S, a ≤ x ∧ x < a + k

theorem legal_mono {k n : ℕ} {S T : Finset ℕ} (h : S ⊆ T)
    (hS : Legal k n S) : Legal k n T := by
  intro a ha hb
  obtain ⟨x, hx, h₁, h₂⟩ := hS a ha hb
  exact ⟨x, h hx, h₁, h₂⟩

noncomputable def options (k n : ℕ) (S : Finset ℕ) : Finset ℕ := by
  classical
  exact S.filter (fun x => Legal k n (S.erase x))

theorem mem_options {k n x : ℕ} {S : Finset ℕ} :
    x ∈ options k n S ↔ x ∈ S ∧ Legal k n (S.erase x) := by
  classical
  simp [options]

private theorem exists_missing (s : Finset ℕ) : ∃ u : ℕ, u ∉ s := by
  refine ⟨s.sup id + 1, ?_⟩
  intro h
  have hb := Finset.le_sup (f := id) h
  simp only [id_eq] at hb
  omega

noncomputable def mex (s : Finset ℕ) : ℕ :=
  Nat.find (exists_missing s)

theorem mex_zero_iff (s : Finset ℕ) : mex s = 0 ↔ 0 ∉ s := by
  constructor
  · intro h
    have hn := Nat.find_spec (exists_missing s)
    change mex s ∉ s at hn
    simpa only [h] using hn
  · intro h
    have := Nat.find_min' (exists_missing s) h
    exact Nat.eq_zero_of_le_zero this

theorem mex_one_iff (s : Finset ℕ) : mex s = 1 ↔ 0 ∈ s ∧ 1 ∉ s := by
  constructor
  · intro h
    have h₀ : 0 ∈ s := by
      by_contra hh
      have := (mex_zero_iff s).2 hh
      omega
    have hn := Nat.find_spec (exists_missing s)
    change mex s ∉ s at hn
    exact ⟨h₀, h ▸ hn⟩
  · rintro ⟨h₀, h₁⟩
    have hu : mex s ≤ 1 := Nat.find_min' (exists_missing s) h₁
    have hl : mex s ≠ 0 := fun he => (mex_zero_iff s).1 he h₀
    omega

/-- Sprague–Grundy value of the actual deletion options. -/
noncomputable def grundy (k n : ℕ) (S : Finset ℕ) : ℕ :=
  mex ((options k n S).attach.image
    (fun x => grundy k n (S.erase x.1)))
termination_by S.card
decreasing_by
  apply Finset.card_erase_lt_of_mem
  exact (mem_options.mp x.2).1

def Next (k n : ℕ) (S : Finset ℕ) (b : Bool) (T : Finset ℕ) (c : Bool) : Prop :=
  (b = true ∧ c = false ∧ T = S) ∨
  ∃ x ∈ options k n S, c = b ∧ T = S.erase x

def mass (S : Finset ℕ) (b : Bool) : ℕ := S.card + b.toNat

theorem next_mass {k n : ℕ} {S T : Finset ℕ} {b c : Bool}
    (h : Next k n S b T c) : mass S b = mass T c + 1 := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩
  · rfl
  · have hc := Finset.card_erase_add_one (mem_options.mp hx).1
    simp only [mass]
    omega

theorem next_legal {k n : ℕ} {S T : Finset ℕ} {b c : Bool}
    (hS : Legal k n S) (h : Next k n S b T c) : Legal k n T := by
  rcases h with ⟨_, _, rfl⟩ | ⟨x, hx, _, rfl⟩
  · exact hS
  · exact (mem_options.mp hx).2

theorem next_subset {k n : ℕ} {S T : Finset ℕ} {b c : Bool}
    (h : Next k n S b T c) : T ⊆ S := by
  rcases h with ⟨_, _, rfl⟩ | ⟨x, _, _, rfl⟩
  · exact Subset.rfl
  · exact Finset.erase_subset _ _

def Loses (k n : ℕ) (S : Finset ℕ) (b : Bool) : Prop :=
  grundy k n S = b.toNat

theorem loses_iff {k n : ℕ} {S : Finset ℕ} {b : Bool} :
    Loses k n S b ↔
      ∀ T c, Next k n S b T c → ¬ Loses k n T c := by
  have hm (j : ℕ) :
      j ∈ ((options k n S).attach.image (fun x => grundy k n (S.erase x.1))) ↔
        ∃ x ∈ options k n S, grundy k n (S.erase x) = j := by
    simp [Finset.mem_image]
  have h₀ : grundy k n S = 0 ↔
      ¬ ∃ x ∈ options k n S, grundy k n (S.erase x) = 0 := by
    rw [grundy, mex_zero_iff, hm]
  have h₁ : grundy k n S = 1 ↔
      grundy k n S ≠ 0 ∧ ¬ ∃ x ∈ options k n S, grundy k n (S.erase x) = 1 := by
    rw [grundy, mex_one_iff]
    rw [← grundy, hm, hm, ne_eq, h₀, not_not]
  cases b with
  | false =>
      change grundy k n S = 0 ↔ _
      rw [h₀]
      constructor
      · intro hn T c h
        rcases h with ⟨hf, _, _⟩ | ⟨x, hx, rfl, rfl⟩
        · cases hf
        · exact fun h => hn ⟨x, hx, h⟩
      · intro h hn
        obtain ⟨x, hx, hg⟩ := hn
        exact h (S.erase x) false (Or.inr ⟨x, hx, rfl, rfl⟩) hg
  | true =>
      change grundy k n S = 1 ↔ _
      rw [h₁]
      constructor
      · rintro ⟨hg, hn⟩ T c h
        rcases h with ⟨_, rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩
        · exact hg
        · exact fun h => hn ⟨x, hx, h⟩
      · intro h
        refine ⟨h S false (Or.inl ⟨rfl, rfl, rfl⟩), ?_⟩
        rintro ⟨x, hx, hg⟩
        exact h (S.erase x) true (Or.inr ⟨x, hx, rfl, rfl⟩) hg


/-- A fixed terminal rank, enforced by an invariant restored on the defender's move. -/
structure Strategy (k n : ℕ) where
  rank : ℕ
  Ready : Finset ℕ → Prop
  lower : ∀ {S}, Ready S → rank ≤ S.card
  child_lower : ∀ {S b T c}, Ready S → Next k n S b T c → rank ≤ T.card
  step : ∀ {S b}, Ready S → rank < mass S b →
    ∃ T c, Next k n S b T c ∧ Ready T
  reply : ∀ {S b T c}, Ready S → Next k n S b T c → rank < mass T c →
    ∃ U d, Next k n T c U d ∧ Ready U

/-- A position is terminal when neither a board move nor an extra move is available. -/
def Terminal (k n : ℕ) (S : Finset ℕ) (b : Bool) : Prop :=
  ¬ ∃ T c, Next k n S b T c

private theorem terminal_flag {k n S b} (h : Terminal k n S b) : b = false := by
  cases b
  · rfl
  · exact (h ⟨S, false, Or.inl ⟨rfl, rfl, rfl⟩⟩).elim

theorem Strategy.terminal_ready (C : Strategy k n) {S b}
    (hS : C.Ready S) (ht : Terminal k n S b) : S.card = C.rank := by
  have hlo := C.lower hS
  obtain rfl := terminal_flag ht
  have hup : S.card ≤ C.rank := by
    by_contra hn
    obtain ⟨T, c, hnext, _⟩ := C.step (b := false) hS (by simpa [mass] using lt_of_not_ge hn)
    exact ht ⟨T, c, hnext⟩
  exact le_antisymm hup hlo

theorem Strategy.terminal_child (C : Strategy k n) {S b T c}
    (hS : C.Ready S) (hnext : Next k n S b T c) (ht : Terminal k n T c) :
    T.card = C.rank := by
  have hlo := C.child_lower hS hnext
  obtain rfl := terminal_flag ht
  have hup : T.card ≤ C.rank := by
    by_contra hn
    obtain ⟨U, d, hreply, _⟩ := C.reply hS hnext (by simpa [mass] using lt_of_not_ge hn)
    exact ht ⟨U, d, hreply⟩
  exact le_antisymm hup hlo

theorem Strategy.loses (C : Strategy k n) {S b} (hS : C.Ready S) :
    Loses k n S b ↔ (mass S b - C.rank) % 2 = 0 := by
  classical
  induction hm : mass S b using Nat.strong_induction_on generalizing S b with
  | h M ih =>
    have hlo := C.lower hS
    have hMB : S.card ≤ M := by
      rw [← hm]
      exact Nat.le_add_right _ _
    constructor
    · intro hL
      by_contra hOdd
      have he : C.rank < mass S b := by omega
      obtain ⟨T, c, hnext, hT⟩ := C.step hS he
      have hdec := next_mass hnext
      have hparity : (mass T c - C.rank) % 2 = 0 := by omega
      have hlose := (ih _ (by omega) hT rfl).2 hparity
      exact (loses_iff.mp hL) T c hnext hlose
    · intro hEven
      apply loses_iff.mpr
      intro T c hnext hL
      have hT := C.child_lower hS hnext
      have hchild : T.card ≤ mass T c := Nat.le_add_right _ _
      have hdec := next_mass hnext
      have he : C.rank < mass T c := by omega
      obtain ⟨U, d, hreply, hU⟩ := C.reply hS hnext he
      have hdec' := next_mass hreply
      have hparity : (mass U d - C.rank) % 2 = 0 := by omega
      have hlose := (ih _ (by omega) hU rfl).2 hparity
      exact (loses_iff.mp hL) U d hreply hlose

theorem Strategy.grundy_eq (C : Strategy k n) {S} (hS : C.Ready S) :
    grundy k n S = (S.card - C.rank) % 2 := by
  have h0 := C.loses (b := false) hS
  have h1 := C.loses (b := true) hS
  change grundy k n S = 0 ↔ (S.card + 0 - C.rank) % 2 = 0 at h0
  change grundy k n S = 1 ↔ (S.card + 1 - C.rank) % 2 = 0 at h1
  have hl := C.lower hS
  by_cases h : (S.card - C.rank) % 2 = 0
  · rw [h]
    apply h0.mpr
    omega
  · have hodd : (S.card - C.rank) % 2 = 1 := by omega
    rw [hodd]
    apply h1.mpr
    omega


/-- Local supports, redundant disjoint reserves, and the global gluing rule. -/
structure BlockSystem (k n : ℕ) where
  blocks : ℕ
  slots : ℕ
  rank : ℕ
  cells : Fin blocks → Finset ℕ
  high : Fin blocks → Finset ℕ
  reserve : Fin blocks → Fin slots → Finset ℕ
  Good : Fin blocks → Finset ℕ → Prop
  high_subset : ∀ j, high j ⊆ cells j
  reserve_subset : ∀ j i, reserve j i ⊆ cells j
  blocks_disjoint : ∀ ⦃j l⦄, j ≠ l → Disjoint (cells j) (cells l)
  reserves_disjoint : ∀ j ⦃i a⦄, i ≠ a → Disjoint (reserve j i) (reserve j a)
  high_reserve : ∀ j i, Disjoint (high j) (reserve j i)
  reserve_good : ∀ j i, Good j (reserve j i)
  finished : ∀ {S}, Legal k n S → ∀ j, Disjoint S (high j) →
    ∃ U ⊆ S, Good j U
  glue : ∀ {S}, (∀ j, ∃ U ⊆ S, Good j U) →
    ∃ U ⊆ S, U.card = rank ∧ Legal k n U ∧ ∀ j, Disjoint U (high j)

namespace BlockSystem

variable (B : BlockSystem k n)

def live (S : Finset ℕ) (j : Fin B.blocks) : Finset ℕ := S ∩ B.high j

def hcount (S : Finset ℕ) (j : Fin B.blocks) : ℕ := (B.live S j).card

def intact (S : Finset ℕ) (j : Fin B.blocks) : Finset (Fin B.slots) :=
  univ.filter (fun i => B.reserve j i ⊆ S)

theorem mem_intact {S : Finset ℕ} {j : Fin B.blocks} {i : Fin B.slots} :
    i ∈ B.intact S j ↔ B.reserve j i ⊆ S := by
  simp [intact]

private theorem live_erase (S : Finset ℕ) (j : Fin B.blocks) (x : ℕ) :
    B.live (S.erase x) j = (B.live S j).erase x := by
  ext y
  simp only [live, mem_inter, mem_erase]
  tauto

private theorem hcount_le (S : Finset ℕ) (j : Fin B.blocks) (x : ℕ) :
    B.hcount (S.erase x) j ≤ B.hcount S j := by
  rw [hcount, hcount, B.live_erase]
  exact card_le_card (erase_subset _ _)

private theorem hcount_eq (S : Finset ℕ) (j : Fin B.blocks) {x : ℕ}
    (hx : x ∉ B.high j) : B.hcount (S.erase x) j = B.hcount S j := by
  rw [hcount, hcount, B.live_erase, erase_eq_of_notMem]
  exact fun h => hx (mem_inter.mp h).2

private theorem hcount_pred {S : Finset ℕ} {j : Fin B.blocks} {x : ℕ}
    (hx : x ∈ B.live S j) : B.hcount (S.erase x) j + 1 = B.hcount S j := by
  rw [hcount, hcount, B.live_erase]
  exact card_erase_add_one hx

private theorem intact_eq (S : Finset ℕ) (j : Fin B.blocks) {x : ℕ}
    (hx : ∀ i, x ∉ B.reserve j i) : B.intact (S.erase x) j = B.intact S j := by
  ext i
  simp only [B.mem_intact]
  exact ⟨fun h => h.trans (erase_subset _ _),
    fun h y hy => mem_erase.mpr ⟨fun e => hx i (e ▸ hy), h hy⟩⟩

private theorem intact_loss (S : Finset ℕ) (j : Fin B.blocks) (x : ℕ) :
    (B.intact S j).card ≤ (B.intact (S.erase x) j).card + 1 := by
  classical
  by_cases h : ∃ i, x ∈ B.reserve j i
  · obtain ⟨i, hi⟩ := h
    have hs : B.intact S j ⊆ insert i (B.intact (S.erase x) j) := by
      intro a ha
      by_cases hai : a = i
      · simp [hai]
      · refine mem_insert_of_mem (B.mem_intact.mpr ?_)
        intro y hy
        refine mem_erase.mpr ⟨?_, (B.mem_intact.mp ha) hy⟩
        rintro rfl
        exact disjoint_left.mp (B.reserves_disjoint j hai) hy hi
    exact (card_le_card hs).trans (card_insert_le _ _)
  · rw [B.intact_eq S j (not_exists.mp h)]
    omega

def Strong (S : Finset ℕ) (j : Fin B.blocks) : Prop :=
  0 < B.hcount S j → B.hcount S j < (B.intact S j).card

def Ready (S : Finset ℕ) : Prop := Legal k n S ∧ ∀ j, B.Strong S j

def Weak (S : Finset ℕ) : Prop :=
  Legal k n S ∧ ∀ j, B.hcount S j ≤ (B.intact S j).card

private theorem Ready.weak {S : Finset ℕ} (h : B.Ready S) : B.Weak S := by
  refine ⟨h.1, fun j => ?_⟩
  by_cases hp : 0 < B.hcount S j
  · exact (h.2 j hp).le
  · omega

private theorem strong_outside {S : Finset ℕ} {j : Fin B.blocks} {x : ℕ}
    (hx : x ∉ B.cells j) :
    B.Strong (S.erase x) j ↔ B.Strong S j := by
  have h₁ := B.hcount_eq S j (fun h => hx (B.high_subset j h))
  have h₂ := B.intact_eq S j (fun i h => hx (B.reserve_subset j i h))
  simp only [Strong, h₁, h₂]

private theorem strong_high {S : Finset ℕ} {j : Fin B.blocks} {x : ℕ}
    (hw : B.Weak S) (hx : x ∈ B.live S j) :
    B.Strong (S.erase x) j := by
  have h₁ := B.hcount_pred hx
  have h₂ := B.intact_eq S j
    (fun i h => disjoint_left.mp (B.high_reserve j i) (mem_inter.mp hx).2 h)
  have h₃ := hw.2 j
  unfold Strong
  rw [h₂]
  omega

private theorem weak_next {S T : Finset ℕ} {b c : Bool}
    (hS : B.Ready S) (h : Next k n S b T c) :
    B.Weak T ∧ ∀ j l, ¬ B.Strong T j → ¬ B.Strong T l → j = l := by
  refine ⟨⟨next_legal hS.1 h, ?_⟩, ?_⟩
  · rcases h with ⟨_, _, rfl⟩ | ⟨x, _, _, rfl⟩
    · exact (Ready.weak B hS).2
    · intro j
      have h₁ := B.hcount_le S j x
      have h₂ := B.intact_loss S j x
      by_cases hp : 0 < B.hcount (S.erase x) j
      · have hs := hS.2 j (by omega)
        omega
      · omega
  · intro j l hj hl
    rcases h with ⟨_, _, rfl⟩ | ⟨x, _, _, rfl⟩
    · exact False.elim (hj (hS.2 j))
    · by_contra hne
      have hxj : x ∈ B.cells j := by
        by_contra hx
        exact hj ((B.strong_outside hx).mpr (hS.2 j))
      have hxl : x ∈ B.cells l := by
        by_contra hx
        exact hl ((B.strong_outside hx).mpr (hS.2 l))
      exact disjoint_left.mp (B.blocks_disjoint hne) hxj hxl

private theorem subset_of_weak {S : Finset ℕ} (hS : B.Weak S) :
    ∃ U ⊆ S, U.card = B.rank ∧ Legal k n U ∧ ∀ j, Disjoint U (B.high j) := by
  apply B.glue
  intro j
  by_cases hp : 0 < B.hcount S j
  · have hi : 0 < (B.intact S j).card := hp.trans_le (hS.2 j)
    obtain ⟨i, hi⟩ := card_pos.mp hi
    exact ⟨B.reserve j i, B.mem_intact.mp hi, B.reserve_good j i⟩
  · apply B.finished hS.1 j
    refine disjoint_left.mpr ?_
    intro x hxS hxH
    exact hp (card_pos.mpr ⟨x, mem_inter.mpr ⟨hxS, hxH⟩⟩)

private theorem rank_le {S : Finset ℕ} (hS : B.Weak S) : B.rank ≤ S.card := by
  obtain ⟨U, hU, hcard, _, _⟩ := B.subset_of_weak hS
  exact hcard ▸ card_le_card hU

private theorem erase_high {S : Finset ℕ} {b : Bool} {j : Fin B.blocks} {x : ℕ}
    (hS : B.Weak S) (hx : x ∈ B.live S j)
    (hOthers : ∀ l, l ≠ j → B.Strong S l) :
    Next k n S b (S.erase x) b ∧ B.Ready (S.erase x) := by
  obtain ⟨U, hsub, _, hlegal, hhigh⟩ := B.subset_of_weak hS
  obtain ⟨hxS, hxH⟩ := mem_inter.mp hx
  have hU : U ⊆ S.erase x := by
    intro y hy
    exact mem_erase.mpr ⟨fun e => disjoint_left.mp (hhigh j) (e ▸ hy) hxH, hsub hy⟩
  have hl := legal_mono hU hlegal
  refine ⟨Or.inr ⟨x, mem_options.mpr ⟨hxS, hl⟩, rfl, rfl⟩, hl, fun l => ?_⟩
  by_cases he : l = j
  · subst l
    exact B.strong_high hS hx
  · have hxout : x ∉ B.cells l :=
      fun h => disjoint_left.mp (B.blocks_disjoint he) h (B.high_subset j hxH)
    exact (B.strong_outside hxout).mpr (hOthers l he)

private theorem make_move {S : Finset ℕ} {b : Bool} (hS : B.Weak S)
    (hUnique : ∀ j l, ¬ B.Strong S j → ¬ B.Strong S l → j = l)
    (hMass : B.rank < mass S b) :
    ∃ T c, Next k n S b T c ∧ B.Ready T := by
  classical
  by_cases hbad : ∃ j, ¬ B.Strong S j
  · obtain ⟨j, hj⟩ := hbad
    have hp : 0 < B.hcount S j := by
      by_contra hn
      exact hj (fun he => (hn he).elim)
    obtain ⟨x, hx⟩ := card_pos.mp hp
    refine ⟨S.erase x, b, B.erase_high hS hx ?_⟩
    intro l hl
    by_contra hs
    exact hl (hUnique l j hs hj)
  · have hstrong : ∀ j, B.Strong S j := by simpa using hbad
    by_cases hlive : ∃ j, 0 < B.hcount S j
    · obtain ⟨j, hj⟩ := hlive
      obtain ⟨x, hx⟩ := card_pos.mp hj
      exact ⟨S.erase x, b, B.erase_high hS hx (fun l _ => hstrong l)⟩
    · cases b with
      | true => exact ⟨S, false, Or.inl ⟨rfl, rfl, rfl⟩, hS.1, hstrong⟩
      | false =>
        obtain ⟨U, hU, hcard, hlegal, _⟩ := B.subset_of_weak hS
        have hc : U.card < S.card := by simpa [mass, hcard] using hMass
        obtain ⟨x, hxS, hxU⟩ := exists_mem_notMem_of_card_lt_card hc
        have hsub : U ⊆ S.erase x := fun y hy =>
          mem_erase.mpr ⟨fun he => hxU (he ▸ hy), hU hy⟩
        have hl := legal_mono hsub hlegal
        refine ⟨S.erase x, false, Or.inr ⟨x, mem_options.mpr ⟨hxS, hl⟩, rfl, rfl⟩,
          hl, fun j hj => ?_⟩
        exact False.elim (hlive ⟨j, hj.trans_le (B.hcount_le S j x)⟩)

def strategy : Strategy k n where
  rank := B.rank
  Ready := B.Ready
  lower h := B.rank_le (Ready.weak B h)
  child_lower hS h := B.rank_le (B.weak_next hS h).1
  step hS hM := B.make_move (Ready.weak B hS)
    (fun j _ hj _ => (hj (hS.2 j)).elim) hM
  reply hS h hM :=
    have hw := B.weak_next hS h
    B.make_move hw.1 hw.2 hM

end BlockSystem


-- The concrete layout consists of full blocks and possibly one final anchor.
namespace Layout

def k (m : ℕ) := 2 * m + 1
def s (m : ℕ) := m + 1
def p (m : ℕ) := 3 * m + 2

structure Shape where
  m : ℕ
  q : ℕ
  pre : ℕ
  post : ℕ
  final : Bool
  pre_le : pre ≤ m
  post_le : post ≤ m
  final_post : final = true → post = 0

namespace Shape

variable (A : Shape)

def blocks := A.q + A.final.toNat
def rank := 2 * A.q + A.final.toNat
def n := A.pre + A.q * p A.m + A.final.toNat * k A.m + A.post

abbrev k' := k A.m
abbrev s' := s A.m

def origin (j : ℕ) := A.pre + j * p A.m
def lo (j i : ℕ) := A.origin j + i + 1
def mid (j i : ℕ) := A.origin j + A.k' + i + 1

def cells (j : Fin A.blocks) : Finset ℕ :=
  Icc (A.origin j + 1) (A.origin j + if j.val < A.q then p A.m else A.k')

def high (j : Fin A.blocks) : Finset ℕ :=
  Icc (A.origin j + A.s' + 1) (A.origin j + A.k')

def support (j : Fin A.blocks) (i z : Fin A.s') : Finset ℕ :=
  if j.val < A.q then {A.lo j i, A.mid j z} else {A.lo j i}

def Good (j : Fin A.blocks) (U : Finset ℕ) : Prop :=
  ∃ i z : Fin A.s', z.val ≤ i.val ∧ U = A.support j i z

private theorem no_full_eq {j : Fin A.blocks} (h : ¬ j.val < A.q) :
    j.val = A.q ∧ A.final = true := by
  have hj := j.isLt
  cases he : A.final <;> simp only [blocks, he, Bool.toNat_false, Bool.toNat_true] at hj
  · omega
  · exact ⟨by omega, rfl⟩

private theorem high_subset (j : Fin A.blocks) : A.high j ⊆ A.cells j := by
  intro x hx
  simp only [high, mem_Icc] at hx
  simp only [cells, mem_Icc]
  split
  · simp only [p, k', k] at *
    omega
  · omega

private theorem support_subset (j : Fin A.blocks) (i z : Fin A.s') :
    A.support j i z ⊆ A.cells j := by
  have hi := i.isLt
  have hz := z.isLt
  intro x hx
  by_cases h : j.val < A.q
  · simp only [support, ite_eq_left h, mem_insert, mem_singleton] at hx
    simp only [cells, ite_eq_left h, mem_Icc]
    rcases hx with rfl | rfl
    · simp only [lo, s', s, p] at *
      omega
    · simp only [mid, k', s', s, p, k] at *
      omega
  · simp only [support, ite_eq_right h, mem_singleton] at hx
    simp only [cells, ite_eq_right h, mem_Icc]
    subst x
    simp only [lo, k', s', s, k] at *
    omega

private theorem lo_lt_mid (j : ℕ) (i z : Fin A.s') : A.lo j i < A.mid j z := by
  have hi := i.isLt
  unfold lo mid k' s' k s at *
  omega

private theorem support_high_disjoint (j : Fin A.blocks) (i z : Fin A.s') :
    Disjoint (A.high j) (A.support j i z) := by
  apply disjoint_left.mpr
  intro x hx hs
  have hi := i.isLt
  simp only [high, mem_Icc] at hx
  unfold support at hs
  split at hs
  · simp only [mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl
    · unfold lo at hx
      omega
    · unfold mid at hx
      omega
  · simp only [mem_singleton] at hs
    subst x
    unfold lo at hx
    omega

private theorem reserves_disjoint (j : Fin A.blocks) {i z : Fin A.s'} (hne : i ≠ z) :
    Disjoint (A.support j i i) (A.support j z z) := by
  apply disjoint_left.mpr
  intro x hi hz
  have hval : i.val ≠ z.val := fun e => hne (Fin.ext e)
  by_cases h : j.val < A.q
  · simp only [support, ite_eq_left h, mem_insert, mem_singleton] at hi hz
    have h₁ := A.lo_lt_mid j i z
    have h₂ := A.lo_lt_mid j z i
    rcases hi with hi | hi <;> rcases hz with hz | hz
    all_goals unfold lo mid at *; omega
  · simp only [support, ite_eq_right h, mem_singleton] at hi hz
    unfold lo at *
    omega

private theorem origin_step (j : ℕ) : A.origin (j + 1) = A.origin j + p A.m := by
  simp [origin, Nat.add_mul, Nat.add_assoc]

private theorem origin_mono : Monotone A.origin := by
  intro i j hij
  unfold origin
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

private theorem cells_disjoint_of_lt {j l : Fin A.blocks} (hlt : j.val < l.val) :
    Disjoint (A.cells j) (A.cells l) := by
  apply disjoint_left.mpr
  intro x hj hl
  simp only [cells, mem_Icc] at hj hl
  have h₁ := A.origin_mono (show j.val + 1 ≤ l.val by omega)
  rw [A.origin_step] at h₁
  have h₂ := hj.2
  split at h₂ <;> unfold p k' k at * <;> omega

private theorem cells_disjoint {j l : Fin A.blocks} (hne : j ≠ l) :
    Disjoint (A.cells j) (A.cells l) := by
  have hval : j.val ≠ l.val := fun e => hne (Fin.ext e)
  rcases lt_or_gt_of_ne hval with h | h
  · exact A.cells_disjoint_of_lt h
  · exact (A.cells_disjoint_of_lt h).symm

private theorem origin_full_le (j : ℕ) (hj : j ≤ A.q) :
    A.origin j ≤ A.pre + A.q * p A.m := A.origin_mono hj

private theorem cells_bounds (j : Fin A.blocks) : A.cells j ⊆ Icc 1 A.n := by
  intro x hx
  simp only [cells, mem_Icc] at hx
  simp only [mem_Icc, n]
  refine ⟨by omega, ?_⟩
  by_cases h : j.val < A.q
  · have hh := A.origin_full_le (j.val + 1) (by omega)
    rw [A.origin_step] at hh
    rw [ite_eq_left h] at hx
    omega
  · obtain ⟨he, hf⟩ := A.no_full_eq h
    have hh := A.origin_full_le j.val he.le
    rw [ite_eq_right h] at hx
    simp only [hf, Bool.toNat_true, Nat.one_mul]
    simp only [k'] at hx
    omega

private theorem anchor_bound (j : Fin A.blocks) : A.origin j + A.k' ≤ A.n := by
  have hx : A.origin j + A.k' ∈ A.cells j := by
    simp only [cells, mem_Icc]
    split <;> simp only [k', k, p] <;> omega
  exact (mem_Icc.mp (A.cells_bounds j hx)).2

private theorem full_bound (j : Fin A.blocks) (h : j.val < A.q) :
    A.origin j + p A.m ≤ A.n := by
  have hx : A.origin j + p A.m ∈ A.cells j := by
    simp only [cells, ite_eq_left h, mem_Icc, le_refl, and_true]
    unfold p
    omega
  exact (mem_Icc.mp (A.cells_bounds j hx)).2

private theorem finished {S : Finset ℕ} (hS : Legal A.k' A.n S)
    (j : Fin A.blocks) (hfin : Disjoint S (A.high j)) :
    ∃ U ⊆ S, A.Good j U := by
  let cuts := S ∩ Icc (A.origin j + 1) (A.origin j + A.k')
  have hne : cuts.Nonempty := by
    obtain ⟨x, hx, h₁, h₂⟩ :=
      hS (A.origin j + 1) (by omega) (by have := A.anchor_bound j; omega)
    exact ⟨x, mem_inter.mpr ⟨hx, mem_Icc.mpr ⟨h₁, by omega⟩⟩⟩
  let x := cuts.max' hne
  have hmem : x ∈ cuts := max'_mem _ _
  obtain ⟨hx, hxa⟩ := mem_inter.mp hmem
  obtain ⟨hxlo, hxhi⟩ := mem_Icc.mp hxa
  have hxl : x ≤ A.origin j + A.s' := by
    by_contra hh
    exact disjoint_left.mp hfin hx (mem_Icc.mpr ⟨by omega, hxhi⟩)
  let i : Fin A.s' := ⟨x - A.origin j - 1, by omega⟩
  have hxval : A.lo j i = x := by
    unfold lo
    change A.origin ↑j + (x - A.origin ↑j - 1) + 1 = x
    omega
  by_cases h : j.val < A.q
  · have hb := A.full_bound j h
    have hsz : p A.m = A.k' + A.s' := by simp only [p, k', s', k, s]; omega
    have harg : x + 1 + A.k' ≤ A.n + 1 := by omega
    obtain ⟨y, hy, hylo, hyhi⟩ := hS (x + 1) (by omega) harg
    have hmid : A.origin j + A.k' < y := by
      by_contra hh
      have hymem : y ∈ cuts :=
        mem_inter.mpr ⟨hy, mem_Icc.mpr ⟨by omega, by omega⟩⟩
      have hyn := le_max' cuts y hymem
      change y ≤ x at hyn
      omega
    let z : Fin A.s' := ⟨y - A.origin j - A.k' - 1, by omega⟩
    have hyval : A.mid j z = y := by
      unfold mid
      change A.origin ↑j + A.k' + (y - A.origin ↑j - A.k' - 1) + 1 = y
      omega
    refine ⟨A.support j i z, ?_, i, z, ?_, rfl⟩
    · simp only [support, ite_eq_left h, hxval, hyval, insert_subset_iff, singleton_subset_iff]
      exact ⟨hx, hy⟩
    · change y - A.origin ↑j - A.k' - 1 ≤ x - A.origin ↑j - 1
      omega
  · refine ⟨A.support j i i, ?_, i, i, le_rfl, rfl⟩
    simpa only [support, ite_eq_right h, hxval, singleton_subset_iff] using hx


private theorem legal_of_chain {N K R : ℕ} {U : Finset ℕ} (c : ℕ → ℕ)
    (hzero : c 0 = 0) (hend : c (R + 1) = N + 1)
    (hgap : ∀ t ≤ R, c (t + 1) ≤ c t + K)
    (hmem : ∀ t, 0 < t → t ≤ R → c t ∈ U) :
    Legal K N U := by
  intro a ha hb
  have he : ∃ t, a ≤ c t := ⟨R + 1, by rw [hend]; omega⟩
  let t := Nat.find he
  have ht : a ≤ c t := Nat.find_spec he
  have htend : t ≤ R + 1 := Nat.find_min' he (by rw [hend]; omega)
  have htpos : 0 < t := by
    by_contra hn
    have h0 : t = 0 := by omega
    rw [h0, hzero] at ht
    omega
  have hprev : ¬ a ≤ c (t - 1) := Nat.find_min he (by omega)
  have hstep := hgap (t - 1) (by omega)
  rw [show t - 1 + 1 = t by omega] at hstep
  have hbound : c t < a + K := by omega
  have htr : t ≤ R := by
    by_contra hn
    have heq : t = R + 1 := by omega
    rw [heq, hend] at hbound
    omega
  exact ⟨c t, hmem t htpos htr, ht, hbound⟩

private def chain (i z : Fin A.blocks → Fin A.s') (t : ℕ) : ℕ :=
  if h₀ : t = 0 then 0
  else if h : t ≤ A.rank then
    let j : Fin A.blocks := ⟨(t - 1) / 2, by
      have hf : A.final.toNat ≤ 1 := by cases A.final <;> decide
      unfold blocks at *
      unfold rank at h
      omega⟩
    if t % 2 = 1 then A.lo j (i j) else A.mid j (z j)
  else A.n + 1

private theorem chain_zero (i z : Fin A.blocks → Fin A.s') :
    A.chain i z 0 = 0 := by simp [chain]

private theorem chain_end (i z : Fin A.blocks → Fin A.s') :
    A.chain i z (A.rank + 1) = A.n + 1 := by simp [chain]

private theorem chain_lo (i z : Fin A.blocks → Fin A.s') (j : Fin A.blocks) :
    A.chain i z (2 * j.val + 1) = A.lo j (i j) := by
  have hj := j.isLt
  have hf : A.final.toNat ≤ 1 := by cases A.final <;> decide
  unfold blocks at hj
  have h₀ : 2 * j.val + 1 ≠ 0 := by omega
  have hr : 2 * j.val + 1 ≤ A.rank := by unfold rank; omega
  have hm : (2 * j.val + 1) % 2 = 1 := by omega
  have he : (⟨(2 * j.val + 1 - 1) / 2, by
      change (2 * j.val + 1 - 1) / 2 < A.q + A.final.toNat
      omega⟩ : Fin A.blocks) = j := Fin.ext (by simp)
  simp only [chain, dite_eq_right h₀, dite_eq_left hr, hm, ite_true, he]
  congr 1
  omega

private theorem chain_mid (i z : Fin A.blocks → Fin A.s') (j : Fin A.blocks)
    (hj : j.val < A.q) : A.chain i z (2 * j.val + 2) = A.mid j (z j) := by
  have h₀ : 2 * j.val + 2 ≠ 0 := by omega
  have hr : 2 * j.val + 2 ≤ A.rank := by unfold rank; omega
  have hm : (2 * j.val + 2) % 2 ≠ 1 := by omega
  have he : (⟨(2 * j.val + 2 - 1) / 2, by
      change (2 * j.val + 2 - 1) / 2 < A.q + A.final.toNat
      omega⟩ : Fin A.blocks) = j := Fin.ext (by
    change (2 * j.val + 2 - 1) / 2 = j.val
    omega)
  simp only [chain, dite_eq_right h₀, dite_eq_left hr, ite_eq_right hm, he]
  congr 1
  omega

private theorem chain_interior (i z : Fin A.blocks → Fin A.s') (t : ℕ)
    (ht : 0 < t) (hr : t ≤ A.rank) :
    ∃ j : Fin A.blocks,
     (t = 2 * j.val + 1 ∧ A.chain i z t = A.lo j (i j)) ∨
     (t = 2 * j.val + 2 ∧ j.val < A.q ∧ A.chain i z t = A.mid j (z j)) := by
  have hf : A.final.toNat ≤ 1 := by cases A.final <;> decide
  have hr' : t ≤ 2 * A.q + A.final.toNat := hr
  let j : Fin A.blocks := ⟨(t - 1) / 2, by unfold blocks; omega⟩
  refine ⟨j, ?_⟩
  change (t = 2 * ((t - 1) / 2) + 1 ∧ _) ∨
    (t = 2 * ((t - 1) / 2) + 2 ∧ (t - 1) / 2 < A.q ∧ _)
  by_cases hm : t % 2 = 1
  · have he : t = 2 * j.val + 1 := by change t = 2 * ((t - 1) / 2) + 1; omega
    exact Or.inl ⟨he, by rw [he, A.chain_lo]⟩
  · have he : t = 2 * j.val + 2 := by change t = 2 * ((t - 1) / 2) + 2; omega
    have hj : j.val < A.q := by change (t - 1) / 2 < A.q; omega
    exact Or.inr ⟨he, hj, by rw [he, A.chain_mid i z j hj]⟩


private theorem chain_gap (i z : Fin A.blocks → Fin A.s')
    (hpair : ∀ j, (z j).val ≤ (i j).val)
    (t : ℕ) (ht : t ≤ A.rank) :
    A.chain i z (t + 1) ≤ A.chain i z t + A.k' := by
  have hf : A.final.toNat ≤ 1 := by cases A.final <;> decide
  have hb : A.blocks = A.q + A.final.toNat := rfl
  have hr : A.rank = 2 * A.q + A.final.toNat := rfl
  by_cases hzero : t = 0
  · subst t
    rw [A.chain_zero]
    by_cases hrz : A.rank = 0
    · have he : A.chain i z 1 = A.n + 1 := by
        simpa only [hrz, Nat.zero_add] using A.chain_end i z
      rw [Nat.zero_add, he, Nat.zero_add]
      have hq : A.q = 0 := by omega
      have hF : A.final.toNat = 0 := by omega
      have hpre := A.pre_le
      have hpost := A.post_le
      simp only [n, hq, hF, Nat.zero_mul, Nat.add_zero, k', k]
      omega
    · let j : Fin A.blocks := ⟨0, by omega⟩
      have he : A.chain i z 1 = A.lo 0 (i j) := by simpa [j] using A.chain_lo i z j
      rw [Nat.zero_add, he, Nat.zero_add]
      have hi := (i j).isLt
      have hpre := A.pre_le
      simp only [lo, origin, Nat.zero_mul, Nat.add_zero, k', k, s', s] at *
      omega
  · by_cases hlast : t = A.rank
    · rw [hlast, A.chain_end]
      have hh : 0 < A.rank := by omega
      cases hF : A.final with
      | false =>
        have hF' : A.final.toNat = 0 := by simp [hF]
        let j : Fin A.blocks := ⟨A.q - 1, by omega⟩
        have hj : j.val < A.q := by change A.q - 1 < A.q; omega
        have he : A.rank = 2 * j.val + 2 := by
          change A.rank = 2 * (A.q - 1) + 2
          omega
        rw [he, A.chain_mid i z j hj]
        have hjo : j.val + 1 = A.q := by change A.q - 1 + 1 = A.q; omega
        have hO := A.origin_step j.val
        rw [hjo] at hO
        have hPost := A.post_le
        change A.origin A.q + A.final.toNat * A.k' + A.post + 1 ≤
          A.mid j (z j) + A.k'
        simp only [hF', Nat.zero_mul, Nat.add_zero, mid, k', k, p, s', s] at *
        omega
      | true =>
        have hF' : A.final.toNat = 1 := by simp [hF]
        let j : Fin A.blocks := ⟨A.q, by omega⟩
        have he : A.rank = 2 * j.val + 1 := by
          change A.rank = 2 * A.q + 1
          omega
        have hO : A.origin j = A.origin A.q := rfl
        rw [he, A.chain_lo]
        change A.origin A.q + A.final.toNat * A.k' + A.post + 1 ≤
          A.lo j (i j) + A.k'
        simp only [hF', Nat.one_mul, A.final_post hF, Nat.add_zero, lo, hO]
        omega
    · have htpos : 0 < t := by omega
      obtain ⟨j, hj | hj⟩ := A.chain_interior i z t htpos ht
      · obtain ⟨he, hlo⟩ := hj
        have hjq : j.val < A.q := by omega
        have hn : t + 1 = 2 * j.val + 2 := by omega
        rw [hn, A.chain_mid i z j hjq, hlo]
        have hp := hpair j
        simp only [mid, lo]
        omega
      · obtain ⟨he, _, hmid⟩ := hj
        let l : Fin A.blocks := ⟨j.val + 1, by omega⟩
        have hn : t + 1 = 2 * l.val + 1 := by change t + 1 = 2 * (j.val + 1) + 1; omega
        rw [hn, A.chain_lo, hmid]
        have hO : A.origin l = A.origin j + p A.m := A.origin_step j.val
        have hi := (i l).isLt
        simp only [lo, mid, hO, p, k', k, s', s] at *
        omega


private theorem lo_mem_support (i z : Fin A.s') (j : Fin A.blocks) :
    A.lo j i ∈ A.support j i z := by
  by_cases h : j.val < A.q <;> simp [support, h]

private theorem mid_mem_support (i z : Fin A.s') (j : Fin A.blocks) (h : j.val < A.q) :
    A.mid j z ∈ A.support j i z := by simp [support, h]

private theorem support_card (j : Fin A.blocks) (i z : Fin A.s') :
    (A.support j i z).card = if j.val < A.q then 2 else 1 := by
  by_cases h : j.val < A.q
  · have he := (A.lo_lt_mid j i z).ne
    simp [support, h, he]
  · simp [support, h]

private theorem sum_block_sizes (q : ℕ) (b : Bool) :
    (∑ j : Fin (q + b.toNat), if j.val < q then 2 else (1 : ℕ)) = 2 * q + b.toNat := by
  let f : ℕ → ℕ := fun j => if j < q then 2 else 1
  change (∑ j : Fin (q + b.toNat), f j.val) = _
  rw [Fin.sum_univ_eq_sum_range f]
  dsimp only [f]
  have hq : (∑ j ∈ range q, if j < q then 2 else (1 : ℕ)) = 2 * q := by
    calc
      _ = ∑ _j ∈ range q, (2 : ℕ) := by
            apply sum_congr rfl
            intro j hj
            simp [mem_range.mp hj]
      _ = _ := by simp [Nat.mul_comm]
  cases b
  · simpa using hq
  · simp only [Bool.toNat_true, sum_range_succ, lt_irrefl, ite_false, hq]

private theorem glue {S : Finset ℕ} (hs : ∀ j, ∃ U ⊆ S, A.Good j U) :
    ∃ U ⊆ S, U.card = A.rank ∧ Legal A.k' A.n U ∧ ∀ j, Disjoint U (A.high j) := by
  classical
  have he : ∀ j, ∃ i z : Fin A.s', z.val ≤ i.val ∧ A.support j i z ⊆ S := by
    intro j
    obtain ⟨U, hsub, i, z, hle, rfl⟩ := hs j
    exact ⟨i, z, hle, hsub⟩
  choose i z hle hsub using he
  let U := univ.biUnion (fun j => A.support j (i j) (z j))
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hx
    exact hsub j hj
  · have hd : (↑(univ : Finset (Fin A.blocks)) : Set (Fin A.blocks)).PairwiseDisjoint
          (fun j => A.support j (i j) (z j)) := by
      intro a _ b _ hne
      exact (A.cells_disjoint hne).mono (A.support_subset a (i a) (z a))
        (A.support_subset b (i b) (z b))
    change (univ.biUnion _).card = _
    rw [card_biUnion hd]
    simp only [A.support_card]
    exact sum_block_sizes A.q A.final
  · apply legal_of_chain (A.chain i z) (A.chain_zero i z) (A.chain_end i z)
      (A.chain_gap i z hle)
    intro t ht htr
    obtain ⟨j, h | h⟩ := A.chain_interior i z t ht htr
    · rw [h.2]
      exact mem_biUnion.mpr ⟨j, mem_univ _, A.lo_mem_support (i j) (z j) j⟩
    · rw [h.2.2]
      exact mem_biUnion.mpr ⟨j, mem_univ _, A.mid_mem_support (i j) (z j) j h.2.1⟩
  · intro j
    apply disjoint_left.mpr
    intro x hx hH
    obtain ⟨l, _, hL⟩ := mem_biUnion.mp hx
    by_cases h : j = l
    · subst l
      exact disjoint_left.mp (A.support_high_disjoint j (i j) (z j)) hH hL
    · exact disjoint_left.mp (A.cells_disjoint h) (A.high_subset j hH)
        (A.support_subset l (i l) (z l) hL)

def system : BlockSystem A.k' A.n where
  blocks := A.blocks
  slots := A.s'
  rank := A.rank
  cells := A.cells
  high := A.high
  reserve j i := A.support j i i
  Good := A.Good
  high_subset := A.high_subset
  reserve_subset j i := A.support_subset j i i
  blocks_disjoint := fun {_ _} h => A.cells_disjoint h
  reserves_disjoint := A.reserves_disjoint
  high_reserve j i := A.support_high_disjoint j i i
  reserve_good _j i := ⟨i, i, le_rfl, rfl⟩
  finished := A.finished
  glue := A.glue

private theorem high_card (j : Fin A.blocks) : (A.high j).card = A.m := by
  simp only [high, Nat.card_Icc, k', k, s', s]
  omega

theorem ready_full : A.system.Ready (Icc 1 A.n) := by
  refine ⟨?_, fun j _ => ?_⟩
  · intro a ha hb
    have hk : 0 < A.k' := by change 0 < 2 * A.m + 1; omega
    exact ⟨a, mem_Icc.mpr ⟨ha, by omega⟩, le_rfl, by omega⟩
  · have hhigh : A.system.live (Icc 1 A.n) j = A.high j := by
      change Icc 1 A.n ∩ A.high j = A.high j
      exact inter_eq_right.mpr ((A.high_subset j).trans (A.cells_bounds j))
    have hint : A.system.intact (Icc 1 A.n) j = univ := by
      apply eq_univ_of_forall
      intro i
      apply A.system.mem_intact.mpr
      exact (A.support_subset j i i).trans (A.cells_bounds j)
    unfold BlockSystem.hcount
    rw [hhigh, hint]
    change (A.high (show Fin A.blocks from j)).card < (univ : Finset (Fin A.s')).card
    rw [A.high_card, card_univ, Fintype.card_fin]
    exact Nat.lt_succ_self A.m

theorem grundy_eq : grundy A.k' A.n (Icc 1 A.n) = (A.n - A.rank) % 2 := by
  have h := A.system.strategy.grundy_eq A.ready_full
  change grundy A.k' A.n (Icc 1 A.n) = ((Icc 1 A.n).card - A.rank) % 2 at h
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h

end Shape

/-- Split the remainder into bounded end gaps or give it its own final anchor. -/
def standard (m n : ℕ) : Shape where
  m := m
  q := n / p m
  pre := if k m ≤ n % p m then n % p m - k m else min (n % p m) m
  post := if k m ≤ n % p m then 0 else n % p m - min (n % p m) m
  final := decide (k m ≤ n % p m)
  pre_le := by
    have hr := Nat.mod_lt n (show 0 < p m by unfold p; omega)
    split
    · change n % p m < 3 * m + 2 at hr
      unfold k at *
      omega
    · exact min_le_right _ _
  post_le := by
    split
    · omega
    · unfold k at *
      omega
  final_post := by
    intro h
    have he := of_decide_eq_true h
    simp [he]

private theorem standard_n (m n : ℕ) : (standard m n).n = n := by
  have hdecomp : n % p m + (n / p m) * p m = n := by
    rw [Nat.mul_comm (n / p m), Nat.mod_add_div]
  by_cases h : k m ≤ n % p m
  · simp [Shape.n, standard, h]
    omega
  · simp [Shape.n, standard, h]
    omega

private theorem standard_rank (m n : ℕ) :
    (standard m n).rank = 2 * (n / p m) + if k m ≤ n % p m then 1 else 0 := by
  by_cases h : k m ≤ n % p m <;> simp [Shape.rank, standard, h]

end Layout

/-- The concrete strategy forces this terminal cut count from a full board. -/
theorem odd_inverse_kcross_rank (m n : ℕ) :
    ∃ C : Strategy (2 * m + 1) n,
      C.Ready (Icc 1 n) ∧
        C.rank = 2 * (n / (3 * m + 2)) +
          if 2 * m + 1 ≤ n % (3 * m + 2) then 1 else 0 := by
  let A := Layout.standard m n
  have hN : A.n = n := Layout.standard_n m n
  have hR := Layout.standard_rank m n
  change A.rank = 2 * (n / (3 * m + 2)) +
    if 2 * m + 1 ≤ n % (3 * m + 2) then 1 else 0 at hR
  have h : ∃ C : Strategy A.k' A.n, C.Ready (Icc 1 A.n) ∧
      C.rank = 2 * (n / (3 * m + 2)) +
        if 2 * m + 1 ≤ n % (3 * m + 2) then 1 else 0 :=
    ⟨A.system.strategy, A.ready_full, hR⟩
  change (∃ C : Strategy (2 * m + 1) A.n, C.Ready (Icc 1 A.n) ∧ _) at h
  rw [hN] at h
  exact h

/-- Exact Sprague–Grundy formula for every empty board at odd k. -/
theorem odd_inverse_kcross_formula (m n : ℕ) :
    grundy (2 * m + 1) n (Icc 1 n) =
      (n + if 2 * m + 1 ≤ n % (3 * m + 2) then 1 else 0) % 2 := by
  obtain ⟨C, hReady, hR⟩ := odd_inverse_kcross_rank m n
  have h := C.grundy_eq hReady
  have hl := C.lower hReady
  rw [Nat.card_Icc, Nat.add_sub_cancel, hR] at h hl
  rw [h]
  by_cases hE : 2 * m + 1 ≤ n % (3 * m + 2)
  · simp only [ite_eq_left hE] at *
    omega
  · simp only [ite_eq_right hE] at *
    omega

private theorem mod_two_add_xor (a b : ℕ) :
    (a + b) % 2 = (a % 2) ^^^ (b % 2) := by
  rw [Nat.add_mod]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> decide

private theorem shift_mod (a P : ℕ) : (P + a) % P = a % P := by
  rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

/-- The empty-board value is always a bit. -/
theorem odd_inverse_kcross_bit (m n : ℕ) :
    grundy (2 * m + 1) n (Icc 1 n) ≤ 1 := by
  rw [odd_inverse_kcross_formula]
  omega

/-- Translation by a full block adds the parity of m. -/
theorem odd_inverse_kcross_translation (m a : ℕ) :
    grundy (2 * m + 1) (3 * m + 2 + a) (Icc 1 (3 * m + 2 + a)) =
      grundy (2 * m + 1) a (Icc 1 a) ^^^ (m % 2) := by
  rw [odd_inverse_kcross_formula, odd_inverse_kcross_formula, shift_mod]
  let e := if 2 * m + 1 ≤ a % (3 * m + 2) then 1 else 0
  change (3 * m + 2 + a + e) % 2 = ((a + e) % 2) ^^^ (m % 2)
  rw [← mod_two_add_xor]
  omega

private theorem reflected_residue (m a : ℕ) (ha : a ≤ 5 * m + 2) :
    2 * m + 1 ≤ (5 * m + 2 - a) % (3 * m + 2) ↔
    2 * m + 1 ≤ a % (3 * m + 2) := by
  let P := 3 * m + 2
  have hP : P = 3 * m + 2 := rfl
  change 2 * m + 1 ≤ (5 * m + 2 - a) % P ↔ 2 * m + 1 ≤ a % P
  by_cases h : a < P
  · rw [Nat.mod_eq_of_lt h]
    by_cases hu : a ≤ 2 * m
    · have he : 5 * m + 2 - a = P + (2 * m - a) := by omega
      rw [he, shift_mod, Nat.mod_eq_of_lt (show 2 * m - a < P by omega)]
      omega
    · have hlt : 5 * m + 2 - a < P := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
  · have he : a = P + (a - P) := by omega
    have hm : a % P = a - P := by
      conv_lhs => rw [he, shift_mod]
      exact Nat.mod_eq_of_lt (by omega)
    have hlt : 5 * m + 2 - a < P := by omega
    rw [hm, Nat.mod_eq_of_lt hlt]
    omega

/-- Reflection in the finite domain from Liang and Li's conjecture. -/
theorem odd_inverse_kcross_reflection (m a : ℕ) (ha : a ≤ 5 * m + 2) :
    grundy (2 * m + 1) (5 * m + 2 - a) (Icc 1 (5 * m + 2 - a)) =
      grundy (2 * m + 1) a (Icc 1 a) ^^^ (m % 2) := by
  rw [odd_inverse_kcross_formula, odd_inverse_kcross_formula]
  simp only [reflected_residue m a ha]
  let e := if 2 * m + 1 ≤ a % (3 * m + 2) then 1 else 0
  change (5 * m + 2 - a + e) % 2 = ((a + e) % 2) ^^^ (m % 2)
  rw [← mod_two_add_xor]
  omega

/-- A Boolean board uses zero-based indices below n, with true marking an X. -/
def boardCuts (n : ℕ) (b : ℕ → Bool) : Finset ℕ :=
  (Icc 1 n).filter (fun x => b (x - 1) = false)

/-- No window of k consecutive cells of the board consists entirely of X's. -/
def BoolBoardLegal (k n : ℕ) (b : ℕ → Bool) : Prop :=
  ¬ ∃ a : ℕ, a + k ≤ n ∧ ∀ j, a ≤ j → j < a + k → b j = true

theorem boardCuts_empty (n : ℕ) : boardCuts n (fun _ => false) = Icc 1 n := by
  simp [boardCuts]

theorem boardCuts_legal_iff (k n : ℕ) (b : ℕ → Bool) :
    Legal k n (boardCuts n b) ↔ BoolBoardLegal k n b := by
  constructor
  · rintro h ⟨a, ha, hall⟩
    obtain ⟨x, hx, hax, hxa⟩ := h (a + 1) (by omega) (by omega)
    have hfalse := (Finset.mem_filter.mp hx).2
    have htrue := hall (x - 1) (by omega) (by omega)
    simp [hfalse] at htrue
  · intro h a ha hak
    have hblank : ∃ j, a - 1 ≤ j ∧ j < a - 1 + k ∧ b j = false := by
      by_contra hnone
      apply h
      refine ⟨a - 1, by omega, ?_⟩
      intro j haj hjak
      cases hbj : b j with
      | false => exact False.elim (hnone ⟨j, haj, hjak, hbj⟩)
      | true => rfl
    obtain ⟨j, haj, hjak, hbj⟩ := hblank
    refine ⟨j + 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩,
      by omega, by omega⟩
    simpa using hbj

theorem boardCuts_place (n : ℕ) (b : ℕ → Bool) (i : ℕ) :
    boardCuts n (fun j => if j = i then true else b j) = (boardCuts n b).erase (i + 1) := by
  ext x
  simp only [boardCuts, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]
  by_cases hx : 1 ≤ x
  · have hx' : x - 1 = i ↔ x = i + 1 := by omega
    by_cases hxi : x = i + 1 <;> simp [hx, hx', hxi, and_comm]
  · simp [hx]

/-- A deletion option is precisely a placement on a blank cell leaving no forbidden run. -/
theorem boardCuts_option_iff (k n : ℕ) (b : ℕ → Bool) (i : ℕ) :
    i + 1 ∈ options k n (boardCuts n b) ↔
      i < n ∧ b i = false ∧ BoolBoardLegal k n (fun j => if j = i then true else b j) := by
  rw [mem_options, ← boardCuts_place, boardCuts_legal_iff]
  simp [boardCuts, and_assoc]

/-- In a legal position a forbidden run after a placement must include its new X. -/
theorem boardCuts_source_move_iff (k n : ℕ) (b : ℕ → Bool) (i : ℕ)
    (hb : BoolBoardLegal k n b) :
    i + 1 ∈ options k n (boardCuts n b) ↔
      i < n ∧ b i = false ∧
        ¬ ∃ a : ℕ, a + k ≤ n ∧ a ≤ i ∧ i < a + k ∧
          ∀ j, a ≤ j → j < a + k → (if j = i then true else b j) = true := by
  rw [boardCuts_option_iff]
  constructor
  · rintro ⟨hi, hx, hlegal⟩
    refine ⟨hi, hx, ?_⟩
    rintro ⟨a, ha, _, _, hall⟩
    exact hlegal ⟨a, ha, hall⟩
  · rintro ⟨hi, hx, hno⟩
    refine ⟨hi, hx, ?_⟩
    rintro ⟨a, ha, hall⟩
    by_cases hinside : a ≤ i ∧ i < a + k
    · exact hno ⟨a, ha, hinside.1, hinside.2, hall⟩
    · apply hb
      refine ⟨a, ha, ?_⟩
      intro j haj hja
      have hji : j ≠ i := fun he => hinside ⟨he ▸ haj, he ▸ hja⟩
      simpa only [ite_eq_right hji] using hall j haj hja

/-- At k = 3, the legal empty board [4] has a move at cell 2 and value 1. -/
theorem odd_inverse_kcross_nonvacuous :
    Legal 3 4 (Icc 1 4) ∧ 2 ∈ options 3 4 (Icc 1 4) ∧ grundy 3 4 (Icc 1 4) = 1 := by
  have hlegal : Legal 3 4 ((Icc 1 4).erase 2) := by
    intro a ha hak
    exact ⟨3, by decide, by omega, by omega⟩
  refine ⟨legal_mono (Finset.erase_subset _ _) hlegal, mem_options.mpr ⟨by decide, hlegal⟩, ?_⟩
  exact odd_inverse_kcross_formula 1 4

end OddInverseKCross

#print axioms OddInverseKCross.odd_inverse_kcross_rank
#print axioms OddInverseKCross.odd_inverse_kcross_formula
#print axioms OddInverseKCross.odd_inverse_kcross_bit
#print axioms OddInverseKCross.odd_inverse_kcross_translation
#print axioms OddInverseKCross.odd_inverse_kcross_reflection
#print axioms OddInverseKCross.boardCuts_empty
#print axioms OddInverseKCross.boardCuts_legal_iff
#print axioms OddInverseKCross.boardCuts_place
#print axioms OddInverseKCross.boardCuts_option_iff
#print axioms OddInverseKCross.boardCuts_source_move_iff
#print axioms OddInverseKCross.odd_inverse_kcross_nonvacuous
```
