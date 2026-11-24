# Lean source appendix — MathDB 346681, stage 6 (COMPLETE)

### `KrewerasWords.lean`

```lean
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Rev
import Mathlib.GroupTheory.Perm.Basic
import Lean.Elab.Tactic.Omega

namespace Kreweras

abbrev Word (n : ℕ) := Fin (3*n) → Fin 3

def count {n : ℕ} (w : Word n) (c : Fin 3) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin (3*n) => i.val < k ∧ w i = c).card

def Valid {n : ℕ} (w : Word n) : Prop :=
  (∀ c, count w c (3*n) = n) ∧
  ∀ k : Fin (3*n+1), count w 1 k ≤ count w 0 k ∧ count w 2 k ≤ count w 0 k

instance {n : ℕ} (w : Word n) : Decidable (Valid w) := inferInstanceAs
  (Decidable ((_ : Prop) ∧ (_ : Prop)))

abbrev K (n : ℕ) := {w : Word n // Valid w}

instance (n : ℕ) : Fintype (Word n) := inferInstanceAs (Fintype (Fin (3*n) → Fin 3))
instance (n : ℕ) : DecidableEq (Word n) := inferInstanceAs (DecidableEq (Fin (3*n) → Fin 3))

@[simp] theorem count_zero {n : ℕ} (w : Word n) (c : Fin 3) : count w c 0 = 0 := by
  simp [count]

theorem count_mono {n : ℕ} (w : Word n) (c : Fin 3) {k l : ℕ} (h : k ≤ l) :
    count w c k ≤ count w c l := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 h, hi.2⟩

theorem count_succ {n : ℕ} (w : Word n) (c : Fin 3) (i : Fin (3*n)) :
    count w c (i.val+1) = count w c i.val + if w i = c then 1 else 0 := by
  unfold count
  by_cases h : w i = c
  · have hs : Finset.univ.filter (fun j : Fin (3*n) => j.val < i.val+1 ∧ w j=c) =
        insert i (Finset.univ.filter fun j : Fin (3*n) => j.val < i.val ∧ w j=c) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        by_cases he : j=i
        · exact Or.inl he
        · exact Or.inr ⟨by have := Fin.val_ne_of_ne he; omega, hj.2⟩
      · rintro (rfl | hj)
        · exact ⟨by omega, h⟩
        · exact ⟨by omega, hj.2⟩
    rw [hs, Finset.card_insert_of_notMem]
    · simp [h]
    · simp
  · have hs : Finset.univ.filter (fun j : Fin (3*n) => j.val < i.val+1 ∧ w j=c) =
        Finset.univ.filter (fun j : Fin (3*n) => j.val < i.val ∧ w j=c) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        have he : j ≠ i := by intro he; subst j; exact h hj.2
        exact ⟨by have := Fin.val_ne_of_ne he; omega, hj.2⟩
      · intro hj; exact ⟨by omega, hj.2⟩
    rw [hs]
    simp [h]

/-- Total adjacent position permutation; an out-of-range index acts trivially. -/
def adjacent (N i : ℕ) : Equiv.Perm (Fin N) :=
  if h : i+1 < N then Equiv.swap ⟨i, by omega⟩ ⟨i+1,h⟩ else Equiv.refl _

theorem adjacent_involutive (N i : ℕ) : Function.Involutive (adjacent N i) := by
  unfold adjacent
  split
  · exact Equiv.swap_apply_self _ _
  · intro x; rfl

def swapWord {n : ℕ} (i : ℕ) (w : Word n) : Word n := w ∘ adjacent (3*n) i

theorem swapWord_involutive {n : ℕ} (i : ℕ) : Function.Involutive (@swapWord n i) := by
  intro w
  funext j
  exact congrArg w (adjacent_involutive (3*n) i j)

/-- Conditional swap on an arbitrary decidable language. -/
def languageTau {n : ℕ} (Q : Word n → Prop) [DecidablePred Q] (i : ℕ)
    (w : {w // Q w}) : {w // Q w} :=
  if h : Q (swapWord i w.val) then ⟨swapWord i w.val,h⟩ else w

theorem languageTau_involutive {n : ℕ} (Q : Word n → Prop) [DecidablePred Q] (i : ℕ) :
    Function.Involutive (languageTau Q i) := by
  intro w
  by_cases h : Q (swapWord i w.val)
  · have h' : Q (swapWord i (swapWord i w.val)) := by
      rw [swapWord_involutive]; exact w.property
    apply Subtype.ext
    simp only [languageTau, dite_eq_left h, dite_eq_left h']
    exact swapWord_involutive i w.val
  · simp [languageTau, h]

def languageRun {n : ℕ} (Q : Word n → Prop) [DecidablePred Q] (s : List ℕ)
    (w : {w // Q w}) : {w // Q w} := s.foldl (fun v i => languageTau Q i v) w

theorem languageRun_bijective {n : ℕ} (Q : Word n → Prop) [DecidablePred Q] (s : List ℕ) :
    Function.Bijective (languageRun Q s) := by
  induction s with
  | nil => exact Function.bijective_id
  | cons i s ih =>
    exact ih.comp (languageTau_involutive Q i).bijective

def prefixSchedule (N : ℕ) : List ℕ := (List.range N).reverse.flatMap List.range

def tau {n : ℕ} (i : ℕ) : K n → K n := languageTau Valid i

theorem tau_involutive {n : ℕ} (i : ℕ) : Function.Involutive (@tau n i) :=
  languageTau_involutive Valid i

def run {n : ℕ} (s : List ℕ) : K n → K n := languageRun Valid s

theorem run_bijective {n : ℕ} (s : List ℕ) : Function.Bijective (@run n s) :=
  languageRun_bijective Valid s

def evac {n : ℕ} : K n → K n := run (prefixSchedule (3*n))

theorem evac_bijective {n : ℕ} : Function.Bijective (@evac n) := run_bijective _

def reverseWord {n : ℕ} (w : Word n) : Word n := fun i => w i.rev

@[simp] theorem reverseWord_reverseWord {n : ℕ} (w : Word n) :
    reverseWord (reverseWord w) = w := by
  funext i
  simp [reverseWord]

theorem reverseWord_involutive {n : ℕ} : Function.Involutive (@reverseWord n) :=
  reverseWord_reverseWord

abbrev ReverseK (n : ℕ) := {w : Word n // Valid (reverseWord w)}

def reversal {n : ℕ} : K n ≃ ReverseK n where
  toFun w := ⟨reverseWord w.val, by simpa using w.property⟩
  invFun w := ⟨reverseWord w.val,w.property⟩
  left_inv w := Subtype.ext (reverseWord_reverseWord w.val)
  right_inv w := Subtype.ext (reverseWord_reverseWord w.val)

/-- Literally reverse, evacuate in the reversed language, reverse back. -/
def dualEvac {n : ℕ} (w : K n) : K n := reversal.symm
  (languageRun (fun v => Valid (reverseWord v)) (prefixSchedule (3*n)) (reversal w))

theorem dualEvac_bijective {n : ℕ} : Function.Bijective (@dualEvac n) :=
  reversal.symm.bijective.comp
    ((languageRun_bijective (fun v => Valid (reverseWord v)) _).comp reversal.bijective)

#print axioms tau_involutive
#print axioms evac_bijective
#print axioms dualEvac_bijective
end Kreweras
```

### `KrewerasStatement.lean`

```lean
import KrewerasWords
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity

namespace Kreweras
open scoped BigOperators

def P (n : ℕ) : ℚ :=
  ((3^(n/2) * 4^((n+1)/2) *
    (∏ j ∈ Finset.Icc 1 (n/2), (3*j-1 : ℕ)) *
    (∏ j ∈ Finset.Icc 1 ((n+1)/2), (3*j-2 : ℕ)) : ℕ) : ℚ) /
    (Nat.factorial (n+1) : ℚ)

def LiteralEndpoint : Prop := ∀ n : ℕ, 1 ≤ n →
  (Fintype.card {w : K n // dualEvac w = w} : ℚ) = P n ∧
  (Fintype.card {w : K n // evac w = w} : ℚ) = if Even n then P n else 0

theorem small_P_one : P 1 = 2 := by norm_num [P, Nat.factorial]
theorem small_P_two : P 2 = 4 := by norm_num [P, Nat.factorial]
end Kreweras
```

### `KrewerasSmallOne.lean`

```lean
import KrewerasStatement

namespace Kreweras
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_card_one : Fintype.card (K 1) = 2 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_evac_one : Fintype.card {w : K 1 // evac w = w} = 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_dual_one : Fintype.card {w : K 1 // dualEvac w = w} = 2 := by decide

#print axioms small_card_one
#print axioms small_evac_one
#print axioms small_dual_one
end Kreweras
```

### `KrewerasSmallTwo.lean`

```lean
import KrewerasStatement

namespace Kreweras
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_card_two : Fintype.card (K 2) = 16 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_evac_two : Fintype.card {w : K 2 // evac w = w} = 4 := by decide

#print axioms small_card_two
#print axioms small_evac_two
end Kreweras
```

### `KrewerasSmallDualTwo.lean`

```lean
import KrewerasStatement

namespace Kreweras
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_dual_two : Fintype.card {w : K 2 // dualEvac w = w} = 4 := by decide

#print axioms small_dual_two
end Kreweras
```

### `KrewerasSanity.lean`

```lean
import KrewerasSmallOne
import KrewerasSmallTwo
import KrewerasSmallDualTwo

namespace Kreweras
theorem small_literal_one :
    (Fintype.card {w : K 1 // dualEvac w=w} : ℚ)=P 1 ∧
    (Fintype.card {w : K 1 // evac w=w} : ℚ)=(if Even (1 : ℕ) then P 1 else 0) := by
  norm_num [small_dual_one,small_evac_one,small_P_one]
theorem small_literal_two :
    (Fintype.card {w : K 2 // dualEvac w=w} : ℚ)=P 2 ∧
    (Fintype.card {w : K 2 // evac w=w} : ℚ)=(if Even (2 : ℕ) then P 2 else 0) := by
  norm_num [small_dual_two,small_evac_two,small_P_two]
#print axioms small_literal_one
#print axioms small_literal_two
#print LiteralEndpoint
end Kreweras
```

### `KrewerasPoset.lean`

```lean
import KrewerasWords
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin

namespace Kreweras
abbrev Element (n : ℕ) := Fin 3 × Fin n

def posetLE {n : ℕ} (p q : Element n) : Prop :=
  (p.1=q.1 ∨ p.1=0) ∧ p.2≤q.2

instance {n : ℕ} : DecidableRel (@posetLE n) := fun p q => inferInstanceAs (Decidable (((p.1=q.1 ∨ p.1=0) ∧ p.2≤q.2)))

theorem posetLE_refl {n : ℕ} (p : Element n) : posetLE p p := ⟨Or.inl rfl,le_rfl⟩
theorem posetLE_trans {n : ℕ} {p q r : Element n} :
    posetLE p q → posetLE q r → posetLE p r := by
  rintro ⟨hp,hpq⟩ ⟨hq,hqr⟩
  constructor
  · rcases hp with hp|hp
    · simpa [hp] using hq
    · exact Or.inr hp
  · exact le_trans hpq hqr
theorem posetLE_antisymm {n : ℕ} {p q : Element n} :
    posetLE p q → posetLE q p → p=q := by
  rintro ⟨hp,hpq⟩ ⟨hq,hqp⟩
  apply Prod.ext
  · rcases hp with hp|hp
    · exact hp
    · rcases hq with hq|hq
      · exact hq.symm
      · exact hp.trans hq.symm
  · exact le_antisymm hpq hqp

/-- An independently specified linear extension, recorded by the position of every element. -/
structure Extension (n : ℕ) where
  order : Element n ≃ Fin (3*n)
  mono : ∀ p q, posetLE p q → order p ≤ order q

def eraseOrder {n : ℕ} (e : Element n ≃ Fin (3*n)) : Word n := fun i => (e.symm i).1

def erase {n : ℕ} (e : Extension n) : Word n := eraseOrder e.order

/-- Counting erasure in a prefix is counting elements of a single chain in that prefix. -/
theorem count_eraseOrder {n : ℕ} (e : Element n ≃ Fin (3*n)) (c : Fin 3) (k : ℕ) :
    count (eraseOrder e) c k = (Finset.univ.filter fun r : Fin n => (e (c,r)).val<k).card := by
  unfold count
  apply Finset.card_bij (fun i _ => (e.symm i).2)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have he : e.symm i = (c,(e.symm i).2) := Prod.ext hi.2 rfl
    simpa only [← he, Equiv.apply_symm_apply] using hi.1
  · intro i hi j hj he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    apply e.symm.injective
    exact Prod.ext (hi.2.trans hj.2.symm) he
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    refine ⟨e (c,r), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr,by simp [eraseOrder]⟩
    · simp

theorem erase_valid {n : ℕ} (e : Extension n) : Valid (erase e) := by
  constructor
  · intro c
    rw [erase, count_eraseOrder]
    simp
  · intro k
    have hc (c : Fin 3) : count (erase e) c k ≤ count (erase e) 0 k := by
      simp only [erase, count_eraseOrder]
      apply Finset.card_le_card
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      have hm := e.mono (0,r) (c,r) ⟨Or.inr rfl,le_rfl⟩
      exact lt_of_le_of_lt hm hr
    exact ⟨hc 1,hc 2⟩

def occurrences {n : ℕ} (w : Word n) (c : Fin 3) : Finset (Fin (3*n)) :=
  Finset.univ.filter fun i => w i=c

theorem occurrences_card {n : ℕ} (w : K n) (c : Fin 3) : (occurrences w.val c).card=n := by
  have h := w.property.1 c
  simpa [count, occurrences] using h

def occPos {n : ℕ} (w : K n) (c : Fin 3) : Fin n ↪o Fin (3*n) :=
  (occurrences w.val c).orderEmbOfFin (occurrences_card w c)

@[simp] theorem occPos_letter {n : ℕ} (w : K n) (c : Fin 3) (r : Fin n) :
    w.val (occPos w c r)=c := by
  have h := Finset.orderEmbOfFin_mem (occurrences w.val c) (occurrences_card w c) r
  exact (Finset.mem_filter.mp h).2

def position {n : ℕ} (w : K n) (p : Element n) : Fin (3*n) := occPos w p.1 p.2

theorem position_bijective {n : ℕ} (w : K n) : Function.Bijective (position w) := by
  constructor
  · rintro ⟨c,r⟩ ⟨d,s⟩ h
    have hc : c=d := (occPos_letter w c r).symm.trans ((congrArg w.val h).trans (occPos_letter w d s))
    subst d
    exact Prod.ext rfl ((occPos w c).injective h)
  · intro i
    have hi : i ∈ occurrences w.val (w.val i) := by simp [occurrences]
    let r := ((occurrences w.val (w.val i)).orderIsoOfFin (occurrences_card w (w.val i))).symm ⟨i,hi⟩
    refine ⟨(w.val i,r), ?_⟩
    exact congrArg Subtype.val
      (((occurrences w.val (w.val i)).orderIsoOfFin (occurrences_card w (w.val i))).apply_symm_apply ⟨i,hi⟩)

noncomputable def labelOrder {n : ℕ} (w : K n) : Element n ≃ Fin (3*n) :=
  Equiv.ofBijective (position w) (position_bijective w)

@[simp] theorem labelOrder_apply {n : ℕ} (w : K n) (p : Element n) :
    labelOrder w p=position w p := rfl

@[simp] theorem erase_labelOrder {n : ℕ} (w : K n) : eraseOrder (labelOrder w)=w.val := by
  funext i
  let p := (labelOrder w).symm i
  have h := occPos_letter w p.1 p.2
  have hp : position w p=i := (labelOrder w).apply_symm_apply i
  exact (congrArg w.val hp).symm.trans h |>.symm

theorem count_at_occPos {n : ℕ} (w : K n) (c : Fin 3) (r : Fin n) :
    count w.val c (occPos w c r).val = r.val := by
  rw [← erase_labelOrder w, count_eraseOrder]
  change (Finset.univ.filter fun s : Fin n => (occPos w c s).val < (occPos w c r).val).card = r.val
  have hs : (Finset.univ.filter fun s : Fin n => (occPos w c s).val < (occPos w c r).val) =
      Finset.univ.filter (fun s : Fin n => s.val<r.val) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← Fin.lt_def,
      (occPos w c).lt_iff_lt]
  rw [hs, Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt r.isLt)]

theorem occPos_cross {n : ℕ} (w : K n) (c : Fin 3) (r : Fin n) :
    occPos w 0 r ≤ occPos w c r := by
  by_contra h
  have hlt : (occPos w c r).val < (occPos w 0 r).val := by simpa using lt_of_not_ge h
  have hmono := count_mono w.val 0 (Nat.succ_le_of_lt hlt)
  rw [count_at_occPos] at hmono
  have hc : count w.val c ((occPos w c r).val+1)=r.val+1 := by
    rw [count_succ, count_at_occPos, occPos_letter, ite_eq_left rfl]
  have hb : count w.val c ((occPos w c r).val+1) ≤ count w.val 0 ((occPos w c r).val+1) := by
    have hh := w.property.2 ⟨(occPos w c r).val+1,by have := (occPos w c r).isLt; omega⟩
    have ht := c.isLt
    rcases (show c=0 ∨ c=1 ∨ c=2 by omega) with rfl|rfl|rfl
    · exact le_rfl
    · exact hh.1
    · exact hh.2
  change count w.val 0 ((occPos w c r).val+1) ≤ r.val at hmono
  omega

noncomputable def label {n : ℕ} (w : K n) : Extension n where
  order := labelOrder w
  mono p q hpq := by
    change occPos w p.1 p.2 ≤ occPos w q.1 q.2
    rcases hpq.1 with h|h
    · simpa [h] using (occPos w q.1).monotone hpq.2
    · rw [h]
      exact le_trans (occPos_cross w q.1 p.2) ((occPos w q.1).monotone hpq.2)

theorem Extension.ext {n : ℕ} {e f : Extension n} (h : e.order=f.order) : e=f := by
  cases e
  cases f
  cases h
  rfl

theorem occPos_erase {n : ℕ} (e : Extension n) (c : Fin 3) :
    (occPos ⟨erase e,erase_valid e⟩ c : Fin n → Fin (3*n)) = fun r => e.order (c,r) := by
  apply Eq.symm
  apply Finset.orderEmbOfFin_unique
  · intro r
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [erase, eraseOrder]⟩
  · intro r s hrs
    apply lt_of_le_of_ne (e.mono (c,r) (c,s) ⟨Or.inl rfl,le_of_lt hrs⟩)
    intro h
    exact (ne_of_lt hrs) (congrArg Prod.snd (e.order.injective h))

theorem label_erase {n : ℕ} (e : Extension n) : label ⟨erase e,erase_valid e⟩=e := by
  apply Extension.ext
  apply Equiv.ext
  rintro ⟨c,r⟩
  exact congrFun (occPos_erase e c) r

noncomputable def wordExtensionEquiv (n : ℕ) : K n ≃ Extension n where
  toFun := label
  invFun e := ⟨erase e,erase_valid e⟩
  left_inv w := Subtype.ext (erase_labelOrder w)
  right_inv := label_erase

theorem label_exists_unique {n : ℕ} (w : K n) : ∃! e : Extension n, erase e=w.val := by
  refine ⟨label w,erase_labelOrder w,?_⟩
  intro e he
  have h : (⟨erase e,erase_valid e⟩ : K n)=w := Subtype.ext he
  rw [← label_erase e, h]

@[simp] theorem label_letter {n : ℕ} (w : K n) (i : Fin (3*n)) :
    (((wordExtensionEquiv n w).order.symm i).1)=w.val i :=
  congrFun (erase_labelOrder w) i

theorem label_index {n : ℕ} (w : K n) (i : Fin (3*n)) :
    ((((wordExtensionEquiv n w).order.symm i).2) : ℕ) = count w.val (w.val i) i.val := by
  let p := (labelOrder w).symm i
  have hp : occPos w p.1 p.2=i := (labelOrder w).apply_symm_apply i
  change p.2.val = count w.val (w.val i) i.val
  have hc := count_at_occPos w p.1 p.2
  rw [hp] at hc
  have hl : p.1=w.val i := label_letter w i
  simpa only [hl] using hc.symm

#print axioms wordExtensionEquiv
#print axioms label_exists_unique
#print axioms label_index
#print axioms erase_valid
#print axioms count_at_occPos
#print axioms label
end Kreweras
```

### `KrewerasOperators.lean`

```lean
import KrewerasPoset

namespace Kreweras

theorem adjacent_le {N i : ℕ} {x y : Fin N} (hxy : x≤y)
    (hbad : ¬(x.val=i ∧ y.val=i+1)) : adjacent N i x ≤ adjacent N i y := by
  unfold adjacent
  split
  · simp only [Equiv.swap_apply_def]
    split_ifs <;> simp only [Fin.le_def] <;> simp only [Fin.ext_iff] at * <;> omega
  · exact hxy

/-- Source linear extensions for an arbitrary relation, including its order dual. -/
structure LinearExtension {α : Type} (R : α → α → Prop) (N : ℕ) where
  order : α ≃ Fin N
  mono : ∀ p q, R p q → order p ≤ order q

theorem LinearExtension.ext {α : Type} {R : α → α → Prop} {N : ℕ}
    {e f : LinearExtension R N} (h : e.order=f.order) : e=f := by
  cases e
  cases f
  cases h
  rfl

def OrderValid {α : Type} (R : α → α → Prop) {N : ℕ} (e : α ≃ Fin N) : Prop :=
  ∀ p q, R p q → e p ≤ e q

theorem swap_orderValid_iff {α : Type} {R : α → α → Prop} {N i : ℕ}
    (e : LinearExtension R N) (hi : i+1<N) :
    OrderValid R (e.order.trans (adjacent N i)) ↔
      ¬R (e.order.symm ⟨i,by omega⟩) (e.order.symm ⟨i+1,hi⟩) ∧
      ¬R (e.order.symm ⟨i+1,hi⟩) (e.order.symm ⟨i,by omega⟩) := by
  let a : Fin N := ⟨i,by omega⟩
  let b : Fin N := ⟨i+1,hi⟩
  have hab : a≠b := by simp [a,b,Fin.ext_iff]
  constructor
  · intro hv
    constructor
    · intro h
      have hm := hv (e.order.symm a) (e.order.symm b) h
      simp only [Equiv.trans_apply,Equiv.apply_symm_apply] at hm
      simp only [a,b,adjacent,dite_eq_left hi,Equiv.swap_apply_left,Equiv.swap_apply_right] at hm
      exact (not_le_of_gt (show a<b by simp [a,b])) hm
    · intro h
      have hm := e.mono (e.order.symm b) (e.order.symm a) h
      have hh : i+1≤i := by simpa [a,b,Fin.le_def] using hm
      omega
  · intro h p q hpq
    apply adjacent_le (e.mono p q hpq)
    rintro ⟨hp,hq⟩
    have hep : e.order p=a := Fin.ext hp
    have heq : e.order q=b := Fin.ext hq
    apply h.1
    change R (e.order.symm a) (e.order.symm b)
    rw [← hep, ← heq, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hpq

noncomputable def sourceTau {α : Type} {R : α → α → Prop} {N : ℕ}
    (i : ℕ) (e : LinearExtension R N) : LinearExtension R N := by
  classical
  exact if h : OrderValid R (e.order.trans (adjacent N i)) then
    ⟨e.order.trans (adjacent N i),h⟩ else e

noncomputable def sourceRun {α : Type} {R : α → α → Prop} {N : ℕ}
    (s : List ℕ) (e : LinearExtension R N) : LinearExtension R N :=
  s.foldl (fun v i => sourceTau i v) e

noncomputable def sourceEvac {α : Type} {R : α → α → Prop} {N : ℕ}
    (e : LinearExtension R N) : LinearExtension R N := sourceRun (prefixSchedule N) e

def asLinear {n : ℕ} (e : Extension n) : LinearExtension (@posetLE n) (3*n) :=
  ⟨e.order,e.mono⟩
def fromLinear {n : ℕ} (e : LinearExtension (@posetLE n) (3*n)) : Extension n :=
  ⟨e.order,e.mono⟩

noncomputable def extensionTau {n : ℕ} (i : ℕ) (e : Extension n) : Extension n :=
  fromLinear (sourceTau i (asLinear e))

/-- Every chain's increasing occurrence positions determine its labels uniquely. -/
theorem order_eq_labelOrder {n : ℕ} (e : Element n ≃ Fin (3*n))
    (hw : Valid (eraseOrder e)) (hc : ∀ c : Fin 3, StrictMono (fun r : Fin n => e (c,r))) :
    e=labelOrder ⟨eraseOrder e,hw⟩ := by
  apply Equiv.ext
  rintro ⟨c,r⟩
  change e (c,r)=occPos ⟨eraseOrder e,hw⟩ c r
  have h := Finset.orderEmbOfFin_unique
    (occurrences_card (⟨eraseOrder e,hw⟩ : K n) c)
    (fun r : Fin n => show e (c,r) ∈ occurrences (eraseOrder e) c from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [eraseOrder]⟩) (hc c)
  exact congrFun h r

theorem eraseOrder_swap {n : ℕ} (e : Element n ≃ Fin (3*n)) (i : ℕ) :
    eraseOrder (e.trans (adjacent (3*n) i)) = swapWord i (eraseOrder e) := by
  funext j
  change (e.symm ((adjacent (3*n) i).symm j)).1 = (e.symm (adjacent (3*n) i j)).1
  have hs : (adjacent (3*n) i).symm = adjacent (3*n) i := by
    unfold adjacent
    split
    · rfl
    · rfl
  rw [hs]

/-- Adjacent swaps of different letters preserve increasing order within every chain. -/
theorem swapped_chain_strictMono {n i : ℕ} (e : Extension n) (hi : i+1<3*n)
    (hne : erase e ⟨i,by omega⟩ ≠ erase e ⟨i+1,hi⟩) (c : Fin 3) :
    StrictMono (fun r : Fin n => (e.order.trans (adjacent (3*n) i)) (c,r)) := by
  intro r s hrs
  apply lt_of_le_of_ne
  · apply adjacent_le (e.mono (c,r) (c,s) ⟨Or.inl rfl,le_of_lt hrs⟩)
    rintro ⟨hr,hs⟩
    have hr' : e.order (c,r)=⟨i,by omega⟩ := Fin.ext hr
    have hs' : e.order (c,s)=⟨i+1,hi⟩ := Fin.ext hs
    apply hne
    change (e.order.symm ⟨i,by omega⟩).1=(e.order.symm ⟨i+1,hi⟩).1
    rw [← hr',← hs',Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  · intro h
    exact (ne_of_lt hrs) (congrArg Prod.snd ((e.order.trans (adjacent (3*n) i)).injective h))

theorem swapWord_eq_self_of_same {n i : ℕ} (w : Word n) (hi : i+1<3*n)
    (he : w ⟨i,by omega⟩=w ⟨i+1,hi⟩) : swapWord i w=w := by
  funext j
  simp only [swapWord,Function.comp_apply,adjacent,dite_eq_left hi,Equiv.swap_apply_def]
  split_ifs with h h
  · subst j; exact he.symm
  · subst j; exact he
  · rfl

/-- A reusable erasure criterion. Repair is needed only for different-letter swaps. -/
theorem erase_sourceTau_of {n : ℕ} {R : Element n → Element n → Prop}
    (Q : Word n → Prop) [DecidablePred Q]
    (good : ∀ e : LinearExtension R (3*n), Q (eraseOrder e.order))
    (repair : ∀ (e : LinearExtension R (3*n)) (i : ℕ) (hi : i+1<3*n),
      eraseOrder e.order ⟨i,by omega⟩ ≠ eraseOrder e.order ⟨i+1,hi⟩ →
      Q (eraseOrder (e.order.trans (adjacent (3*n) i))) →
      OrderValid R (e.order.trans (adjacent (3*n) i)))
    (i : ℕ) (e : LinearExtension R (3*n)) :
    eraseOrder (sourceTau i e).order =
      (languageTau Q i ⟨eraseOrder e.order,good e⟩).val := by
  classical
  by_cases hs : OrderValid R (e.order.trans (adjacent (3*n) i))
  · have hq : Q (swapWord i (eraseOrder e.order)) := by
      rw [← eraseOrder_swap]
      exact good ⟨e.order.trans (adjacent (3*n) i),hs⟩
    simp only [sourceTau,dite_eq_left hs,languageTau,dite_eq_left hq,eraseOrder_swap]
  · by_cases hq : Q (swapWord i (eraseOrder e.order))
    · have he : swapWord i (eraseOrder e.order)=eraseOrder e.order := by
        by_cases hi : i+1<3*n
        · by_cases hd : eraseOrder e.order ⟨i,by omega⟩ ≠ eraseOrder e.order ⟨i+1,hi⟩
          · exact False.elim (hs (repair e i hi hd (by rwa [eraseOrder_swap])))
          · exact swapWord_eq_self_of_same _ hi (not_ne_iff.mp hd)
        · funext j
          simp [swapWord,adjacent,hi]
      simp only [sourceTau,dite_eq_right hs,languageTau,he,dite_eq_left (good e)]
    · simp only [sourceTau,dite_eq_right hs,languageTau,dite_eq_right hq]

theorem erase_sourceTau {n : ℕ} (i : ℕ) (e : LinearExtension (@posetLE n) (3*n)) :
    eraseOrder (sourceTau i e).order =
      (tau i ⟨eraseOrder e.order,erase_valid (fromLinear e)⟩).val := by
  apply erase_sourceTau_of Valid (fun e => erase_valid (fromLinear e))
  intro f j hj hd hw
  have he := order_eq_labelOrder (f.order.trans (adjacent (3*n) j)) hw
    (swapped_chain_strictMono (fromLinear f) hj hd)
  rw [he]
  exact (label ⟨_,hw⟩).mono

theorem erase_injective {n : ℕ} : Function.Injective (@erase n) := by
  intro e f h
  have he : (⟨erase e,erase_valid e⟩ : K n)=⟨erase f,erase_valid f⟩ := Subtype.ext h
  rw [← label_erase e,← label_erase f,he]

theorem tau_bridge {n : ℕ} (i : ℕ) (w : K n) :
    wordExtensionEquiv n (tau i w)=extensionTau i (wordExtensionEquiv n w) := by
  apply erase_injective
  have h := erase_sourceTau i (asLinear (label w))
  have he : (⟨erase (label w),erase_valid (label w)⟩ : K n)=w :=
    Subtype.ext (erase_labelOrder w)
  change erase (label (tau i w))=eraseOrder (sourceTau i (asLinear (label w))).order
  rw [show erase (label (tau i w))=(tau i w).val from erase_labelOrder _]
  exact (h.trans (congrArg (fun v : K n => (tau i v).val) he)).symm

noncomputable def extensionRun {n : ℕ} (s : List ℕ) (e : Extension n) : Extension n :=
  s.foldl (fun v i => extensionTau i v) e
noncomputable def extensionEvac {n : ℕ} (e : Extension n) : Extension n :=
  extensionRun (prefixSchedule (3*n)) e

theorem run_bridge {n : ℕ} (s : List ℕ) (w : K n) :
    wordExtensionEquiv n (run s w)=extensionRun s (wordExtensionEquiv n w) := by
  induction s generalizing w with
  | nil => rfl
  | cons i s ih =>
    change wordExtensionEquiv n (run s (tau i w))=extensionRun s (extensionTau i (wordExtensionEquiv n w))
    rw [ih,tau_bridge]

theorem evac_bridge {n : ℕ} (w : K n) :
    wordExtensionEquiv n (evac w)=extensionEvac (wordExtensionEquiv n w) := run_bridge _ w

theorem extensionRun_asLinear {n : ℕ} (s : List ℕ) (e : Extension n) :
    asLinear (extensionRun s e)=sourceRun s (asLinear e) := by
  induction s generalizing e with
  | nil => rfl
  | cons i s ih => exact ih (extensionTau i e)

#print axioms tau_bridge
#print axioms evac_bridge
#print axioms swap_orderValid_iff
end Kreweras
```

### `KrewerasDual.lean`

```lean
import KrewerasOperators

namespace Kreweras

def reverseLinear {α : Type} {R : α → α → Prop} {N : ℕ}
    (e : LinearExtension R N) : LinearExtension (fun p q => R q p) N where
  order := e.order.trans Fin.revPerm
  mono p q h := Fin.rev_le_rev.mpr (e.mono q p h)

@[simp] theorem reverseLinear_reverseLinear {α : Type} {R : α → α → Prop} {N : ℕ}
    (e : LinearExtension R N) : reverseLinear (reverseLinear e)=e := by
  apply LinearExtension.ext
  apply Equiv.ext
  intro p
  exact Fin.rev_rev _

@[simp] theorem erase_reverseOrder {n : ℕ} (e : Element n ≃ Fin (3*n)) :
    eraseOrder (e.trans Fin.revPerm)=reverseWord (eraseOrder e) := by
  funext i
  rfl

abbrev DualExtension (n : ℕ) := LinearExtension (fun p q : Element n => posetLE q p) (3*n)

theorem erase_dual_valid {n : ℕ} (e : DualExtension n) :
    Valid (reverseWord (eraseOrder e.order)) := by
  have h := erase_valid (fromLinear (reverseLinear e))
  exact h

theorem swapped_chain_strictAnti {n i : ℕ} (e : DualExtension n) (hi : i+1<3*n)
    (hne : eraseOrder e.order ⟨i,by omega⟩ ≠ eraseOrder e.order ⟨i+1,hi⟩) (c : Fin 3) :
    StrictAnti (fun r : Fin n => (e.order.trans (adjacent (3*n) i)) (c,r)) := by
  intro r s hrs
  apply lt_of_le_of_ne
  · apply adjacent_le (e.mono (c,s) (c,r) ⟨Or.inl rfl,le_of_lt hrs⟩)
    rintro ⟨hs,hr⟩
    have hs' : e.order (c,s)=⟨i,by omega⟩ := Fin.ext hs
    have hr' : e.order (c,r)=⟨i+1,hi⟩ := Fin.ext hr
    apply hne
    change (e.order.symm ⟨i,by omega⟩).1=(e.order.symm ⟨i+1,hi⟩).1
    rw [← hs',← hr',Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  · intro h
    exact (ne_of_gt hrs) (congrArg Prod.snd ((e.order.trans (adjacent (3*n) i)).injective h))

theorem erase_sourceTau_dual {n : ℕ} (i : ℕ) (e : DualExtension n) :
    eraseOrder (sourceTau i e).order =
      (languageTau (fun v => Valid (reverseWord v)) i
        ⟨eraseOrder e.order,erase_dual_valid e⟩).val := by
  apply erase_sourceTau_of (fun v => Valid (reverseWord v)) erase_dual_valid
  intro f j hj hd hw
  let s := f.order.trans (adjacent (3*n) j)
  have hw' : Valid (eraseOrder (s.trans Fin.revPerm)) := hw
  have hc (c : Fin 3) : StrictMono (fun r : Fin n => (s.trans Fin.revPerm) (c,r)) := by
    intro r t hrt
    exact Fin.rev_lt_rev.mpr (swapped_chain_strictAnti f hj hd c hrt)
  have he := order_eq_labelOrder (s.trans Fin.revPerm) hw' hc
  intro p q hpq
  have hm := (label ⟨eraseOrder (s.trans Fin.revPerm),hw'⟩).mono q p hpq
  change labelOrder _ q ≤ labelOrder _ p at hm
  rw [← he] at hm
  exact Fin.rev_le_rev.mp hm

noncomputable def dualLabel {n : ℕ} (v : ReverseK n) : DualExtension n :=
  reverseLinear (asLinear (label ⟨reverseWord v.val,v.property⟩))

@[simp] theorem erase_dualLabel {n : ℕ} (v : ReverseK n) : eraseOrder (dualLabel v).order=v.val := by
  change eraseOrder ((labelOrder ⟨reverseWord v.val,v.property⟩).trans Fin.revPerm)=v.val
  rw [erase_reverseOrder,erase_labelOrder,reverseWord_reverseWord]

theorem dual_erase_injective {n : ℕ} {e f : DualExtension n}
    (h : eraseOrder e.order=eraseOrder f.order) : e=f := by
  have hh : erase (fromLinear (reverseLinear e))=erase (fromLinear (reverseLinear f)) :=
    congrArg reverseWord h
  have he := erase_injective hh
  have ho : (reverseLinear e).order=(reverseLinear f).order := congrArg Extension.order he
  have hr : reverseLinear e=reverseLinear f := LinearExtension.ext ho
  have ht := congrArg reverseLinear hr
  simpa only [reverseLinear_reverseLinear] using ht

theorem dual_tau_bridge {n : ℕ} (i : ℕ) (v : ReverseK n) :
    dualLabel (languageTau (fun w => Valid (reverseWord w)) i v)=sourceTau i (dualLabel v) := by
  apply dual_erase_injective
  rw [erase_dualLabel,erase_sourceTau_dual]
  have he : (⟨eraseOrder (dualLabel v).order,erase_dual_valid (dualLabel v)⟩ : ReverseK n)=v :=
    Subtype.ext (erase_dualLabel v)
  rw [he]

theorem dual_run_bridge {n : ℕ} (s : List ℕ) (v : ReverseK n) :
    dualLabel (languageRun (fun w => Valid (reverseWord w)) s v)=sourceRun s (dualLabel v) := by
  induction s generalizing v with
  | nil => rfl
  | cons i s ih =>
    change dualLabel (languageRun _ s (languageTau _ i v))=sourceRun s (sourceTau i (dualLabel v))
    rw [ih,dual_tau_bridge]

@[simp] theorem dualLabel_reversal {n : ℕ} (w : K n) :
    dualLabel (reversal w)=reverseLinear (asLinear (label w)) := by
  unfold dualLabel
  have he : (⟨reverseWord (reversal w).val,(reversal w).property⟩ : K n)=w :=
    Subtype.ext (reverseWord_reverseWord w.val)
  rw [he]

theorem reverse_dualLabel {n : ℕ} (v : ReverseK n) :
    fromLinear (reverseLinear (dualLabel v))=label (reversal.symm v) := by
  apply Extension.ext
  apply Equiv.ext
  intro p
  exact Fin.rev_rev _

noncomputable def extensionDualEvac {n : ℕ} (e : Extension n) : Extension n :=
  fromLinear (reverseLinear (sourceEvac (reverseLinear (asLinear e))))

theorem dualEvac_bridge {n : ℕ} (w : K n) :
    wordExtensionEquiv n (dualEvac w)=extensionDualEvac (wordExtensionEquiv n w) := by
  change label (reversal.symm (languageRun _ (prefixSchedule (3*n)) (reversal w)))=_
  rw [← reverse_dualLabel,dual_run_bridge,dualLabel_reversal]
  rfl

theorem swap_valid_iff_incomparable {n : ℕ} (w : K n) (i : Fin (3*n)) (j : Fin (3*n))
    (h : j.val=i.val+1) (hne : w.val i ≠ w.val j) :
    Valid (w.val ∘ Equiv.swap i j) ↔
      ¬posetLE ((wordExtensionEquiv n w).order.symm i) ((wordExtensionEquiv n w).order.symm j) ∧
      ¬posetLE ((wordExtensionEquiv n w).order.symm j) ((wordExtensionEquiv n w).order.symm i) := by
  have hi : i.val+1<3*n := by omega
  have hj : j=⟨i.val+1,hi⟩ := Fin.ext h
  subst j
  let e := asLinear (label w)
  have he : eraseOrder e.order=w.val := erase_labelOrder w
  have hiff := swap_orderValid_iff e hi
  change Valid (w.val ∘ Equiv.swap i ⟨i.val+1,hi⟩) ↔
    ¬posetLE (e.order.symm ⟨i.val,by omega⟩) (e.order.symm ⟨i.val+1,hi⟩) ∧
    ¬posetLE (e.order.symm ⟨i.val+1,hi⟩) (e.order.symm ⟨i.val,by omega⟩)
  rw [← hiff]
  constructor
  · intro hv
    have hw : Valid (eraseOrder (e.order.trans (adjacent (3*n) i.val))) := by
      rw [eraseOrder_swap,he]
      simpa [swapWord,adjacent,hi] using hv
    have hd : erase (fromLinear e) i ≠ erase (fromLinear e) ⟨i.val+1,hi⟩ := by
      change eraseOrder e.order i ≠ eraseOrder e.order ⟨i.val+1,hi⟩
      rwa [he]
    have hl := order_eq_labelOrder _ hw (swapped_chain_strictMono (fromLinear e) hi hd)
    rw [hl]
    exact (label ⟨_,hw⟩).mono
  · intro hv
    have hx := erase_valid (fromLinear ⟨_,hv⟩)
    change Valid (eraseOrder (e.order.trans (adjacent (3*n) i.val))) at hx
    rw [eraseOrder_swap,he] at hx
    simpa [swapWord,adjacent,hi] using hx

#print axioms dualEvac_bridge
#print axioms swap_valid_iff_incomparable
end Kreweras
```

### `KrewerasIdeals.lean`

```lean
import KrewerasPoset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Kreweras

structure IdealState where
  a : ℕ
  b : ℕ
  c : ℕ
  b_le_a : b≤a
  c_le_a : c≤a
  deriving DecidableEq

@[ext] theorem IdealState.ext {s t : IdealState} (ha : s.a=t.a) (hb : s.b=t.b) (hc : s.c=t.c) : s=t := by
  cases s; cases t; cases ha; cases hb; cases hc; rfl

def IdealState.coord (s : IdealState) (c : Fin 3) : ℕ :=
  if c=0 then s.a else if c=1 then s.b else s.c

@[simp] theorem coord_zero (s : IdealState) : s.coord 0=s.a := by simp [IdealState.coord]
@[simp] theorem coord_one (s : IdealState) : s.coord 1=s.b := by simp [IdealState.coord]
@[simp] theorem coord_two (s : IdealState) : s.coord 2=s.c := by simp [IdealState.coord]

theorem coord_le_a (s : IdealState) (c : Fin 3) : s.coord c≤s.a := by
  unfold IdealState.coord
  split_ifs
  · exact le_rfl
  · exact s.b_le_a
  · exact s.c_le_a

def DownClosed {n : ℕ} (I : Finset (Element n)) : Prop :=
  ∀ q ∈ I, ∀ p, posetLE p q → p∈I
abbrev FiniteIdeal (n : ℕ) := {I : Finset (Element n) // DownClosed I}

def chainSet {n : ℕ} (I : Finset (Element n)) (c : Fin 3) : Finset (Fin n) :=
  Finset.univ.filter fun r => (c,r)∈I

theorem chainSet_down {n : ℕ} (I : FiniteIdeal n) (c : Fin 3) {r s : Fin n}
    (hs : s∈chainSet I.val c) (hrs : r≤s) : r∈chainSet I.val c := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    I.property (c,s) (Finset.mem_filter.mp hs).2 (c,r) ⟨Or.inl rfl,hrs⟩⟩

theorem fin_downset_iff {n : ℕ} (s : Finset (Fin n))
    (hd : ∀ r ∈ s, ∀ t, t≤r → t∈s) (r : Fin n) : r∈s ↔ r.val<s.card := by
  constructor
  · intro hr
    have hs : (Finset.univ.filter fun j : Fin n => j.val<r.val+1) ⊆ s := by
      intro j hj
      exact hd r hr j (by have := (Finset.mem_filter.mp hj).2; omega)
    have hc := Finset.card_le_card hs
    rw [Fin.card_filter_val_lt,min_eq_right (by omega)] at hc
    omega
  · intro hr
    by_contra hn
    have hs : s ⊆ (Finset.univ.filter fun j : Fin n => j.val<r.val) := by
      intro j hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      by_contra h
      exact hn (hd j hj r (by omega))
    have hc := Finset.card_le_card hs
    rw [Fin.card_filter_val_lt,min_eq_right (le_of_lt r.isLt)] at hc
    omega

def idealState {n : ℕ} (I : FiniteIdeal n) : IdealState where
  a := (chainSet I.val 0).card
  b := (chainSet I.val 1).card
  c := (chainSet I.val 2).card
  b_le_a := Finset.card_le_card (by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      I.property (1,r) (Finset.mem_filter.mp hr).2 (0,r) ⟨Or.inr rfl,le_rfl⟩⟩)
  c_le_a := Finset.card_le_card (by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      I.property (2,r) (Finset.mem_filter.mp hr).2 (0,r) ⟨Or.inr rfl,le_rfl⟩⟩)

theorem idealState_coord {n : ℕ} (I : FiniteIdeal n) (c : Fin 3) :
    (idealState I).coord c=(chainSet I.val c).card := by
  have ht := c.isLt
  rcases (show c=0 ∨ c=1 ∨ c=2 by omega) with rfl|rfl|rfl <;>
    simp [idealState]

def stateIdeal (n : ℕ) (s : IdealState) : Finset (Element n) :=
  Finset.univ.filter fun p => p.2.val<s.coord p.1

theorem stateIdeal_down (n : ℕ) (s : IdealState) : DownClosed (stateIdeal n s) := by
  intro q hq p hpq
  have hq' := (Finset.mem_filter.mp hq).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  have hc : s.coord q.1≤s.coord p.1 := by
    rcases hpq.1 with h|h
    · rw [h]
    · rw [h,coord_zero]
      exact coord_le_a s q.1
  have hi : p.2.val≤q.2.val := hpq.2
  omega

theorem idealState_cap {n : ℕ} (I : FiniteIdeal n) : (idealState I).a≤n := by
  exact (Finset.card_le_univ (chainSet I.val 0)).trans_eq (Fintype.card_fin n)

theorem stateIdeal_idealState {n : ℕ} (I : FiniteIdeal n) : stateIdeal n (idealState I)=I.val := by
  ext p
  unfold stateIdeal
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and,idealState_coord]
  exact (fin_downset_iff (chainSet I.val p.1)
    (fun r hr t ht => chainSet_down I p.1 hr ht) p.2).symm.trans
    (by simp [chainSet])

theorem chainSet_stateIdeal (n : ℕ) (s : IdealState) (c : Fin 3) :
    chainSet (stateIdeal n s) c=Finset.univ.filter (fun r : Fin n => r.val<s.coord c) := by
  ext r
  simp [chainSet,stateIdeal]

theorem idealState_stateIdeal (n : ℕ) (s : IdealState) (hs : s.a≤n) :
    idealState ⟨stateIdeal n s,stateIdeal_down n s⟩=s := by
  apply IdealState.ext <;>
    simp only [idealState,chainSet_stateIdeal,Fin.card_filter_val_lt,coord_zero,coord_one,coord_two]
  · exact min_eq_right hs
  · exact min_eq_right (s.b_le_a.trans hs)
  · exact min_eq_right (s.c_le_a.trans hs)

theorem ideal_coordinates {n : ℕ} (I : FiniteIdeal n) :
    ∃! s : IdealState, s.a≤n ∧ I.val=stateIdeal n s := by
  refine ⟨idealState I,⟨idealState_cap I,(stateIdeal_idealState I).symm⟩,?_⟩
  intro s hs
  have h : I=(⟨stateIdeal n s,stateIdeal_down n s⟩ : FiniteIdeal n) := Subtype.ext hs.2
  rw [h,idealState_stateIdeal n s hs.1]

theorem fiber_card {n : ℕ} (I : Finset (Element n)) (c : Fin 3) :
    (I.filter fun p => p.1=c).card=(chainSet I c).card := by
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    have h := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [← h.2] using h.1⟩
  · intro p hp q hq he
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
  · intro r hr
    refine ⟨(c,r),Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).2,rfl⟩,rfl⟩

theorem stateIdeal_card (n : ℕ) (s : IdealState) (h : s.a≤n) :
    (stateIdeal n s).card=s.a+s.b+s.c := by
  have hc : (stateIdeal n s).card = ∑ c : Fin 3, ((stateIdeal n s).filter fun p => p.1=c).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [hc]
  simp only [fiber_card,chainSet_stateIdeal,Fin.card_filter_val_lt,Fin.sum_univ_three,
    coord_zero,coord_one,coord_two]
  rw [min_eq_right h,min_eq_right (s.b_le_a.trans h),min_eq_right (s.c_le_a.trans h)]

/-- Five and only five candidate domino additions; source equivalence remains to be proved. -/
def DominoStep (s t : IdealState) : Prop :=
  (t.a=s.a+2 ∧ t.b=s.b ∧ t.c=s.c) ∨
  (t.a=s.a ∧ t.b=s.b+2 ∧ t.c=s.c) ∨
  (t.a=s.a ∧ t.b=s.b ∧ t.c=s.c+2) ∨
  (s.a=s.b ∧ t.a=s.a+1 ∧ t.b=s.b+1 ∧ t.c=s.c) ∨
  (s.a=s.c ∧ t.a=s.a+1 ∧ t.b=s.b ∧ t.c=s.c+1)

theorem domino_step_size {s t : IdealState} (h : DominoStep s t) :
    t.a+t.b+t.c=s.a+s.b+s.c+2 := by
  rcases h with h|h|h|h|h <;> omega

theorem domino_step_mono {s t : IdealState} (h : DominoStep s t) :
    s.a≤t.a ∧ s.b≤t.b ∧ s.c≤t.c := by
  rcases h with h|h|h|h|h <;> omega

#print axioms stateIdeal_card
#print axioms ideal_coordinates
#print axioms domino_step_size
#print axioms domino_step_mono
end Kreweras
```

### `KrewerasParity.lean`

```lean
import KrewerasIdeals

namespace Kreweras

def HasSector (s : IdealState) : Prop :=
  (s.a%2=0 ∧ s.b%2=0 ∧ s.c%2=0) ∨
  (s.a%2=1 ∧ s.b%2=1 ∧ s.c%2=0) ∨
  (s.a%2=1 ∧ s.b%2=0 ∧ s.c%2=1)

def zeroState : IdealState := ⟨0,0,0,le_rfl,le_rfl⟩

def SingletonSector (s : IdealState) : Prop := s.a%2=1 ∧ s.b%2=0 ∧ s.c%2=0

theorem sector_step_closed {s t : IdealState} (hs : HasSector s) (h : DominoStep s t) : HasSector t := by
  rcases hs with hs|hs|hs <;> rcases h with h|h|h|h|h <;> unfold HasSector <;> omega

inductive Reachable : IdealState → Prop where
  | zero : Reachable zeroState
  | step {s t : IdealState} : Reachable s → DominoStep s t → Reachable t

theorem reachable_sector {s : IdealState} (h : Reachable s) : HasSector s := by
  induction h with
  | zero => exact Or.inl ⟨rfl,rfl,rfl⟩
  | step _ h ih => exact sector_step_closed ih h

theorem sector_closed {s t : IdealState} (h : Reachable s) (ht : DominoStep s t) : HasSector t :=
  sector_step_closed (reachable_sector h) ht

theorem singleton_sector_closed {s t : IdealState} (hs : SingletonSector s)
    (h : DominoStep s t) : SingletonSector t := by
  rcases h with h|h|h|h|h <;> unfold SingletonSector at * <;> omega

/-- This is the parity obstruction for a chain whose first block is the singleton A₁.
It is not yet an assertion about evacuation fixed points. -/
theorem singleton_no_odd_diagonal {s : IdealState} (h : SingletonSector s)
    (he : s.a=s.b) : False := by
  unfold SingletonSector at h
  omega

#print axioms sector_closed
#print axioms singleton_sector_closed
#print axioms singleton_no_odd_diagonal
end Kreweras
```

### `KrewerasSectors.lean`

```lean
import KrewerasIdeals

namespace Kreweras
inductive Sector where
  | E | X | Y
  deriving DecidableEq

structure SectorPoint where
  sector : Sector
  x : ℕ
  y : ℕ
  deriving DecidableEq

def unfold (p : SectorPoint) : ℤ×ℤ := match p.sector with
  | .E => (p.x,p.y)
  | .X => (-(p.x : ℤ)-1,(p.y : ℤ)-p.x)
  | .Y => ((p.x : ℤ)-p.y,-(p.y : ℤ)-1)

def Slit (p : ℤ×ℤ) : Prop := ¬(p.1=p.2 ∧ p.1<0)

theorem unfold_injective : Function.Injective unfold := by
  rintro ⟨s,x,y⟩ ⟨t,u,v⟩ h
  cases s <;> cases t <;> simp only [unfold,Prod.mk.injEq] at h
  all_goals first | (exfalso; omega) | (congr 1 <;> omega)

theorem unfold_slit (p : SectorPoint) : Slit (unfold p) := by
  rcases p with ⟨s,x,y⟩
  cases s <;> simp only [unfold,Slit] <;> omega

theorem unfold_surjective (p : ℤ×ℤ) (h : Slit p) : ∃ q, unfold q=p := by
  rcases p with ⟨u,v⟩
  by_cases hE : 0≤u ∧ 0≤v
  · refine ⟨⟨.E,u.toNat,v.toNat⟩,?_⟩
    simp only [unfold,Prod.mk.injEq]
    exact ⟨Int.toNat_of_nonneg hE.1,Int.toNat_of_nonneg hE.2⟩
  · by_cases hX : u≤-1 ∧ u+1≤v
    · refine ⟨⟨.X,(-u-1).toNat,(v-u-1).toNat⟩,?_⟩
      have hx : 0≤-u-1 := by omega
      have hy : 0≤v-u-1 := by omega
      simp only [unfold,Int.toNat_of_nonneg hx,Int.toNat_of_nonneg hy,Prod.mk.injEq]
      constructor <;> omega
    · have hY : v≤-1 ∧ v+1≤u := by unfold Slit at h; dsimp at h; omega
      refine ⟨⟨.Y,(u-v-1).toNat,(-v-1).toNat⟩,?_⟩
      have hx : 0≤u-v-1 := by omega
      have hy : 0≤-v-1 := by omega
      simp only [unfold,Int.toNat_of_nonneg hx,Int.toNat_of_nonneg hy,Prod.mk.injEq]
      constructor <;> omega

def PlaneStep (p q : ℤ×ℤ) : Prop :=
  (q.1=p.1+1 ∧ q.2=p.2+1) ∨
  (q.1=p.1-1 ∧ q.2=p.2) ∨
  (q.1=p.1 ∧ q.2=p.2-1)

def SectorStep (p q : SectorPoint) : Prop :=
  (p.sector=q.sector ∧
    ((q.x=p.x+1 ∧ q.y=p.y+1) ∨ (p.x=q.x+1 ∧ q.y=p.y) ∨
      (q.x=p.x ∧ p.y=q.y+1))) ∨
  (p.sector=.E ∧ q.sector=.X ∧ p.x=0 ∧ q.x=0 ∧ q.y=p.y) ∨
  (p.sector=.X ∧ q.sector=.E ∧ p.x=0 ∧ q.x=0 ∧ q.y=p.y+1) ∨
  (p.sector=.E ∧ q.sector=.Y ∧ p.y=0 ∧ q.y=0 ∧ q.x=p.x) ∨
  (p.sector=.Y ∧ q.sector=.E ∧ p.y=0 ∧ q.y=0 ∧ q.x=p.x+1)

theorem unfold_step_iff (p q : SectorPoint) :
    SectorStep p q ↔ PlaneStep (unfold p) (unfold q) := by
  rcases p with ⟨s,x,y⟩
  rcases q with ⟨t,u,v⟩
  cases s <;> cases t <;> simp only [SectorStep,PlaneStep,unfold,
    reduceCtorEq,
    true_and,false_and,or_false,false_or] <;> try omega
  all_goals
    constructor
    · intro h; exact False.elim h
    · intro h; rcases h with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩ <;> omega

theorem lift_unique (p : SectorPoint) (v : ℤ×ℤ) (hv : Slit v)
    (hs : PlaneStep (unfold p) v) : ∃! q, SectorStep p q ∧ unfold q=v := by
  obtain ⟨q,hq⟩ := unfold_surjective v hv
  refine ⟨q,⟨(unfold_step_iff p q).mpr (hq.symm ▸ hs),hq⟩,?_⟩
  intro r hr
  exact unfold_injective (hr.2.trans hq.symm)

theorem recover_E (d A B C x y : ℕ) (hx : A=B+x) (hy : A=C+y) (ht : d=A+B+C) :
    3*A=d+x+y := by omega

theorem recover_XY (d A B C x y : ℕ) (hx : A=B+x) (hy : A=C+y) (ht : d=A+B+C+1) :
    3*A=d+x+y-1 := by omega

#print axioms unfold_injective
#print axioms unfold_surjective
#print axioms unfold_step_iff
#print axioms lift_unique
end Kreweras
```

### `KrewerasUnfold.lean`

```lean
import KrewerasSectors
import KrewerasParity

namespace Kreweras

def encode (s : IdealState) : SectorPoint :=
  ⟨if s.a%2=0 then .E else if s.b%2=1 then .X else .Y,
    s.a/2-s.b/2,s.a/2-s.c/2⟩

set_option maxHeartbeats 2000000 in
theorem encode_step {s t : IdealState} (hs : HasSector s) (h : DominoStep s t) :
    SectorStep (encode s) (encode t) := by
  have ht := sector_step_closed hs h
  have hsba := s.b_le_a
  have hsca := s.c_le_a
  have htba := t.b_le_a
  have htca := t.c_le_a
  unfold HasSector at hs ht
  unfold encode
  split_ifs <;> simp only [SectorStep,reduceCtorEq,true_and,false_and,false_or,or_false] <;>
    rcases h with h|h|h|h|h <;> omega

theorem encode_plane_step {s t : IdealState} (hs : HasSector s) (h : DominoStep s t) :
    PlaneStep (unfold (encode s)) (unfold (encode t)) :=
  (unfold_step_iff _ _).mp (encode_step hs h)

set_option maxHeartbeats 2000000 in
theorem encode_time_injective {s t : IdealState} (_hs : HasSector s) (ht : HasSector t)
    (hsize : s.a+s.b+s.c=t.a+t.b+t.c)
    (hp : unfold (encode s)=unfold (encode t)) : s=t := by
  have he := unfold_injective hp
  have hsba := s.b_le_a
  have hsca := s.c_le_a
  have htba := t.b_le_a
  have htca := t.c_le_a
  unfold HasSector at _hs ht
  unfold encode at he
  split_ifs at he <;> simp only [SectorPoint.mk.injEq,reduceCtorEq,true_and,false_and] at he
  all_goals apply IdealState.ext <;> omega

@[simp] theorem encode_even_diagonal (m : ℕ) :
    encode ⟨2*m,2*m,2*m,le_rfl,le_rfl⟩=⟨.E,0,0⟩ := by
  simp [encode]

@[simp] theorem encode_odd_adjacent (m : ℕ) :
    encode ⟨2*m+1,2*m+1,2*m,le_rfl,by omega⟩=⟨.X,0,0⟩ := by
  simp [encode,Nat.add_div]

theorem even_diagonal_position (m : ℕ) :
    unfold (encode ⟨2*m,2*m,2*m,le_rfl,le_rfl⟩)=(0,0) := by
  rw [encode_even_diagonal]
  rfl

theorem odd_adjacent_position (m : ℕ) :
    unfold (encode ⟨2*m+1,2*m+1,2*m,le_rfl,by omega⟩)=(-1,0) := by
  rw [encode_odd_adjacent]
  rfl

#print axioms encode_step
#print axioms encode_time_injective
#print axioms even_diagonal_position
#print axioms odd_adjacent_position
end Kreweras
```

### `KrewerasChains.lean`

```lean
import KrewerasDual
import KrewerasIdeals

namespace Kreweras

def prefixIdeal {n : ℕ} (e : Extension n) (k : ℕ) : FiniteIdeal n :=
  ⟨Finset.univ.filter (fun p => (e.order p).val<k),by
    intro q hq p hpq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_le_of_lt (e.mono p q hpq) (Finset.mem_filter.mp hq).2⟩⟩

theorem prefixIdeal_mono {n : ℕ} (e : Extension n) {k l : ℕ} (h : k≤l) :
    (prefixIdeal e k).val ⊆ (prefixIdeal e l).val := by
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_lt_of_le (Finset.mem_filter.mp hp).2 h⟩

theorem prefixIdeal_card {n : ℕ} (e : Extension n) (k : ℕ) (hk : k≤3*n) :
    (prefixIdeal e k).val.card=k := by
  have he : (prefixIdeal e k).val.card=(Finset.univ.filter fun i : Fin (3*n) => i.val<k).card := by
    apply Finset.card_bij (fun p _ => e.order p)
    · intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩
    · intro p _ q _ h
      exact e.order.injective h
    · intro i hi
      refine ⟨e.order.symm i,?_,e.order.apply_symm_apply i⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using (Finset.mem_filter.mp hi).2⟩
  rw [he,Fin.card_filter_val_lt,min_eq_right hk]

theorem prefixIdeal_coordinates {n : ℕ} (e : Extension n) (k : ℕ) (c : Fin 3) :
    (idealState (prefixIdeal e k)).coord c=count (erase e) c k := by
  rw [idealState_coord,erase,count_eraseOrder]
  congr 1
  ext r
  simp [chainSet,prefixIdeal]

theorem source_minimal_element (n : ℕ) (hn : 0<n) (p : Element n) :
    (∀ q, posetLE q p → q=p) ↔ p=(0,⟨0,hn⟩) := by
  constructor
  · intro h
    have he := h (0,⟨0,hn⟩) ⟨Or.inr rfl,by change 0≤p.2.val; omega⟩
    exact he.symm
  · rintro rfl q hq
    apply Prod.ext
    · rcases hq.1 with he|he <;> exact he
    · apply Fin.ext
      change q.2.val=0
      have hh : q.2.val≤0 := hq.2
      omega

theorem dual_initial_singleton (n : ℕ) (hn : 0<n) (p : Element n) :
    (∀ q, posetLE p q → q=p) ↔
      p=(1,⟨n-1,by omega⟩) ∨ p=(2,⟨n-1,by omega⟩) := by
  constructor
  · intro h
    have he := h (p.1,⟨n-1,by omega⟩) ⟨Or.inl rfl,by change p.2.val≤n-1; have := p.2.isLt; omega⟩
    have hi : p.2.val=n-1 := congrArg (fun q : Element n => q.2.val) he.symm
    have hc : p.1≠0 := by
      intro hc
      have hq := h (1,p.2) ⟨Or.inr hc,le_rfl⟩
      have hp := congrArg Prod.fst hq
      rw [hc] at hp
      exact (by decide : (1 : Fin 3) ≠ 0) hp
    have ht := p.1.isLt
    have hcolor : p.1=1 ∨ p.1=2 := by omega
    rcases hcolor with hh|hh
    · exact Or.inl (Prod.ext hh (Fin.ext hi))
    · exact Or.inr (Prod.ext hh (Fin.ext hi))
  · rintro (rfl|rfl) q hq
    all_goals
      apply Prod.ext
      · rcases hq.1 with hh|hh
        · exact hh.symm
        · have hh' := congrArg Fin.val hh
          dsimp at hh'
          omega
      · apply Fin.ext
        change q.2.val=n-1
        have hle : n-1≤q.2.val := hq.2
        have hlt := q.2.isLt
        omega

/-- Schedules for the remaining specialized Stanley conjugation proof. These are
actual finite operator words, but the universal conjugation identity is not asserted. -/
def dominoPairSchedule (N : ℕ) : List ℕ :=
  (List.range (N/2)).map fun j => N-2-2*j

def dominoConjugatorSchedule (N : ℕ) : List ℕ :=
  (List.range (N/2)).flatMap fun j => (List.range (2*j+1)).reverse

def DominoConjugationGoal : Prop := ∀ n : ℕ, ∀ w : K n,
  evac (run (dominoConjugatorSchedule (3*n)) w) =
    run (dominoConjugatorSchedule (3*n)) (run (dominoPairSchedule (3*n)) w)

#print axioms source_minimal_element
#print axioms dual_initial_singleton
#print axioms prefixIdeal_card
#print axioms prefixIdeal_coordinates
#print DominoConjugationGoal
end Kreweras
```

### `KrewerasWalks.lean`

```lean
import KrewerasUnfold

namespace Kreweras

abbrev SectorWalk (d : ℕ) := {p : Fin (d+1) → SectorPoint //
  p 0=⟨.E,0,0⟩ ∧ ∀ i : Fin d, SectorStep (p i.castSucc) (p i.succ)}

abbrev SlitWalk (d : ℕ) := {p : Fin (d+1) → ℤ×ℤ //
  p 0=(0,0) ∧ (∀ i, Slit (p i)) ∧ ∀ i : Fin d, PlaneStep (p i.castSucc) (p i.succ)}

def unfoldWalk {d : ℕ} (p : SectorWalk d) : SlitWalk d :=
  ⟨fun i => unfold (p.val i),by
    constructor
    · change unfold (p.val 0)=(0,0)
      rw [p.property.1]
      rfl
    · exact ⟨fun i => unfold_slit _,fun i => (unfold_step_iff _ _).mp (p.property.2 i)⟩⟩

theorem unfoldWalk_bijective (d : ℕ) : Function.Bijective (@unfoldWalk d) := by
  constructor
  · intro p q h
    apply Subtype.ext
    funext i
    exact unfold_injective (congrFun (congrArg Subtype.val h) i)
  · intro p
    classical
    choose q hq using fun i => unfold_surjective (p.val i) (p.property.2.1 i)
    have hstart : q 0=⟨.E,0,0⟩ := by
      apply unfold_injective
      exact (hq 0).trans p.property.1
    have hstep (i : Fin d) : SectorStep (q i.castSucc) (q i.succ) := by
      apply (unfold_step_iff _ _).mpr
      rw [hq,hq]
      exact p.property.2.2 i
    refine ⟨⟨q,hstart,hstep⟩,?_⟩
    apply Subtype.ext
    exact funext hq

noncomputable def sectorSlitWalkEquiv (d : ℕ) : SectorWalk d ≃ SlitWalk d :=
  Equiv.ofBijective unfoldWalk (unfoldWalk_bijective d)

theorem walk_origin_iff {d : ℕ} (p : SectorWalk d) :
    (unfoldWalk p).val (Fin.last d)=(0,0) ↔ p.val (Fin.last d)=⟨.E,0,0⟩ := by
  change unfold (p.val (Fin.last d))=unfold ⟨.E,0,0⟩ ↔ _
  exact unfold_injective.eq_iff

theorem walk_adjacent_iff {d : ℕ} (p : SectorWalk d) :
    (unfoldWalk p).val (Fin.last d)=(-1,0) ↔ p.val (Fin.last d)=⟨.X,0,0⟩ := by
  change unfold (p.val (Fin.last d))=unfold ⟨.X,0,0⟩ ↔ _
  exact unfold_injective.eq_iff

#print axioms sectorSlitWalkEquiv
#print axioms walk_origin_iff
#print axioms walk_adjacent_iff
end Kreweras
```

### `KrewerasNonempty.lean`

```lean
import KrewerasPoset
import Mathlib.Logic.Equiv.Fin.Basic

namespace Kreweras

def blockExtension (n : ℕ) : Extension n where
  order := finProdFinEquiv
  mono p q hpq := by
    change p.2.val+n*p.1.val ≤ q.2.val+n*q.1.val
    rcases hpq.1 with h|h
    · rw [h]
      exact Nat.add_le_add_right hpq.2 _
    · rw [h]
      simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero]
      exact (show p.2.val≤q.2.val from hpq.2).trans (Nat.le_add_right _ _)

theorem K_nonempty (n : ℕ) : Nonempty (K n) := ⟨⟨erase (blockExtension n),erase_valid _⟩⟩

#print axioms K_nonempty
end Kreweras
```

### `KrewerasCommutation.lean`

```lean
import KrewerasOperators

namespace Kreweras
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

theorem adjacent_apply_of_far {N i : ℕ} (x : Fin N)
    (h0 : x.val≠i) (h1 : x.val≠i+1) : adjacent N i x=x := by
  unfold adjacent
  split
  · simp only [Equiv.swap_apply_def]
    split_ifs <;> simp only [Fin.ext_iff] at * <;> omega
  · rfl

theorem adjacent_commute (N i j : ℕ) (h : i+1<j ∨ j+1<i) :
    Function.Commute (adjacent N i) (adjacent N j) := by
  intro x
  unfold adjacent
  split_ifs <;> try rfl
  all_goals
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp only [Fin.ext_iff] at * <;> omega

theorem adjacent_symm (N i : ℕ) : (adjacent N i).symm=adjacent N i := by
  unfold adjacent
  split <;> rfl

theorem sourceTau_out {α : Type} {R : α → α → Prop} {N : ℕ}
    (i : ℕ) (hi : ¬i+1<N) (e : LinearExtension R N) : sourceTau i e=e := by
  classical
  have hv : OrderValid R (e.order.trans (adjacent N i)) := by
    simpa [OrderValid,adjacent,hi] using e.mono
  apply LinearExtension.ext
  simp only [sourceTau,dite_eq_left hv]
  simp [adjacent,hi]

theorem sourceTau_symm_far {α : Type} {R : α → α → Prop} {N i : ℕ}
    (e : LinearExtension R N) (x : Fin N) (h0 : x.val≠i) (h1 : x.val≠i+1) :
    (sourceTau i e).order.symm x=e.order.symm x := by
  classical
  unfold sourceTau
  split
  · change e.order.symm ((adjacent N i).symm x)=_
    rw [adjacent_symm,adjacent_apply_of_far x h0 h1]
  · rfl

theorem sourceTau_involutive {α : Type} {R : α → α → Prop} {N : ℕ} (i : ℕ) :
    Function.Involutive (@sourceTau α R N i) := by
  classical
  intro e
  by_cases hv : OrderValid R (e.order.trans (adjacent N i))
  · have he : (e.order.trans (adjacent N i)).trans (adjacent N i)=e.order := by
      apply Equiv.ext
      intro p
      exact adjacent_involutive N i _
    have hv' : OrderValid R ((sourceTau i e).order.trans (adjacent N i)) := by
      simpa only [sourceTau,dite_eq_left hv,he] using (show OrderValid R e.order from e.mono)
    apply LinearExtension.ext
    rw [sourceTau,dite_eq_left hv']
    change (sourceTau i e).order.trans (adjacent N i)=e.order
    simpa only [sourceTau,dite_eq_left hv] using he
  · simp only [sourceTau,dite_eq_right hv]

theorem sourceTau_distant {α : Type} {R : α → α → Prop} {N i j : ℕ}
    (h : i+1<j ∨ j+1<i) : Function.Commute (@sourceTau α R N i) (sourceTau j) := by
  classical
  intro e
  by_cases hi : i+1<N
  swap
  · rw [sourceTau_out i hi,sourceTau_out i hi]
  by_cases hj : j+1<N
  swap
  · rw [sourceTau_out j hj,sourceTau_out j hj]
  have hv (i j : ℕ) (hi : i+1<N) (h : i+1<j ∨ j+1<i) :
      OrderValid R ((sourceTau j e).order.trans (adjacent N i)) ↔
        OrderValid R (e.order.trans (adjacent N i)) := by
    rw [swap_orderValid_iff _ hi,swap_orderValid_iff _ hi]
    rw [sourceTau_symm_far e ⟨i,by omega⟩ (by dsimp; omega) (by dsimp; omega),
      sourceTau_symm_far e ⟨i+1,hi⟩ (by dsimp; omega) (by dsimp; omega)]
  have hvi := hv i j hi h
  have hvj := hv j i hj (by omega)
  have order_tau (k : ℕ) (f : LinearExtension R N) :
      (sourceTau k f).order = if OrderValid R (f.order.trans (adjacent N k))
        then f.order.trans (adjacent N k) else f.order := by
    unfold sourceTau
    split <;> simp_all
  apply LinearExtension.ext
  rw [order_tau i (sourceTau j e),order_tau j (sourceTau i e),hvi,hvj]
  by_cases vi : OrderValid R (e.order.trans (adjacent N i)) <;>
    by_cases vj : OrderValid R (e.order.trans (adjacent N j))
  all_goals simp only [vi,vj,ite_true,ite_false,order_tau]
  all_goals first
    | rfl
    | (apply Equiv.ext; intro p; exact adjacent_commute N i j h _)

#print axioms sourceTau_involutive
#print axioms sourceTau_distant
end Kreweras
```

### `KrewerasWordAlgebra.lean`

```lean
import KrewerasChains
import KrewerasCommutation

namespace Kreweras
namespace InvolutionWord
set_option linter.unusedSimpArgs false
variable {α : Type} (f : ℕ → α → α)

def act (s : List ℕ) (x : α) : α := s.foldl (fun x i => f i x) x
@[simp] theorem act_nil (x : α) : act f [] x=x := rfl
@[simp] theorem act_cons (i : ℕ) (s : List ℕ) (x : α) :
    act f (i::s) x=act f s (f i x) := rfl
@[simp] theorem act_append (s t : List ℕ) (x : α) :
    act f (s++t) x=act f t (act f s x) := List.foldl_append

variable (hinv : ∀ i, Function.Involutive (f i))
variable (hcomm : ∀ i j, i+1<j ∨ j+1<i → Function.Commute (f i) (f j))

include hinv in
theorem act_reverse_cancel (s : List ℕ) (x : α) :
    act f s.reverse (act f s x)=x := by
  induction s generalizing x with
  | nil => rfl
  | cons i s ih =>
    simp only [List.reverse_cons,act_append,act_cons,act_nil,ih]
    exact hinv i x

include hcomm in
theorem commute_act (i : ℕ) (s : List ℕ) (h : ∀ j∈s, j+1<i) (x : α) :
    act f s (f i x)=f i (act f s x) := by
  induction s generalizing x with
  | nil => rfl
  | cons j s ih =>
    simp only [act_cons]
    rw [hcomm j i (Or.inl (h j (by simp))) x]
    exact ih (fun k hk => h k (by simp [hk])) _

def column (N : ℕ) : List ℕ := (List.range N).flatMap fun j => (List.range j).reverse

theorem column_succ (N : ℕ) : column (N+1)=column N++(List.range N).reverse := by
  simp [column,List.range_succ,List.flatMap_append]

theorem column_bound {N j : ℕ} (h : j∈column N) : j+1<N := by
  obtain ⟨k,hk,hj⟩ := List.mem_flatMap.mp h
  have hk' := List.mem_range.mp hk
  have hj' := List.mem_range.mp (List.mem_reverse.mp hj)
  omega

include hcomm in
theorem slide (k : ℕ) (x : α) :
    act f (column k) (act f (List.range k) x)=
      act f (List.range k).reverse (act f (column k) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [column_succ,List.range_succ,List.reverse_append]
    simp only [act_append,List.reverse_cons,List.reverse_nil,List.nil_append,act_cons,act_nil]
    rw [commute_act f hcomm k (column k) (fun j hj => column_bound hj),ih]

include hcomm in
theorem prefix_column (N : ℕ) (x : α) :
    act f (prefixSchedule N) x=act f (column N) x := by
  induction N generalizing x with
  | zero => rfl
  | succ N ih =>
    have hp : prefixSchedule (N+1)=List.range N++prefixSchedule N := by
      simp [prefixSchedule,List.range_succ,List.reverse_append,List.flatMap_append]
    rw [hp,act_append,ih,slide f hcomm,column_succ,act_append]

include hcomm in
theorem prefix_snoc (N : ℕ) (x : α) :
    act f (prefixSchedule (N+1)) x=
      act f (List.range N).reverse (act f (prefixSchedule N) x) := by
  rw [prefix_column f hcomm,column_succ,act_append,prefix_column f hcomm]

theorem pair_two (N : ℕ) :
    dominoPairSchedule (N+2)=N::dominoPairSchedule N := by
  have hd : (N+2)/2=N/2+1 := by omega
  unfold dominoPairSchedule
  rw [hd,List.range_succ_eq_map,List.map_cons,List.map_map]
  simp only [Nat.add_sub_cancel]
  congr 1
  apply List.map_congr_left
  intro j hj
  dsimp
  omega

theorem conjugator_two (N : ℕ) :
    dominoConjugatorSchedule (N+2)=
      dominoConjugatorSchedule N++(List.range (2*(N/2)+1)).reverse := by
  have hd : (N+2)/2=N/2+1 := by omega
  simp only [dominoConjugatorSchedule,hd,List.range_succ,List.flatMap_append,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem conjugator_bound {N j : ℕ} (h : j∈dominoConjugatorSchedule N) : j+1<N := by
  obtain ⟨k,hk,hj⟩ := List.mem_flatMap.mp h
  have hk' := List.mem_range.mp hk
  have hj' := List.mem_range.mp (List.mem_reverse.mp hj)
  omega

theorem pair_bound {N j : ℕ} (h : j∈dominoPairSchedule N) : j+1<N := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
  have hk' := List.mem_range.mp hk
  omega

include hinv hcomm in
/-- The conjugator uses odd descending blocks. At odd N its largest block
has length N-2; at even N it has length N-1. -/
theorem conjugation (N : ℕ) (x : α) :
    act f (prefixSchedule N) (act f (dominoConjugatorSchedule N) x)=
      act f (dominoConjugatorSchedule N) (act f (dominoPairSchedule N) x) := by
  induction N using Nat.twoStepInduction generalizing x with
  | zero => rfl
  | one => rfl
  | more N ih _ =>
    rw [conjugator_two,pair_two]
    by_cases he : N%2=0
    · have hd : 2*(N/2)+1=N+1 := by omega
      rw [hd,act_append,act_cons]
      have hp : prefixSchedule (N+2)=List.range (N+1)++prefixSchedule (N+1) := by
        simp [prefixSchedule,List.range_succ,List.reverse_append,List.flatMap_append]
      rw [hp,act_append]
      have hc (y : α) : act f (List.range (N+1))
          (act f (List.range (N+1)).reverse y)=y := by
        simpa only [List.reverse_reverse] using
          act_reverse_cancel f hinv (List.range (N+1)).reverse y
      rw [hc,prefix_snoc f hcomm,ih]
      simp only [act_append,List.range_succ,List.reverse_append,List.reverse_cons,
        List.reverse_nil,List.nil_append,act_cons,act_nil]
      rw [commute_act f hcomm N (dominoPairSchedule N) (fun j hj => pair_bound hj),
        commute_act f hcomm N (dominoConjugatorSchedule N) (fun j hj => conjugator_bound hj)]
      exact congrArg (act f (List.range N).reverse) (hinv N _).symm
    · have hd : 2*(N/2)+1=N := by omega
      rw [hd,act_append,act_cons]
      rw [prefix_snoc f hcomm (N+1)]
      have hp : prefixSchedule (N+1)=List.range N++prefixSchedule N := by
        simp [prefixSchedule,List.range_succ,List.reverse_append,List.flatMap_append]
      rw [hp,act_append]
      have hc (y : α) : act f (List.range N) (act f (List.range N).reverse y)=y := by
        simpa only [List.reverse_reverse] using act_reverse_cancel f hinv (List.range N).reverse y
      rw [hc,ih,List.range_succ,List.reverse_append]
      simp only [List.reverse_cons,List.reverse_nil,List.nil_append,act_append,act_cons,act_nil]
      rw [commute_act f hcomm N (dominoPairSchedule N) (fun j hj => pair_bound hj),
        commute_act f hcomm N (dominoConjugatorSchedule N) (fun j hj => conjugator_bound hj)]

end InvolutionWord
end Kreweras
```

### `KrewerasConjugation.lean`

```lean
import KrewerasWordAlgebra

namespace Kreweras

theorem extensionTau_distant {n i j : ℕ} (h : i+1<j ∨ j+1<i) :
    Function.Commute (@extensionTau n i) (extensionTau j) := by
  intro e
  exact congrArg fromLinear (sourceTau_distant h (asLinear e))

theorem tau_distant {n i j : ℕ} (h : i+1<j ∨ j+1<i) :
    Function.Commute (@tau n i) (tau j) := by
  intro w
  apply (wordExtensionEquiv n).injective
  simp only [tau_bridge]
  exact extensionTau_distant h _

theorem domino_conjugation : DominoConjugationGoal := by
  intro n w
  exact InvolutionWord.conjugation (@tau n) tau_involutive
    (fun _ _ h => tau_distant h) (3*n) w

theorem source_domino_conjugation {α : Type} {R : α → α → Prop} {N : ℕ}
    (e : LinearExtension R N) :
    sourceEvac (sourceRun (dominoConjugatorSchedule N) e)=
      sourceRun (dominoConjugatorSchedule N) (sourceRun (dominoPairSchedule N) e) :=
  InvolutionWord.conjugation (@sourceTau α R N) sourceTau_involutive
    (fun _ _ h => sourceTau_distant h) N e

theorem conjugate_fixed_iff {n : ℕ} (w : K n) :
    evac (run (dominoConjugatorSchedule (3*n)) w)=
      run (dominoConjugatorSchedule (3*n)) w ↔
        run (dominoPairSchedule (3*n)) w=w := by
  rw [domino_conjugation]
  exact (run_bijective _).injective.eq_iff

noncomputable def pairFixedEvacEquiv (n : ℕ) :
    {w : K n // run (dominoPairSchedule (3*n)) w=w} ≃ {w : K n // evac w=w} where
  toFun w := ⟨run (dominoConjugatorSchedule (3*n)) w.val,(conjugate_fixed_iff _).mpr w.property⟩
  invFun w := by
    let e : K n ≃ K n := Equiv.ofBijective (run (dominoConjugatorSchedule (3*n))) (run_bijective _)
    refine ⟨e.symm w.val,?_⟩
    apply (conjugate_fixed_iff _).mp
    change evac (e (e.symm w.val))=e (e.symm w.val)
    rw [e.apply_symm_apply]
    exact w.property
  left_inv w := by
    apply Subtype.ext
    exact (Equiv.ofBijective _ (run_bijective _)).symm_apply_apply w.val
  right_inv w := by
    apply Subtype.ext
    exact (Equiv.ofBijective _ (run_bijective _)).apply_symm_apply w.val

#print axioms domino_conjugation
#print axioms source_domino_conjugation
#print axioms pairFixedEvacEquiv
end Kreweras
```

### `KrewerasPairFixed.lean`

```lean
import KrewerasConjugation

namespace Kreweras
set_option linter.unusedSimpArgs false

theorem sourceTau_fixed_of_endpoint {α : Type} {R : α → α → Prop} {N i : ℕ}
    (hi : i+1<N) (e : LinearExtension R N)
    (h : (sourceTau i e).order.symm ⟨i,by omega⟩=e.order.symm ⟨i,by omega⟩) :
    sourceTau i e=e := by
  classical
  by_cases hv : OrderValid R (e.order.trans (adjacent N i))
  · exfalso
    have hh : (e.order.trans (adjacent N i)).symm ⟨i,by omega⟩=e.order.symm ⟨i,by omega⟩ := by
      simpa only [sourceTau,dite_eq_left hv] using h
    change e.order.symm ((adjacent N i).symm ⟨i,by omega⟩)=_ at hh
    rw [adjacent_symm] at hh
    have he : e.order.symm ⟨i+1,hi⟩=e.order.symm ⟨i,by omega⟩ := by
      simpa only [adjacent,dite_eq_left hi,Equiv.swap_apply_left] using hh
    have hh' := congrArg Fin.val (e.order.symm.injective he)
    dsimp at hh'
    omega
  · simp only [sourceTau,dite_eq_right hv]

theorem sourceTau_fixed_iff {α : Type} {R : α → α → Prop} {N i : ℕ}
    (hi : i+1<N) (e : LinearExtension R N) :
    sourceTau i e=e ↔ R (e.order.symm ⟨i,by omega⟩) (e.order.symm ⟨i+1,hi⟩) := by
  classical
  have hback : ¬R (e.order.symm ⟨i+1,hi⟩) (e.order.symm ⟨i,by omega⟩) := by
    intro h
    have hh := e.mono _ _ h
    simp only [Equiv.apply_symm_apply,Fin.le_def] at hh
    omega
  have hs := swap_orderValid_iff e hi
  by_cases hr : R (e.order.symm ⟨i,by omega⟩) (e.order.symm ⟨i+1,hi⟩)
  · have hv : ¬OrderValid R (e.order.trans (adjacent N i)) := by
      intro h; exact (hs.mp h).1 hr
    simp only [sourceTau,dite_eq_right hv,hr,true_iff]
  · have hv := hs.mpr ⟨hr,hback⟩
    constructor
    · intro he
      have hp := congrArg (fun f : LinearExtension R N => f.order.symm ⟨i,by omega⟩) he
      have he' := sourceTau_fixed_of_endpoint hi e hp
      have hh : (adjacent N i) ⟨i,by omega⟩=⟨i,by omega⟩ := by
        have ho := congrArg LinearExtension.order he'
        simp only [sourceTau,dite_eq_left hv] at ho
        simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using
          congrArg (fun g : α ≃ Fin N => g (e.order.symm ⟨i,by omega⟩)) ho
      simp only [adjacent,dite_eq_left hi,Equiv.swap_apply_left,Fin.ext_iff] at hh
      omega
    · exact False.elim ∘ hr

theorem sourceRun_endpoint {α : Type} {R : α → α → Prop} {N : ℕ}
    (s : List ℕ) (i : ℕ) (hi : i<N) (hfar : ∀j∈s, j+1<i)
    (e : LinearExtension R N) :
    (sourceRun s e).order.symm ⟨i,hi⟩=e.order.symm ⟨i,hi⟩ := by
  induction s generalizing e with
  | nil => rfl
  | cons j s ih =>
    change (sourceRun s (sourceTau j e)).order.symm ⟨i,hi⟩=_
    rw [ih (fun k hk => hfar k (by simp [hk]))]
    exact sourceTau_symm_far e _ (by have := hfar j (by simp); dsimp; omega)
      (by have := hfar j (by simp); dsimp; omega)

theorem sourceRun_pair_fixed_iff {α : Type} {R : α → α → Prop} {N : ℕ}
    (s : List ℕ) (hbound : ∀i∈s, i+1<N)
    (hsep : s.Pairwise (fun i j => j+1<i)) (e : LinearExtension R N) :
    sourceRun s e=e ↔ ∀i∈s, sourceTau i e=e := by
  induction s generalizing e with
  | nil => simp [sourceRun]
  | cons i s ih =>
    have ht := List.pairwise_cons.mp hsep
    have hb := hbound i (by simp)
    have hb' : ∀j∈s, j+1<N := fun j hj => hbound j (by simp [hj])
    constructor
    · intro h
      have hp : (sourceTau i e).order.symm ⟨i,by omega⟩=e.order.symm ⟨i,by omega⟩ := by
        rw [← sourceRun_endpoint s i (by omega) ht.1 (sourceTau i e)]
        exact congrArg (fun f : LinearExtension R N => f.order.symm ⟨i,by omega⟩) h
      have he := sourceTau_fixed_of_endpoint hb e hp
      have hr : sourceRun s e=e := by
        change sourceRun s (sourceTau i e)=e at h
        rwa [he] at h
      simpa only [List.mem_cons,forall_eq_or_imp] using And.intro he ((ih hb' ht.2 e).mp hr)
    · intro h
      change sourceRun s (sourceTau i e)=e
      rw [h i (by simp)]
      exact (ih hb' ht.2 e).mpr (fun j hj => h j (by simp [hj]))

theorem pairSchedule_separated (N : ℕ) :
    (dominoPairSchedule N).Pairwise (fun i j => j+1<i) := by
  induction N using Nat.twoStepInduction with
  | zero => exact List.Pairwise.nil
  | one => exact List.Pairwise.nil
  | more N ih _ =>
    rw [InvolutionWord.pair_two,List.pairwise_cons]
    exact ⟨fun j hj => InvolutionWord.pair_bound hj,ih⟩

def PairedExtension {α : Type} {R : α → α → Prop} {N : ℕ}
    (e : LinearExtension R N) : Prop :=
  ∀ i, ∀ h : i∈dominoPairSchedule N,
    R (e.order.symm ⟨i,by have := InvolutionWord.pair_bound h; omega⟩)
      (e.order.symm ⟨i+1,InvolutionWord.pair_bound h⟩)

theorem source_pair_fixed_iff {α : Type} {R : α → α → Prop} {N : ℕ}
    (e : LinearExtension R N) :
    sourceRun (dominoPairSchedule N) e=e ↔ PairedExtension e := by
  rw [sourceRun_pair_fixed_iff _ (fun _ h => InvolutionWord.pair_bound h) (pairSchedule_separated N)]
  exact forall_congr' fun i => forall_congr' fun hi =>
    sourceTau_fixed_iff (InvolutionWord.pair_bound hi) e

theorem run_label_asLinear {n : ℕ} (s : List ℕ) (w : K n) :
    asLinear (label (run s w))=sourceRun s (asLinear (label w)) := by
  change asLinear (wordExtensionEquiv n (run s w))=_
  rw [run_bridge,extensionRun_asLinear]
  rfl

theorem word_pair_fixed_iff {n : ℕ} (w : K n) :
    run (dominoPairSchedule (3*n)) w=w ↔ PairedExtension (asLinear (label w)) := by
  rw [← source_pair_fixed_iff,← run_label_asLinear]
  constructor
  · intro h; rw [h]
  · intro h
    apply (wordExtensionEquiv n).injective
    apply Extension.ext
    exact congrArg LinearExtension.order h

noncomputable def evacPairedEquiv (n : ℕ) :
    {w : K n // evac w=w} ≃ {w : K n // PairedExtension (asLinear (label w))} :=
  (pairFixedEvacEquiv n).symm.trans (Equiv.subtypeEquivRight word_pair_fixed_iff)

#print axioms word_pair_fixed_iff
#print axioms evacPairedEquiv

#print axioms source_pair_fixed_iff
end Kreweras
```

### `KrewerasDominoStep.lean`

```lean
import KrewerasChains

namespace Kreweras
set_option linter.unusedSimpArgs false

def ComparableAddition (n : ℕ) (s t : IdealState) : Prop :=
  stateIdeal n s ⊂ stateIdeal n t ∧
    ∃ p q : Element n, p≠q ∧ posetLE p q ∧ stateIdeal n t \ stateIdeal n s={p,q}

theorem stateIdeal_fiber (n : ℕ) (s : IdealState) (hs : s.a≤n) (c : Fin 3) :
    ((stateIdeal n s).filter fun p => p.1=c).card=s.coord c := by
  rw [fiber_card,chainSet_stateIdeal,Fin.card_filter_val_lt]
  exact min_eq_right ((coord_le_a s c).trans hs)

theorem pair_fiber_card {n : ℕ} (S : Finset (Element n)) (p q : Element n)
    (hp : p∉S) (hq : q∉S) (hne : p≠q) (c : Fin 3) :
    ((insert p (insert q S)).filter fun r => r.1=c).card=
      (S.filter fun r => r.1=c).card+(if p.1=c then 1 else 0)+(if q.1=c then 1 else 0) := by
  by_cases hpc : p.1=c <;> by_cases hqc : q.1=c <;>
    simp [Finset.filter_insert,hpc,hqc,Finset.card_insert_of_notMem,hp,hq,hne,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem addition_coordinates {n : ℕ} {s t : IdealState} (hs : s.a≤n) (ht : t.a≤n)
    {p q : Element n} (hne : p≠q) (hsub : stateIdeal n s ⊆ stateIdeal n t)
    (hdiff : stateIdeal n t \ stateIdeal n s={p,q}) (c : Fin 3) :
    t.coord c=s.coord c+(if p.1=c then 1 else 0)+(if q.1=c then 1 else 0) := by
  have hp : p∈stateIdeal n t ∧ p∉stateIdeal n s := by
    apply Finset.mem_sdiff.mp
    rw [hdiff]
    simp
  have hq : q∈stateIdeal n t ∧ q∉stateIdeal n s := by
    apply Finset.mem_sdiff.mp
    rw [hdiff]
    simp
  have he : stateIdeal n t=insert p (insert q (stateIdeal n s)) := by
    ext r
    constructor
    · intro hr
      by_cases hr' : r∈stateIdeal n s
      · simp [hr']
      · have hh : r∈stateIdeal n t \ stateIdeal n s := Finset.mem_sdiff.mpr ⟨hr,hr'⟩
        rw [hdiff] at hh
        rcases Finset.mem_insert.mp hh with hrp|hrq
        · exact Finset.mem_insert.mpr (Or.inl hrp)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hrq))))
    · intro hr
      rcases Finset.mem_insert.mp hr with rfl|hr
      · exact hp.1
      · rcases Finset.mem_insert.mp hr with rfl|hr
        · exact hq.1
        · exact hsub hr
  rw [← stateIdeal_fiber n t ht c,he,pair_fiber_card _ _ _ hp.2 hq.2 hne,
    stateIdeal_fiber n s hs c]

@[simp] theorem mem_stateIdeal {n : ℕ} (s : IdealState) (p : Element n) :
    p∈stateIdeal n s ↔ p.2.val<s.coord p.1 := by simp [stateIdeal]

theorem comparable_addition_domino {n : ℕ} {s t : IdealState}
    (hs : s.a≤n) (ht : t.a≤n) (h : ComparableAddition n s t) : DominoStep s t := by
  obtain ⟨hsub,p,q,hne,hpq,hdiff⟩ := h
  have hc := addition_coordinates hs ht hne (Finset.ssubset_iff_subset_ne.mp hsub).1 hdiff
  have ha := hc 0
  have hb := hc 1
  have hcc := hc 2
  have hp : p∈stateIdeal n t ∧ p∉stateIdeal n s := by
    apply Finset.mem_sdiff.mp
    rw [hdiff]; simp
  have hq : q∈stateIdeal n t ∧ q∉stateIdeal n s := by
    apply Finset.mem_sdiff.mp
    rw [hdiff]; simp
  simp only [mem_stateIdeal] at hp hq
  have hi : p.2.val≤q.2.val := hpq.2
  have sp := s.b_le_a
  have sc := s.c_le_a
  have ht1 := p.1.isLt
  have ht2 := q.1.isLt
  rcases (show p.1=0 ∨ p.1=1 ∨ p.1=2 by omega) with hp0|hp0|hp0 <;>
    rcases (show q.1=0 ∨ q.1=1 ∨ q.1=2 by omega) with hq0|hq0|hq0
  all_goals simp [IdealState.coord,hp0,hq0,posetLE] at ha hb hcc hp hq hpq
  all_goals unfold DominoStep
  all_goals omega

/-- A uniform membership proof supplies all five explicit comparable pairs. -/
theorem stateIdeal_difference_pair {n : ℕ} (s t : IdealState) (p q : Element n)
    (h : ∀ r : Element n, s.coord r.1≤t.coord r.1 ∧
      (s.coord r.1≤r.2.val ∧ r.2.val<t.coord r.1 ↔ r=p ∨ r=q)) :
    stateIdeal n s ⊆ stateIdeal n t ∧ stateIdeal n t \ stateIdeal n s={p,q} := by
  constructor
  · intro r hr
    rw [mem_stateIdeal] at hr ⊢
    exact lt_of_lt_of_le hr (h r).1
  · ext r
    simp only [Finset.mem_sdiff,mem_stateIdeal,Finset.mem_insert,Finset.mem_singleton]
    rw [and_comm]
    simp only [not_lt]
    exact (h r).2

theorem comparableAddition_of_pair {n : ℕ} (s t : IdealState) (p q : Element n)
    (hne : p≠q) (hpq : posetLE p q)
    (h : ∀ r : Element n, s.coord r.1≤t.coord r.1 ∧
      (s.coord r.1≤r.2.val ∧ r.2.val<t.coord r.1 ↔ r=p ∨ r=q)) :
    ComparableAddition n s t := by
  obtain ⟨hsub,hdiff⟩ := stateIdeal_difference_pair s t p q h
  refine ⟨Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩,p,q,hne,hpq,hdiff⟩
  intro he
  have hp : p∈stateIdeal n t \ stateIdeal n s := by rw [hdiff]; simp
  rw [← he] at hp
  simp at hp

theorem domino_comparable_addition {n : ℕ} {s t : IdealState}
    (ht : t.a≤n) (h : DominoStep s t) : ComparableAddition n s t := by
  have hb := t.b_le_a
  have hc := t.c_le_a
  rcases h with ⟨ha,hb',hc'⟩|⟨ha,hb',hc'⟩|⟨ha,hb',hc'⟩|
    ⟨he,ha,hb',hc'⟩|⟨he,ha,hb',hc'⟩
  · let p : Element n := (0,⟨s.a,by omega⟩)
    let q : Element n := (0,⟨s.a+1,by omega⟩)
    apply comparableAddition_of_pair s t p q
    · simp [p,q,Prod.ext_iff,Fin.ext_iff]
    · simp only [p,q,posetLE,Fin.le_def]
      exact ⟨by decide,by omega⟩
    · intro r
      have hr := r.1.isLt
      rcases (show r.1=0 ∨ r.1=1 ∨ r.1=2 by omega) with hr0|hr0|hr0
      all_goals simp only [IdealState.coord,hr0,ha,hb',hc',p,q,Prod.ext_iff,Fin.ext_iff]
      all_goals simp <;> omega
  · let p : Element n := (1,⟨s.b,by omega⟩)
    let q : Element n := (1,⟨s.b+1,by omega⟩)
    apply comparableAddition_of_pair s t p q
    · simp [p,q,Prod.ext_iff,Fin.ext_iff]
    · simp only [p,q,posetLE,Fin.le_def]
      exact ⟨by decide,by omega⟩
    · intro r
      have hr := r.1.isLt
      rcases (show r.1=0 ∨ r.1=1 ∨ r.1=2 by omega) with hr0|hr0|hr0
      all_goals simp only [IdealState.coord,hr0,ha,hb',hc',p,q,Prod.ext_iff,Fin.ext_iff]
      all_goals simp <;> omega
  · let p : Element n := (2,⟨s.c,by omega⟩)
    let q : Element n := (2,⟨s.c+1,by omega⟩)
    apply comparableAddition_of_pair s t p q
    · simp [p,q,Prod.ext_iff,Fin.ext_iff]
    · simp only [p,q,posetLE,Fin.le_def]
      exact ⟨by decide,by omega⟩
    · intro r
      have hr := r.1.isLt
      rcases (show r.1=0 ∨ r.1=1 ∨ r.1=2 by omega) with hr0|hr0|hr0
      all_goals simp only [IdealState.coord,hr0,ha,hb',hc',p,q,Prod.ext_iff,Fin.ext_iff]
      all_goals simp <;> omega
  · let p : Element n := (0,⟨s.a,by omega⟩)
    let q : Element n := (1,⟨s.b,by omega⟩)
    apply comparableAddition_of_pair s t p q
    · simp [p,q,Prod.ext_iff,Fin.ext_iff]
    · simp only [p,q,posetLE,Fin.le_def]
      exact ⟨by decide,by omega⟩
    · intro r
      have hr := r.1.isLt
      rcases (show r.1=0 ∨ r.1=1 ∨ r.1=2 by omega) with hr0|hr0|hr0
      all_goals simp only [IdealState.coord,hr0,ha,hb',hc',p,q,Prod.ext_iff,Fin.ext_iff]
      all_goals simp <;> omega
  · let p : Element n := (0,⟨s.a,by omega⟩)
    let q : Element n := (2,⟨s.c,by omega⟩)
    apply comparableAddition_of_pair s t p q
    · simp [p,q,Prod.ext_iff,Fin.ext_iff]
    · simp only [p,q,posetLE,Fin.le_def]
      exact ⟨by decide,by omega⟩
    · intro r
      have hr := r.1.isLt
      rcases (show r.1=0 ∨ r.1=1 ∨ r.1=2 by omega) with hr0|hr0|hr0
      all_goals simp only [IdealState.coord,hr0,ha,hb',hc',p,q,Prod.ext_iff,Fin.ext_iff]
      all_goals simp <;> omega

theorem domino_step_iff (n : ℕ) (s t : IdealState) (hs : s.a≤n) (ht : t.a≤n) :
    ComparableAddition n s t ↔ DominoStep s t :=
  ⟨comparable_addition_domino hs ht,domino_comparable_addition ht⟩

theorem uncapped_step_counterexample :
    ComparableAddition 2 ⟨3,0,0,by omega,by omega⟩ ⟨2,2,0,by omega,by omega⟩ ∧
      ¬DominoStep ⟨3,0,0,by omega,by omega⟩ ⟨2,2,0,by omega,by omega⟩ := by
  unfold ComparableAddition DominoStep
  decide

#print axioms domino_step_iff
#print axioms uncapped_step_counterexample

#print axioms comparable_addition_domino
end Kreweras
```

### `KrewerasPrefixDomino.lean`

```lean
import KrewerasDominoStep
import KrewerasPairFixed
import KrewerasParity

namespace Kreweras
set_option linter.unusedSimpArgs false

theorem prefixIdeal_pair_difference {n i : ℕ} (e : Extension n) (hi : i+1<3*n) :
    (prefixIdeal e (i+2)).val \ (prefixIdeal e i).val=
      {e.order.symm ⟨i,by omega⟩,e.order.symm ⟨i+1,hi⟩} := by
  ext r
  simp only [prefixIdeal,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro h
    have hr : (e.order r).val=i ∨ (e.order r).val=i+1 := by omega
    rcases hr with hr|hr
    · left; exact e.order.injective (by simpa using Fin.ext hr)
    · right; exact e.order.injective (by simpa using Fin.ext hr)
  · rintro (rfl|rfl) <;> simp only [Equiv.apply_symm_apply] <;> omega

theorem prefixIdeal_pair_addition {n i : ℕ} (e : Extension n) (hi : i+1<3*n)
    (hr : posetLE (e.order.symm ⟨i,by omega⟩) (e.order.symm ⟨i+1,hi⟩)) :
    ComparableAddition n (idealState (prefixIdeal e i)) (idealState (prefixIdeal e (i+2))) := by
  have hsub := prefixIdeal_mono e (show i≤i+2 by omega)
  have hproper : (prefixIdeal e i).val ⊂ (prefixIdeal e (i+2)).val := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩
    intro he
    have hh := congrArg Finset.card he
    rw [prefixIdeal_card e i (by omega),prefixIdeal_card e (i+2) (by omega)] at hh
    omega
  unfold ComparableAddition
  rw [stateIdeal_idealState,stateIdeal_idealState]
  refine ⟨hproper,_,_,?_,hr,prefixIdeal_pair_difference e hi⟩
  intro he
  have hh := congrArg Fin.val (e.order.symm.injective he)
  dsimp at hh
  omega

theorem paired_prefix_domino {n : ℕ} (e : Extension n) (h : PairedExtension (asLinear e))
    (i : ℕ) (hi : i∈dominoPairSchedule (3*n)) :
    DominoStep (idealState (prefixIdeal e i)) (idealState (prefixIdeal e (i+2))) :=
  comparable_addition_domino (idealState_cap _) (idealState_cap _)
    (prefixIdeal_pair_addition e (InvolutionWord.pair_bound hi) (h i hi))

theorem prefixIdeal_terminal {n : ℕ} (e : Extension n) :
    idealState (prefixIdeal e (3*n))=⟨n,n,n,le_rfl,le_rfl⟩ := by
  apply IdealState.ext
  all_goals
    first
    | change (idealState (prefixIdeal e (3*n))).coord 0=n
    | change (idealState (prefixIdeal e (3*n))).coord 1=n
    | change (idealState (prefixIdeal e (3*n))).coord 2=n
  all_goals rw [prefixIdeal_coordinates]; exact (erase_valid e).1 _

theorem prefixIdeal_first {n : ℕ} (hn : 0<n) (e : Extension n) :
    idealState (prefixIdeal e 1)=⟨1,0,0,by omega,by omega⟩ := by
  have hp : e.order.symm ⟨0,by omega⟩=(0,⟨0,hn⟩) := by
    apply (source_minimal_element n hn _).mp
    intro q hq
    have hh := e.mono _ _ hq
    simp only [Equiv.apply_symm_apply,Fin.le_def] at hh
    apply e.order.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    change (e.order q).val=0
    omega
  have he : (prefixIdeal e 1).val={(0,⟨0,hn⟩)} := by
    ext p
    simp only [prefixIdeal,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro h
      rw [← hp]
      apply e.order.injective
      simp only [Equiv.apply_symm_apply]
      apply Fin.ext
      change (e.order p).val=0
      omega
    · rintro rfl
      rw [← hp,Equiv.apply_symm_apply]
      simp
  apply IdealState.ext <;> simp [idealState,he,chainSet,Finset.filter_eq']

theorem pairSchedule_odd_member {N k : ℕ} (ho : N%2=1) (hk : 2*k+2<N) :
    2*k+1∈dominoPairSchedule N := by
  unfold dominoPairSchedule
  apply List.mem_map.mpr
  refine ⟨N/2-1-k,List.mem_range.mpr (by omega),?_⟩
  omega

theorem paired_odd_impossible (n : ℕ) (hn : n%2=1) (e : Extension n)
    (h : PairedExtension (asLinear e)) : False := by
  have hn' : 0<n := by omega
  have ho : (3*n)%2=1 := by omega
  have hs (k : ℕ) (hk : 2*k+1≤3*n) :
      SingletonSector (idealState (prefixIdeal e (2*k+1))) := by
    induction k with
    | zero => rw [show 2*0+1=1 by omega,prefixIdeal_first hn' e]; exact ⟨rfl,rfl,rfl⟩
    | succ k ih =>
      have hprev := ih (by omega)
      have hi := pairSchedule_odd_member ho (show 2*k+2<3*n by omega)
      have hd := paired_prefix_domino e h (2*k+1) hi
      convert singleton_sector_closed hprev hd using 1
  have ht : 2*((3*n)/2)+1=3*n := by omega
  have hh := hs ((3*n)/2) (by omega)
  rw [ht,prefixIdeal_terminal] at hh
  exact singleton_no_odd_diagonal hh rfl

theorem odd_evac_zero (m : ℕ) : Fintype.card {w : K (2*m+1) // evac w=w}=0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨?_⟩
  intro w
  let v := evacPairedEquiv (2*m+1) w
  exact paired_odd_impossible (2*m+1) (by omega) (label v.val) v.property

#print axioms paired_prefix_domino
#print axioms prefixIdeal_first
#print axioms odd_evac_zero
end Kreweras
```

### `KrewerasIdealFlags.lean`

```lean
import KrewerasPrefixDomino

namespace Kreweras
set_option linter.unusedSimpArgs false

/-- A saturated chain of actual finite ideals, with no extension in its data. -/
structure IdealFlag (n : ℕ) where
  ideals : Fin (3*n+1) → FiniteIdeal n
  size : ∀ k, (ideals k).val.card=k.val
  mono : ∀ i j, i≤j → (ideals i).val ⊆ (ideals j).val

@[ext] theorem IdealFlag.ext {n : ℕ} {c d : IdealFlag n} (h : c.ideals=d.ideals) : c=d := by
  cases c; cases d; cases h; rfl

def extensionFlag {n : ℕ} (e : Extension n) : IdealFlag n where
  ideals k := prefixIdeal e k.val
  size k := prefixIdeal_card e k.val (by omega)
  mono _ _ h := prefixIdeal_mono e h

theorem flag_step_exists {n : ℕ} (c : IdealFlag n) (i : Fin (3*n)) :
    ∃ p : Element n, (c.ideals i.succ).val \ (c.ideals i.castSucc).val={p} := by
  apply Finset.card_eq_one.mp
  rw [Finset.card_sdiff_of_subset (c.mono _ _ (by change i.val≤i.val+1; omega)),c.size,c.size]
  change i.val+1-i.val=1
  omega

noncomputable def flagElement {n : ℕ} (c : IdealFlag n) (i : Fin (3*n)) : Element n :=
  Classical.choose (flag_step_exists c i)

theorem flagElement_diff {n : ℕ} (c : IdealFlag n) (i : Fin (3*n)) :
    (c.ideals i.succ).val \ (c.ideals i.castSucc).val={flagElement c i} :=
  Classical.choose_spec (flag_step_exists c i)

theorem flagElement_mem {n : ℕ} (c : IdealFlag n) (i : Fin (3*n)) :
    flagElement c i∈(c.ideals i.succ).val ∧ flagElement c i∉(c.ideals i.castSucc).val := by
  apply Finset.mem_sdiff.mp
  rw [flagElement_diff]
  simp

theorem flagElement_injective {n : ℕ} (c : IdealFlag n) : Function.Injective (flagElement c) := by
  suffices hh : ∀ i j : Fin (3*n), i<j → flagElement c i≠flagElement c j by
    intro i j h
    rcases lt_trichotomy i j with hij|hij|hij
    · exact False.elim (hh i j hij h)
    · exact hij
    · exact False.elim (hh j i hij h.symm)
  intro i j hij he
  have hm := c.mono i.succ j.castSucc (by change i.val+1≤j.val; exact hij)
    (flagElement_mem c i).1
  rw [he] at hm
  exact (flagElement_mem c j).2 hm

noncomputable def flagOrder {n : ℕ} (c : IdealFlag n) : Fin (3*n) ≃ Element n :=
  Equiv.ofBijective (flagElement c) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨flagElement_injective c,by simp [Element]⟩)

theorem flagElement_prefix_iff {n : ℕ} (c : IdealFlag n) (i : Fin (3*n))
    (k : Fin (3*n+1)) : flagElement c i∈(c.ideals k).val ↔ i.val<k.val := by
  constructor
  · intro hm
    by_contra h
    exact (flagElement_mem c i).2 (c.mono k i.castSucc (by change k.val≤i.val; omega) hm)
  · intro h
    exact c.mono i.succ k (by change i.val+1≤k.val; omega) (flagElement_mem c i).1

noncomputable def flagExtension {n : ℕ} (c : IdealFlag n) : Extension n where
  order := (flagOrder c).symm
  mono p q hpq := by
    by_contra h
    let i := (flagOrder c).symm p
    let j := (flagOrder c).symm q
    have hij : j<i := lt_of_not_ge h
    have hq : flagElement c j∈(c.ideals i.castSucc).val :=
      (flagElement_prefix_iff c j i.castSucc).mpr hij
    have hp : flagElement c i∈(c.ideals i.castSucc).val := by
      apply (c.ideals i.castSucc).property (flagElement c j) hq (flagElement c i)
      simpa only [← show (flagOrder c : Fin (3*n) → Element n)=flagElement c from rfl,
        i,j,Equiv.apply_symm_apply] using hpq
    exact (flagElement_mem c i).2 hp

theorem flagExtension_prefix {n : ℕ} (c : IdealFlag n) (k : Fin (3*n+1)) :
    prefixIdeal (flagExtension c) k.val=c.ideals k := by
  apply Subtype.ext
  ext p
  obtain ⟨i,rfl⟩ := (flagOrder c).surjective p
  simp only [prefixIdeal,Finset.mem_filter,Finset.mem_univ,true_and]
  change ((flagOrder c).symm ((flagOrder c) i)).val<k.val ↔ _
  rw [Equiv.symm_apply_apply]
  exact (flagElement_prefix_iff c i k).symm

theorem extensionFlag_bijective (n : ℕ) : Function.Bijective (@extensionFlag n) := by
  constructor
  · intro e f h
    apply Extension.ext
    apply Equiv.ext
    intro p
    symm
    apply le_antisymm
    · have hm : p∈(prefixIdeal f ((e.order p).val+1)).val := by
        have hh := congrArg (fun c : IdealFlag n => (c.ideals ⟨(e.order p).val+1,by omega⟩).val) h
        change (prefixIdeal e ((e.order p).val+1)).val=(prefixIdeal f ((e.order p).val+1)).val at hh
        rw [← hh]
        simp [prefixIdeal]
      have hh := (Finset.mem_filter.mp hm).2
      change (e.order p).val+1>(f.order p).val at hh
      exact (show (f.order p).val≤(e.order p).val from by omega)
    · have hm : p∈(prefixIdeal e ((f.order p).val+1)).val := by
        have hh := congrArg (fun c : IdealFlag n => (c.ideals ⟨(f.order p).val+1,by omega⟩).val) h
        change (prefixIdeal e ((f.order p).val+1)).val=(prefixIdeal f ((f.order p).val+1)).val at hh
        rw [hh]
        simp [prefixIdeal]
      have hh := (Finset.mem_filter.mp hm).2
      exact (show (e.order p).val≤(f.order p).val from by omega)
  · intro c
    refine ⟨flagExtension c,?_⟩
    apply IdealFlag.ext
    funext k
    exact flagExtension_prefix c k

noncomputable def extensionIdealFlagEquiv (n : ℕ) : Extension n ≃ IdealFlag n :=
  Equiv.ofBijective extensionFlag (extensionFlag_bijective n)

#print axioms extensionIdealFlagEquiv
end Kreweras
```

### `KrewerasDominoBridge.lean`

```lean
import KrewerasIdealFlags

namespace Kreweras
set_option linter.unusedSimpArgs false

theorem prefix_domino_iff {n i : ℕ} (e : Extension n) (hi : i+1<3*n) :
    DominoStep (idealState (prefixIdeal e i)) (idealState (prefixIdeal e (i+2))) ↔
      posetLE (e.order.symm ⟨i,by omega⟩) (e.order.symm ⟨i+1,hi⟩) := by
  constructor
  · intro h
    obtain ⟨_,p,q,hne,hpq,hdiff⟩ := domino_comparable_addition (idealState_cap _) h
    rw [stateIdeal_idealState,stateIdeal_idealState,prefixIdeal_pair_difference e hi] at hdiff
    have hp : p=e.order.symm ⟨i,by omega⟩ ∨ p=e.order.symm ⟨i+1,hi⟩ := by
      have hh : p∈({p,q} : Finset (Element n)) := by simp
      rw [← hdiff] at hh
      simpa using hh
    have hq : q=e.order.symm ⟨i,by omega⟩ ∨ q=e.order.symm ⟨i+1,hi⟩ := by
      have hh : q∈({p,q} : Finset (Element n)) := by simp
      rw [← hdiff] at hh
      simpa using hh
    rcases hp with hp|hp <;> rcases hq with hq|hq
    · exact False.elim (hne (hp.trans hq.symm))
    · simpa only [hp,hq] using hpq
    · have hh := e.mono p q hpq
      rw [hp,hq,Equiv.apply_symm_apply,Equiv.apply_symm_apply] at hh
      have hh' : i+1≤i := hh
      omega
    · exact False.elim (hne (hp.trans hq.symm))
  · intro h
    exact comparable_addition_domino (idealState_cap _) (idealState_cap _)
      (prefixIdeal_pair_addition e hi h)

/-- An expanded domino chain: all rank-one intermediate ideals are retained.
At pair indices the two-rank difference is required to be a comparable domino.
The first unpaired rank is the initial singleton when 3*n is odd. -/
def FlagDomino {n : ℕ} (c : IdealFlag n) : Prop :=
  ∀ i, ∀ h : i∈dominoPairSchedule (3*n),
    DominoStep (idealState (c.ideals ⟨i,by have := InvolutionWord.pair_bound h; omega⟩))
      (idealState (c.ideals ⟨i+2,by have := InvolutionWord.pair_bound h; omega⟩))

abbrev SourceDominoChains (n : ℕ) := {c : IdealFlag n // FlagDomino c}

theorem extensionFlag_domino_iff {n : ℕ} (e : Extension n) :
    FlagDomino (extensionFlag e) ↔ PairedExtension (asLinear e) := by
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact prefix_domino_iff e (InvolutionWord.pair_bound hi)

noncomputable def pairedIdealEquiv (n : ℕ) :
    {w : K n // PairedExtension (asLinear (label w))} ≃ SourceDominoChains n :=
  (Equiv.subtypeEquiv (wordExtensionEquiv n) (fun _ => Iff.rfl)).trans
    (Equiv.subtypeEquiv (extensionIdealFlagEquiv n) (fun e => (extensionFlag_domino_iff e).symm))

noncomputable def evacDominoEquiv (n : ℕ) :
    {w : K n // evac w=w} ≃ SourceDominoChains n :=
  (evacPairedEquiv n).trans (pairedIdealEquiv n)

theorem initial_singleton (n : ℕ) (hn : 0<n) (c : SourceDominoChains n) :
    idealState (c.val.ideals ⟨1,by omega⟩)=⟨1,0,0,by omega,by omega⟩ := by
  rw [← flagExtension_prefix]
  exact prefixIdeal_first hn _

#print axioms prefix_domino_iff
#print axioms evacDominoEquiv
#print axioms initial_singleton
end Kreweras
```

### `KrewerasDominoPaths.lean`

```lean
import KrewerasWalks

namespace Kreweras
set_option linter.unusedSimpArgs false

abbrev AllDominoPaths (d : ℕ) := {p : Fin (d+1) → IdealState //
  p 0=zeroState ∧ ∀ i : Fin d, DominoStep (p i.castSucc) (p i.succ)}

theorem path_size {d : ℕ} (p : AllDominoPaths d) (i : Fin (d+1)) :
    (p.val i).a+(p.val i).b+(p.val i).c=2*i.val := by
  induction i using Fin.induction with
  | zero => rw [p.property.1]; rfl
  | succ i ih =>
    simp only [Fin.val_castSucc] at ih
    have h := domino_step_size (p.property.2 i)
    change (p.val i.succ).a+(p.val i.succ).b+(p.val i.succ).c=2*(i.val+1)
    omega

theorem path_reachable {d : ℕ} (p : AllDominoPaths d) (i : Fin (d+1)) : Reachable (p.val i) := by
  induction i using Fin.induction with
  | zero => rw [p.property.1]; exact Reachable.zero
  | succ i ih => exact Reachable.step ih (p.property.2 i)

theorem path_coord_bound {d : ℕ} (p : AllDominoPaths d) (i : Fin (d+1)) :
    (p.val i).a≤2*d ∧ (p.val i).b≤2*d ∧ (p.val i).c≤2*d := by
  have h := path_size p i
  have hi := i.isLt
  omega

def boundedPath {d : ℕ} (p : AllDominoPaths d) : Fin (d+1) → Fin (2*d+1) × Fin (2*d+1) × Fin (2*d+1) :=
  fun i => (⟨(p.val i).a,by have := path_coord_bound p i; omega⟩,
    ⟨(p.val i).b,by have := path_coord_bound p i; omega⟩,
    ⟨(p.val i).c,by have := path_coord_bound p i; omega⟩)

theorem boundedPath_injective (d : ℕ) : Function.Injective (@boundedPath d) := by
  intro p q h
  apply Subtype.ext
  funext i
  have hh := congrFun h i
  apply IdealState.ext
  · exact congrArg (fun r => r.1.val) hh
  · exact congrArg (fun r => r.2.1.val) hh
  · exact congrArg (fun r => r.2.2.val) hh

noncomputable instance (d : ℕ) : Fintype (AllDominoPaths d) :=
  Fintype.ofInjective boundedPath (boundedPath_injective d)

abbrev DominoPath (d : ℕ) (s : IdealState) := {p : AllDominoPaths d // p.val (Fin.last d)=s}
abbrev CappedDominoPath (n d : ℕ) (s : IdealState) :=
  {p : DominoPath d s // ∀ i, (p.val.val i).a≤n}

noncomputable instance (d : ℕ) (s : IdealState) : Fintype (DominoPath d s) := by
  classical
  unfold DominoPath
  infer_instance
noncomputable instance (n d : ℕ) (s : IdealState) : Fintype (CappedDominoPath n d s) := by
  classical
  unfold CappedDominoPath
  infer_instance

theorem path_mono_a {d : ℕ} (p : AllDominoPaths d) {i j : Fin (d+1)} (h : i≤j) :
    (p.val i).a≤(p.val j).a := by
  suffices hm : Monotone (fun k => (p.val k).a) from hm h
  exact Fin.monotone_iff_le_succ.mpr (fun i => (domino_step_mono (p.property.2 i)).1)

noncomputable def dominoCapEquiv (n d : ℕ) (s : IdealState) (hs : s.a≤n) :
    CappedDominoPath n d s ≃ DominoPath d s where
  toFun := Subtype.val
  invFun p := ⟨p,fun i => by
    have hm := path_mono_a p.val (show i≤Fin.last d from Fin.le_last i)
    rw [p.property] at hm
    exact hm.trans hs⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem domino_cap_irrelevant (n d : ℕ) (s : IdealState) (hs : s.a≤n) :
    Fintype.card (CappedDominoPath n d s)=Fintype.card (DominoPath d s) :=
  Fintype.card_congr (dominoCapEquiv n d s hs)

noncomputable def D (a b c : ℕ) : ℕ :=
  if h : b≤a ∧ c≤a then
    Fintype.card (DominoPath ((a+b+c)/2) ⟨a,b,c,h.1,h.2⟩) else 0

#print axioms domino_cap_irrelevant
#print axioms path_size
end Kreweras
```

### `KrewerasDominoSymmetry.lean`

```lean
import KrewerasDominoPaths

namespace Kreweras

def swapState (s : IdealState) : IdealState := ⟨s.a,s.c,s.b,s.c_le_a,s.b_le_a⟩

@[simp] theorem swapState_twice (s : IdealState) : swapState (swapState s)=s := rfl

theorem domino_swap {s t : IdealState} (h : DominoStep s t) :
    DominoStep (swapState s) (swapState t) := by
  rcases h with h|h|h|h|h
  · exact Or.inl ⟨h.1,h.2.2,h.2.1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨h.1,h.2.2,h.2.1⟩))
  · exact Or.inr (Or.inl ⟨h.1,h.2.2,h.2.1⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1,h.2.1,h.2.2.2,h.2.2.1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,h.2.1,h.2.2.2,h.2.2.1⟩)))

def swapDominoPath {d : ℕ} (p : AllDominoPaths d) : AllDominoPaths d :=
  ⟨fun i => swapState (p.val i),by
    constructor
    · change swapState (p.val 0)=zeroState
      rw [p.property.1]; rfl
    · intro i; exact domino_swap (p.property.2 i)⟩

@[simp] theorem swapDominoPath_twice {d : ℕ} (p : AllDominoPaths d) :
    swapDominoPath (swapDominoPath p)=p := by
  apply Subtype.ext
  rfl

def swapDominoEquiv (d : ℕ) (s : IdealState) : DominoPath d s ≃ DominoPath d (swapState s) where
  toFun p := ⟨swapDominoPath p.val,congrArg swapState p.property⟩
  invFun p := ⟨swapDominoPath p.val,by
    change swapState (p.val.val (Fin.last d))=s
    rw [p.property,swapState_twice]⟩
  left_inv p := by apply Subtype.ext; exact swapDominoPath_twice _
  right_inv p := by apply Subtype.ext; exact swapDominoPath_twice _

theorem D_swap (a b c : ℕ) : D a b c=D a c b := by
  unfold D
  by_cases hb : b≤a <;> by_cases hc : c≤a
  · rw [dite_eq_left ⟨hb,hc⟩,dite_eq_left ⟨hc,hb⟩]
    have ht : (a+b+c)/2=(a+c+b)/2 := by omega
    rw [← ht]
    exact Fintype.card_congr (swapDominoEquiv _ ⟨a,b,c,hb,hc⟩)
  all_goals simp only [hb,hc,and_false,false_and,dite_false]

theorem D_odd_zero (a b c : ℕ) (hodd : (a+b+c)%2=1) : D a b c=0 := by
  unfold D
  split
  · apply Fintype.card_eq_zero_iff.mpr
    refine ⟨?_⟩
    intro p
    have hh := path_size p.val (Fin.last ((a+b+c)/2))
    rw [p.property] at hh
    change a+b+c=2*((a+b+c)/2) at hh
    omega
  · rfl

#print axioms D_swap
#print axioms D_odd_zero
end Kreweras
```

### `KrewerasRefinement.lean`

```lean
import KrewerasDominoBridge
import KrewerasDominoPaths

namespace Kreweras

/-- A saturated step expressed in the classified ideal coordinates. -/
def UnitStep (s t : IdealState) : Prop :=
  s.a≤t.a ∧ s.b≤t.b ∧ s.c≤t.c ∧ t.a+t.b+t.c=s.a+s.b+s.c+1

theorem domino_middle_unique {s t u v : IdealState} (h : DominoStep s t)
    (hu : UnitStep s u ∧ UnitStep u t) (hv : UnitStep s v ∧ UnitStep v t) : u=v := by
  have su := u.b_le_a
  have cu := u.c_le_a
  have sv := v.b_le_a
  have cv := v.c_le_a
  rcases h with h|h|h|h|h
  all_goals
    apply IdealState.ext <;> unfold UnitStep at hu hv <;> omega

theorem domino_middle_exists {s t : IdealState} (h : DominoStep s t) :
    ∃ u, UnitStep s u ∧ UnitStep u t := by
  have sb := s.b_le_a
  have sc := s.c_le_a
  have tb := t.b_le_a
  have tc := t.c_le_a
  rcases h with h|h|h|h|h
  · refine ⟨⟨s.a+1,s.b,s.c,by omega,by omega⟩,?_⟩
    unfold UnitStep; dsimp; omega
  · refine ⟨⟨s.a,s.b+1,s.c,by omega,by omega⟩,?_⟩
    unfold UnitStep; dsimp; omega
  · refine ⟨⟨s.a,s.b,s.c+1,by omega,by omega⟩,?_⟩
    unfold UnitStep; dsimp; omega
  · refine ⟨⟨s.a+1,s.b,s.c,by omega,by omega⟩,?_⟩
    unfold UnitStep; dsimp; omega
  · refine ⟨⟨s.a+1,s.b,s.c,by omega,by omega⟩,?_⟩
    unfold UnitStep; dsimp; omega

noncomputable def dominoMiddle {s t : IdealState} (h : DominoStep s t) : IdealState :=
  Classical.choose (domino_middle_exists h)

theorem dominoMiddle_spec {s t : IdealState} (h : DominoStep s t) :
    UnitStep s (dominoMiddle h) ∧ UnitStep (dominoMiddle h) t :=
  Classical.choose_spec (domino_middle_exists h)

/-- No unproved extension data is hidden in this coordinate flag. -/
structure CoordinateFlag (n : ℕ) where
  states : Fin (3*n+1) → IdealState
  cap : ∀ i, (states i).a≤n
  size : ∀ i, (states i).a+(states i).b+(states i).c=i.val
  step : ∀ i : Fin (3*n), UnitStep (states i.castSucc) (states i.succ)

@[ext] theorem CoordinateFlag.ext {n : ℕ} {c d : CoordinateFlag n}
    (h : c.states=d.states) : c=d := by
  cases c; cases d; cases h; rfl

theorem coordinateFlag_mono {n : ℕ} (c : CoordinateFlag n) {i j : Fin (3*n+1)} (h : i≤j) :
    (c.states i).a≤(c.states j).a ∧ (c.states i).b≤(c.states j).b ∧
      (c.states i).c≤(c.states j).c := by
  have ha : Monotone (fun k => (c.states k).a) :=
    Fin.monotone_iff_le_succ.mpr (fun k => (c.step k).1)
  have hb : Monotone (fun k => (c.states k).b) :=
    Fin.monotone_iff_le_succ.mpr (fun k => (c.step k).2.1)
  have hc : Monotone (fun k => (c.states k).c) :=
    Fin.monotone_iff_le_succ.mpr (fun k => (c.step k).2.2.1)
  exact ⟨ha h,hb h,hc h⟩

theorem stateIdeal_mono {n : ℕ} {s t : IdealState}
    (h : s.a≤t.a ∧ s.b≤t.b ∧ s.c≤t.c) : stateIdeal n s ⊆ stateIdeal n t := by
  intro p hp
  have hh : s.coord p.1≤t.coord p.1 := by
    unfold IdealState.coord
    split_ifs <;> omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_lt_of_le (Finset.mem_filter.mp hp).2 hh⟩

def coordinateIdealFlag {n : ℕ} (c : CoordinateFlag n) : IdealFlag n where
  ideals i := ⟨stateIdeal n (c.states i),stateIdeal_down _ _⟩
  size i := (stateIdeal_card _ _ (c.cap i)).trans (c.size i)
  mono _ _ h := stateIdeal_mono (coordinateFlag_mono c h)

def idealCoordinateFlag {n : ℕ} (c : IdealFlag n) : CoordinateFlag n where
  states i := idealState (c.ideals i)
  cap _ := idealState_cap _
  size i := by rw [← stateIdeal_card _ _ (idealState_cap _),stateIdeal_idealState,c.size]
  step i := by
    have hm := c.mono i.castSucc i.succ (by change i.val≤i.val+1; omega)
    have hc (k : Fin 3) : (idealState (c.ideals i.castSucc)).coord k≤
        (idealState (c.ideals i.succ)).coord k := by
      simp only [idealState_coord]
      apply Finset.card_le_card
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm (Finset.mem_filter.mp hr).2⟩
    refine ⟨hc 0,hc 1,hc 2,?_⟩
    have hs (k : Fin (3*n+1)) :
        (idealState (c.ideals k)).a+(idealState (c.ideals k)).b+(idealState (c.ideals k)).c=k.val := by
      rw [← stateIdeal_card _ _ (idealState_cap _),stateIdeal_idealState,c.size]
    rw [hs,hs]; rfl

noncomputable def idealCoordinateEquiv (n : ℕ) : IdealFlag n ≃ CoordinateFlag n where
  toFun := idealCoordinateFlag
  invFun := coordinateIdealFlag
  left_inv c := by
    apply IdealFlag.ext
    funext i
    exact Subtype.ext (stateIdeal_idealState _)
  right_inv c := by
    apply CoordinateFlag.ext
    funext i
    exact idealState_stateIdeal _ _ (c.cap i)

#print axioms domino_middle_unique
#print axioms domino_middle_exists
#print axioms idealCoordinateEquiv
end Kreweras
```

### `KrewerasPathRefinement.lean`

```lean
import KrewerasRefinement

namespace Kreweras
set_option linter.unusedSimpArgs false

noncomputable def refineState {d : ℕ} (p : AllDominoPaths d) (k : Fin (2*d+1)) : IdealState :=
  if h : k.val%2=0 then p.val ⟨k.val/2,by omega⟩
  else dominoMiddle (p.property.2 ⟨k.val/2,by omega⟩)

@[simp] theorem refineState_even {d : ℕ} (p : AllDominoPaths d) (i : Fin (d+1)) :
    refineState p ⟨2*i.val,by omega⟩=p.val i := by
  simp only [refineState,Nat.mul_mod_right,dite_true]
  exact congrArg p.val (Fin.ext (by dsimp; omega))

@[simp] theorem refineState_odd {d : ℕ} (p : AllDominoPaths d) (i : Fin d) :
    refineState p ⟨2*i.val+1,by omega⟩=dominoMiddle (p.property.2 i) := by
  have he : (2*i.val+1)%2≠0 := by omega
  have hi : (⟨(2*i.val+1)/2,by omega⟩ : Fin d)=i := Fin.ext (by dsimp; omega)
  simp only [refineState,dite_eq_right he,hi]

theorem refineState_step {d : ℕ} (p : AllDominoPaths d) (k : Fin (2*d)) :
    UnitStep (refineState p k.castSucc) (refineState p k.succ) := by
  by_cases he : k.val%2=0
  · let i : Fin d := ⟨k.val/2,by omega⟩
    have h0 : k.castSucc=(⟨2*i.val,by have := i.isLt; omega⟩ : Fin (2*d+1)) := Fin.ext (by dsimp [i]; omega)
    have h1 : k.succ=(⟨2*i.val+1,by have := i.isLt; omega⟩ : Fin (2*d+1)) := Fin.ext (by dsimp [i]; omega)
    rw [h0,h1,refineState_odd]
    have hh := refineState_even p i.castSucc
    change refineState p ⟨2*i.val,by omega⟩=p.val i.castSucc at hh
    rw [hh]
    exact (dominoMiddle_spec _).1
  · let i : Fin d := ⟨k.val/2,by omega⟩
    have h0 : k.castSucc=(⟨2*i.val+1,by have := i.isLt; omega⟩ : Fin (2*d+1)) := Fin.ext (by dsimp [i]; omega)
    have h1 : k.succ=(⟨2*i.succ.val,by have := i.isLt; dsimp; omega⟩ : Fin (2*d+1)) := Fin.ext (by dsimp [i]; omega)
    rw [h0,h1,refineState_odd,refineState_even]
    exact (dominoMiddle_spec _).2

theorem refineState_size {d : ℕ} (p : AllDominoPaths d) (k : Fin (2*d+1)) :
    (refineState p k).a+(refineState p k).b+(refineState p k).c=k.val := by
  induction k using Fin.induction with
  | zero =>
    have h := refineState_even p (0 : Fin (d+1))
    change refineState p 0=p.val 0 at h
    rw [h,p.property.1]; rfl
  | succ k ih =>
    have h := (refineState_step p k).2.2.2
    change (refineState p k.succ).a+(refineState p k.succ).b+(refineState p k.succ).c=k.val+1
    simp only [Fin.val_castSucc] at ih
    omega

theorem refineState_cap {d : ℕ} {s : IdealState} (p : DominoPath d s)
    (k : Fin (2*d+1)) : (refineState p.val k).a≤s.a := by
  have hm : Monotone (fun i => (refineState p.val i).a) :=
    Fin.monotone_iff_le_succ.mpr (fun i => (refineState_step p.val i).1)
  have h := hm (Fin.le_last k)
  have he := refineState_even p.val (Fin.last d)
  change refineState p.val (Fin.last (2*d))=p.val.val (Fin.last d) at he
  dsimp only at h
  rwa [he,p.property] at h

/-- Pair membership, including its exact parity offset. -/
theorem pairSchedule_mem_iff (N i : ℕ) :
    i∈dominoPairSchedule N ↔ i+1<N ∧ i%2=N%2 := by
  constructor
  · intro h
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    have hj' := List.mem_range.mp hj
    exact ⟨by omega,by omega⟩
  · rintro ⟨hi,hp⟩
    apply List.mem_map.mpr
    refine ⟨(N-i)/2-1,List.mem_range.mpr (by omega),?_⟩
    omega

#print axioms refineState_step
#print axioms refineState_size
#print axioms pairSchedule_mem_iff
end Kreweras
```

### `KrewerasEvenCompression.lean`

```lean
import KrewerasPathRefinement

namespace Kreweras
set_option linter.unusedSimpArgs false

abbrev EvenCoordinateChains (m : ℕ) := {c : CoordinateFlag (2*m) //
  ∀ i : Fin (3*m), DominoStep (c.states ⟨2*i.val,by omega⟩)
    (c.states ⟨2*i.val+2,by omega⟩)}

theorem flag_even_coordinate_iff (m : ℕ) (c : IdealFlag (2*m)) :
    FlagDomino c ↔ ∀ i : Fin (3*m),
      DominoStep ((idealCoordinateFlag c).states ⟨2*i.val,by omega⟩)
        ((idealCoordinateFlag c).states ⟨2*i.val+2,by omega⟩) := by
  constructor
  · intro h i
    exact h (2*i.val) ((pairSchedule_mem_iff _ _).mpr ⟨by omega,by omega⟩)
  · intro h i hi
    have hh := (pairSchedule_mem_iff _ _).mp hi
    let j : Fin (3*m) := ⟨i/2,by omega⟩
    have he : 2*j.val=i := by dsimp [j]; omega
    simpa only [idealCoordinateFlag,he] using h j

noncomputable def sourceEvenCoordinateEquiv (m : ℕ) :
    SourceDominoChains (2*m) ≃ EvenCoordinateChains m :=
  Equiv.subtypeEquiv (idealCoordinateEquiv _) (flag_even_coordinate_iff m)

theorem coordinateFlag_zero {n : ℕ} (c : CoordinateFlag n) : c.states 0=zeroState := by
  have hs := c.size 0
  simp only [Fin.val_zero] at hs
  apply IdealState.ext <;> change _=0 <;> omega

theorem coordinateFlag_last {n : ℕ} (c : CoordinateFlag n) :
    c.states (Fin.last (3*n))=⟨n,n,n,le_rfl,le_rfl⟩ := by
  have hs := c.size (Fin.last (3*n))
  have ha := c.cap (Fin.last (3*n))
  have hb := (c.states (Fin.last (3*n))).b_le_a
  have hc := (c.states (Fin.last (3*n))).c_le_a
  apply IdealState.ext <;> dsimp at * <;> omega

def compressEven {m : ℕ} (c : EvenCoordinateChains m) :
    DominoPath (3*m) ⟨2*m,2*m,2*m,le_rfl,le_rfl⟩ :=
  ⟨⟨fun i => c.val.states ⟨2*i.val,by omega⟩,by
    constructor
    · exact coordinateFlag_zero c.val
    · intro i; exact c.property i⟩,by
      change c.val.states ⟨2*(3*m),by omega⟩=_
      have hi : (⟨2*(3*m),by omega⟩ : Fin (3*(2*m)+1))=Fin.last (3*(2*m)) := Fin.ext (by simp; omega)
      rw [hi]
      exact coordinateFlag_last c.val⟩

noncomputable def expandEven {m : ℕ}
    (p : DominoPath (3*m) ⟨2*m,2*m,2*m,le_rfl,le_rfl⟩) : EvenCoordinateChains m :=
  ⟨{ states := fun k => refineState p.val ⟨k.val,by omega⟩
     cap := fun k => refineState_cap p ⟨k.val,by omega⟩
     size := fun k => refineState_size p.val ⟨k.val,by omega⟩
     step := fun k => refineState_step p.val ⟨k.val,by omega⟩ },by
    intro i
    change DominoStep (refineState p.val ⟨2*i.val,by omega⟩)
      (refineState p.val ⟨2*i.val+2,by omega⟩)
    have h0 := refineState_even p.val i.castSucc
    have h1 := refineState_even p.val i.succ
    change refineState p.val ⟨2*i.val,by omega⟩=p.val.val i.castSucc at h0
    change refineState p.val ⟨2*i.val+2,by omega⟩=p.val.val i.succ at h1
    rw [h0,h1]
    exact p.val.property.2 i⟩

theorem compress_expand_even {m : ℕ}
    (p : DominoPath (3*m) ⟨2*m,2*m,2*m,le_rfl,le_rfl⟩) :
    compressEven (expandEven p)=p := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact refineState_even p.val i

theorem compressEven_injective (m : ℕ) : Function.Injective (@compressEven m) := by
  intro c e he
  have hh : ∀ i : Fin (3*m+1),
      c.val.states ⟨2*i.val,by omega⟩=e.val.states ⟨2*i.val,by omega⟩ := by
    intro i
    exact congrFun (congrArg (fun p : DominoPath (3*m) ⟨2*m,2*m,2*m,le_rfl,le_rfl⟩ => p.val.val) he) i
  apply Subtype.ext
  apply CoordinateFlag.ext
  funext k
  by_cases hk : k.val%2=0
  · let i : Fin (3*m+1) := ⟨k.val/2,by omega⟩
    have he' : (⟨2*i.val,by omega⟩ : Fin (3*(2*m)+1))=k := Fin.ext (by dsimp [i]; omega)
    simpa only [he'] using hh i
  · let i : Fin (3*m) := ⟨k.val/2,by omega⟩
    have hk' : (⟨2*i.val+1,by omega⟩ : Fin (3*(2*m)+1))=k := Fin.ext (by dsimp [i]; omega)
    have hc0 := c.val.step (⟨2*i.val,by omega⟩ : Fin (3*(2*m)))
    have hc1 := c.val.step (⟨2*i.val+1,by omega⟩ : Fin (3*(2*m)))
    have he0 := e.val.step (⟨2*i.val,by omega⟩ : Fin (3*(2*m)))
    have he1 := e.val.step (⟨2*i.val+1,by omega⟩ : Fin (3*(2*m)))
    change UnitStep (c.val.states ⟨2*i.val,by omega⟩) (c.val.states ⟨2*i.val+1,by omega⟩) at hc0
    change UnitStep (c.val.states ⟨2*i.val+1,by omega⟩) (c.val.states ⟨2*i.val+2,by omega⟩) at hc1
    change UnitStep (e.val.states ⟨2*i.val,by omega⟩) (e.val.states ⟨2*i.val+1,by omega⟩) at he0
    change UnitStep (e.val.states ⟨2*i.val+1,by omega⟩) (e.val.states ⟨2*i.val+2,by omega⟩) at he1
    have h0 := hh i.castSucc
    change c.val.states ⟨2*i.val,by omega⟩=e.val.states ⟨2*i.val,by omega⟩ at h0
    have h1 := hh i.succ
    change c.val.states ⟨2*i.val+2,by omega⟩=e.val.states ⟨2*i.val+2,by omega⟩ at h1
    rw [← h0] at he0
    rw [← h1] at he1
    have hm := domino_middle_unique (c.property i) ⟨hc0,hc1⟩ ⟨he0,he1⟩
    simpa only [hk'] using hm

noncomputable def evenCompressionEquiv (m : ℕ) :
    SourceDominoChains (2*m) ≃ DominoPath (3*m) ⟨2*m,2*m,2*m,le_rfl,le_rfl⟩ :=
  (sourceEvenCoordinateEquiv m).trans (Equiv.ofBijective compressEven
    ⟨compressEven_injective m,fun p => ⟨expandEven p,compress_expand_even p⟩⟩)

theorem even_evac_domino (m : ℕ) :
    Fintype.card {w : K (2*m) // evac w=w}=D (2*m) (2*m) (2*m) := by
  unfold D
  rw [dite_eq_left ⟨le_rfl,le_rfl⟩]
  have ht : (2*m+2*m+2*m)/2=3*m := by omega
  rw [ht]
  exact Fintype.card_congr ((evacDominoEquiv _).trans (evenCompressionEquiv m))

#print axioms evenCompressionEquiv
#print axioms even_evac_domino
end Kreweras
```

### `KrewerasDualPairs.lean`

```lean
import KrewerasPathRefinement

namespace Kreweras
set_option linter.unusedSimpArgs false

theorem sourceRun_bijective {α : Type} {R : α → α → Prop} {N : ℕ} (s : List ℕ) :
    Function.Bijective (@sourceRun α R N s) := by
  induction s with
  | nil => exact Function.bijective_id
  | cons i s ih => exact ih.comp (sourceTau_involutive i).bijective

noncomputable def sourceConjugatorEquiv {α : Type} (R : α → α → Prop) (N : ℕ) :
    LinearExtension R N ≃ LinearExtension R N :=
  Equiv.ofBijective (sourceRun (dominoConjugatorSchedule N)) (sourceRun_bijective _)

noncomputable def sourceEvacPairedEquiv {α : Type} (R : α → α → Prop) (N : ℕ) :
    {e : LinearExtension R N // sourceEvac e=e} ≃
      {e : LinearExtension R N // PairedExtension e} := by
  let c := sourceConjugatorEquiv R N
  have h (e : LinearExtension R N) : sourceEvac (c e)=c e ↔ PairedExtension e := by
    rw [show sourceEvac (c e)=c (sourceRun (dominoPairSchedule N) e) from
      source_domino_conjugation e,c.injective.eq_iff,source_pair_fixed_iff]
  exact (Equiv.subtypeEquiv c (fun e => (h e).symm)).symm

def reverseLinearEquiv {α : Type} (R : α → α → Prop) (N : ℕ) :
    LinearExtension R N ≃ LinearExtension (fun p q => R q p) N where
  toFun := reverseLinear
  invFun := reverseLinear
  left_inv := reverseLinear_reverseLinear
  right_inv := reverseLinear_reverseLinear

def extensionLinearEquiv (n : ℕ) : Extension n ≃ LinearExtension (@posetLE n) (3*n) where
  toFun := asLinear
  invFun := fromLinear
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def wordDualEquiv (n : ℕ) : K n ≃ DualExtension n :=
  ((wordExtensionEquiv n).trans (extensionLinearEquiv n)).trans (reverseLinearEquiv _ _)

theorem wordDualEquiv_bridge {n : ℕ} (w : K n) :
    wordDualEquiv n (dualEvac w)=sourceEvac (wordDualEquiv n w) := by
  have hh := dualEvac_bridge w
  change label (dualEvac w)=extensionDualEvac (label w) at hh
  change reverseLinear (asLinear (label (dualEvac w)))=_
  rw [hh]
  exact reverseLinear_reverseLinear _

noncomputable def dualFixedSourceEquiv (n : ℕ) :
    {w : K n // dualEvac w=w} ≃ {e : DualExtension n // sourceEvac e=e} :=
  Equiv.subtypeEquiv (wordDualEquiv n) (fun w => by
    rw [← wordDualEquiv_bridge,(wordDualEquiv n).injective.eq_iff])

theorem paired_reverse_even_forward {α : Type} {R : α → α → Prop} {N : ℕ}
    (he : N%2=0) (e : LinearExtension R N) (h : PairedExtension e) :
    PairedExtension (reverseLinear e) := by
  intro i hi
  have hb := (pairSchedule_mem_iff _ _).mp hi
  let j := N-2-i
  have hj : j∈dominoPairSchedule N :=
    (pairSchedule_mem_iff _ _).mpr ⟨by dsimp [j]; omega,by dsimp [j]; omega⟩
  have hh := h j hj
  change R (e.order.symm (⟨i+1,InvolutionWord.pair_bound hi⟩ : Fin N).rev)
    (e.order.symm (⟨i,by omega⟩ : Fin N).rev)
  have h0 : (⟨i+1,InvolutionWord.pair_bound hi⟩ : Fin N).rev=⟨j,by have := InvolutionWord.pair_bound hj; omega⟩ :=
    Fin.ext (by simp only [Fin.val_rev]; dsimp [j]; omega)
  have h1 : (⟨i,by omega⟩ : Fin N).rev=⟨j+1,InvolutionWord.pair_bound hj⟩ :=
    Fin.ext (by simp only [Fin.val_rev]; dsimp [j]; omega)
  rw [h0,h1]
  exact hh

theorem paired_reverse_even_iff {α : Type} {R : α → α → Prop} {N : ℕ}
    (he : N%2=0) (e : LinearExtension R N) :
    PairedExtension (reverseLinear e) ↔ PairedExtension e := by
  constructor
  · intro h
    have hh := paired_reverse_even_forward he (reverseLinear e) h
    simpa only [reverseLinear_reverseLinear] using hh
  · exact paired_reverse_even_forward he e

#print axioms sourceEvacPairedEquiv
#print axioms dualFixedSourceEquiv
#print axioms paired_reverse_even_iff
end Kreweras
```

### `KrewerasEvenDual.lean`

```lean
import KrewerasDualPairs
import KrewerasEvenCompression

namespace Kreweras

noncomputable def dualFixedPairedEquiv (n : ℕ) :
    {w : K n // dualEvac w=w} ≃ {e : DualExtension n // PairedExtension e} :=
  (dualFixedSourceEquiv n).trans (sourceEvacPairedEquiv _ _)

noncomputable def evenPairedDualEquiv (m : ℕ) :
    {w : K (2*m) // PairedExtension (asLinear (label w))} ≃
      {e : DualExtension (2*m) // PairedExtension e} :=
  Equiv.subtypeEquiv (wordDualEquiv _) (fun w =>
    (paired_reverse_even_iff (by omega) (asLinear (label w))).symm)

noncomputable def evenDualEvacEquiv (m : ℕ) :
    {w : K (2*m) // dualEvac w=w} ≃ {w : K (2*m) // evac w=w} :=
  ((dualFixedPairedEquiv _).trans (evenPairedDualEquiv m).symm).trans (evacPairedEquiv _).symm

theorem even_dual_domino (m : ℕ) :
    Fintype.card {w : K (2*m) // dualEvac w=w}=D (2*m) (2*m) (2*m) :=
  (Fintype.card_congr (evenDualEvacEquiv m)).trans (even_evac_domino m)

#print axioms evenDualEvacEquiv
#print axioms even_dual_domino
end Kreweras
```

### `KrewerasTerminalPairs.lean`

```lean
import KrewerasDualPairs

namespace Kreweras
set_option linter.unusedSimpArgs false

/-- Pair all positions from the beginning, leaving a terminal singleton at odd size. -/
def ForwardPaired {α : Type} {R : α → α → Prop} {N : ℕ} (e : LinearExtension R N) : Prop :=
  ∀ j, ∀ hj : 2*j+1<N,
    R (e.order.symm ⟨2*j,by omega⟩) (e.order.symm ⟨2*j+1,hj⟩)

theorem paired_reverse_iff_forward {α : Type} {R : α → α → Prop} {N : ℕ}
    (e : LinearExtension R N) : PairedExtension (reverseLinear e) ↔ ForwardPaired e := by
  constructor
  · intro h j hj
    let i := N-2-2*j
    have hi : i∈dominoPairSchedule N :=
      (pairSchedule_mem_iff _ _).mpr ⟨by dsimp [i]; omega,by dsimp [i]; omega⟩
    have hh := h i hi
    change R (e.order.symm (⟨i+1,InvolutionWord.pair_bound hi⟩ : Fin N).rev)
      (e.order.symm (⟨i,by have := InvolutionWord.pair_bound hi; omega⟩ : Fin N).rev) at hh
    have h0 : (⟨i+1,InvolutionWord.pair_bound hi⟩ : Fin N).rev=⟨2*j,by omega⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; dsimp [i]; omega)
    have h1 : (⟨i,by have := InvolutionWord.pair_bound hi; omega⟩ : Fin N).rev=⟨2*j+1,hj⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; dsimp [i]; omega)
    rwa [h0,h1] at hh
  · intro h i hi
    have hb := (pairSchedule_mem_iff _ _).mp hi
    let j := (N-2-i)/2
    have hj : 2*j+1<N := by dsimp [j]; omega
    change R (e.order.symm (⟨i+1,InvolutionWord.pair_bound hi⟩ : Fin N).rev)
      (e.order.symm (⟨i,by omega⟩ : Fin N).rev)
    have h0 : (⟨i+1,InvolutionWord.pair_bound hi⟩ : Fin N).rev=⟨2*j,by omega⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; dsimp [j]; omega)
    have h1 : (⟨i,by omega⟩ : Fin N).rev=⟨2*j+1,hj⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; dsimp [j]; omega)
    rw [h0,h1]
    exact h j hj

noncomputable def dualFixedForwardEquiv (n : ℕ) :
    {w : K n // dualEvac w=w} ≃ {w : K n // ForwardPaired (asLinear (label w))} :=
  ((dualFixedSourceEquiv n).trans (sourceEvacPairedEquiv _ _)).trans
    (Equiv.subtypeEquiv (wordDualEquiv n) (fun w =>
      (paired_reverse_iff_forward (asLinear (label w))).symm)).symm

abbrev OddCoordinateChains (m : ℕ) := {c : CoordinateFlag (2*m+1) //
  ∀ i : Fin (3*m+1), DominoStep (c.states ⟨2*i.val,by omega⟩)
    (c.states ⟨2*i.val+2,by omega⟩)}

theorem odd_forward_flag_iff (m : ℕ) (w : K (2*m+1)) :
    ForwardPaired (asLinear (label w)) ↔
      ∀ i : Fin (3*m+1),
        DominoStep ((idealCoordinateFlag (extensionFlag (label w))).states ⟨2*i.val,by omega⟩)
          ((idealCoordinateFlag (extensionFlag (label w))).states ⟨2*i.val+2,by omega⟩) := by
  constructor
  · intro h i
    exact (@prefix_domino_iff (2*m+1) (2*i.val) (label w) (by omega)).mpr (h i.val (by omega))
  · intro h j hj
    exact (@prefix_domino_iff (2*m+1) (2*j) (label w) hj).mp (h ⟨j,by omega⟩)

noncomputable def oddForwardCoordinateEquiv (m : ℕ) :
    {w : K (2*m+1) // ForwardPaired (asLinear (label w))} ≃ OddCoordinateChains m :=
  Equiv.subtypeEquiv
    ((wordExtensionEquiv _).trans ((extensionIdealFlagEquiv _).trans (idealCoordinateEquiv _)))
    (odd_forward_flag_iff m)

noncomputable def oddDualCoordinateEquiv (m : ℕ) :
    {w : K (2*m+1) // dualEvac w=w} ≃ OddCoordinateChains m :=
  (dualFixedForwardEquiv _).trans (oddForwardCoordinateEquiv m)

#print axioms paired_reverse_iff_forward
#print axioms oddDualCoordinateEquiv
end Kreweras
```

### `KrewerasOddCompression.lean`

```lean
import KrewerasTerminalPairs
import KrewerasEvenCompression

namespace Kreweras
set_option linter.unusedSimpArgs false

def fullState (n : ℕ) : IdealState := ⟨n,n,n,le_rfl,le_rfl⟩

abbrev OddTerminalPaths (m : ℕ) := {p : AllDominoPaths (3*m+1) //
  UnitStep (p.val (Fin.last (3*m+1))) (fullState (2*m+1))}

def compressOdd {m : ℕ} (c : OddCoordinateChains m) : OddTerminalPaths m :=
  ⟨⟨fun i => c.val.states ⟨2*i.val,by omega⟩,by
    constructor
    · exact coordinateFlag_zero c.val
    · intro i; exact c.property i⟩,by
      have hh := c.val.step (⟨2*(3*m+1),by omega⟩ : Fin (3*(2*m+1)))
      change UnitStep (c.val.states ⟨2*(3*m+1),by omega⟩)
        (c.val.states ⟨2*(3*m+1)+1,by omega⟩) at hh
      have he : (⟨2*(3*m+1)+1,by omega⟩ : Fin (3*(2*m+1)+1))=Fin.last (3*(2*m+1)) :=
        Fin.ext (by simp; omega)
      rw [he,coordinateFlag_last] at hh
      exact hh⟩

noncomputable def oddExpandedState {m : ℕ} (p : OddTerminalPaths m)
    (k : Fin (3*(2*m+1)+1)) : IdealState :=
  if h : k.val≤2*(3*m+1) then refineState p.val ⟨k.val,by omega⟩ else fullState (2*m+1)

@[simp] theorem oddExpandedState_prefix {m : ℕ} (p : OddTerminalPaths m)
    (k : Fin (2*(3*m+1)+1)) :
    oddExpandedState p ⟨k.val,by omega⟩=refineState p.val k := by
  simp only [oddExpandedState,dite_eq_left (show k.val≤2*(3*m+1) by omega)]

@[simp] theorem oddExpandedState_last {m : ℕ} (p : OddTerminalPaths m) :
    oddExpandedState p (Fin.last (3*(2*m+1)))=fullState (2*m+1) := by
  simp only [oddExpandedState,Fin.val_last,dite_eq_right (show ¬3*(2*m+1)≤2*(3*m+1) by omega)]

theorem oddExpandedState_step {m : ℕ} (p : OddTerminalPaths m) (k : Fin (3*(2*m+1))) :
    UnitStep (oddExpandedState p k.castSucc) (oddExpandedState p k.succ) := by
  by_cases hk : k.val<2*(3*m+1)
  · have h0 := oddExpandedState_prefix p (⟨k.val,by omega⟩ : Fin (2*(3*m+1)+1))
    have h1 := oddExpandedState_prefix p (⟨k.val+1,by omega⟩ : Fin (2*(3*m+1)+1))
    change oddExpandedState p k.castSucc=_ at h0
    change oddExpandedState p k.succ=_ at h1
    rw [h0,h1]
    exact refineState_step p.val ⟨k.val,hk⟩
  · have he : k.val=2*(3*m+1) := by omega
    have h0 : k.castSucc=(⟨2*(3*m+1),by omega⟩ : Fin (3*(2*m+1)+1)) := Fin.ext he
    have h1 : k.succ=Fin.last (3*(2*m+1)) := Fin.ext (by simp; omega)
    rw [h0,h1,oddExpandedState_last]
    have hh := oddExpandedState_prefix p (Fin.last (2*(3*m+1)))
    change oddExpandedState p ⟨2*(3*m+1),by omega⟩=_ at hh
    rw [hh]
    have hr := refineState_even p.val (Fin.last (3*m+1))
    change refineState p.val (Fin.last (2*(3*m+1)))=p.val.val (Fin.last (3*m+1)) at hr
    rw [hr]
    exact p.property

noncomputable def expandOdd {m : ℕ} (p : OddTerminalPaths m) : OddCoordinateChains m :=
  ⟨{ states := oddExpandedState p
     cap := by
       intro k
       have hm : Monotone (fun i => (oddExpandedState p i).a) :=
         Fin.monotone_iff_le_succ.mpr (fun i => (oddExpandedState_step p i).1)
       have hh := hm (Fin.le_last k)
       dsimp only at hh
       rw [oddExpandedState_last] at hh
       exact hh
     size := by
       intro k
       unfold oddExpandedState
       split
       · exact refineState_size p.val _
       · dsimp [fullState]; omega
     step := oddExpandedState_step p },by
    intro i
    change DominoStep (oddExpandedState p ⟨2*i.val,by omega⟩)
      (oddExpandedState p ⟨2*i.val+2,by omega⟩)
    have h0 := oddExpandedState_prefix p ⟨2*i.val,by omega⟩
    have h1 := oddExpandedState_prefix p ⟨2*i.val+2,by omega⟩
    rw [h0,h1]
    have hr0 := refineState_even p.val i.castSucc
    have hr1 := refineState_even p.val i.succ
    change refineState p.val ⟨2*i.val,by omega⟩=_ at hr0
    change refineState p.val ⟨2*i.val+2,by omega⟩=_ at hr1
    rw [hr0,hr1]
    exact p.val.property.2 i⟩

theorem compress_expand_odd {m : ℕ} (p : OddTerminalPaths m) : compressOdd (expandOdd p)=p := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change oddExpandedState p ⟨2*i.val,by omega⟩=p.val.val i
  exact (oddExpandedState_prefix p ⟨2*i.val,by omega⟩).trans (refineState_even p.val i)

theorem compressOdd_injective (m : ℕ) : Function.Injective (@compressOdd m) := by
  intro c e he
  have hh : ∀ i : Fin (3*m+2),
      c.val.states ⟨2*i.val,by omega⟩=e.val.states ⟨2*i.val,by omega⟩ := by
    intro i
    exact congrFun (congrArg (fun p : OddTerminalPaths m => p.val.val) he) i
  apply Subtype.ext
  apply CoordinateFlag.ext
  funext k
  by_cases hlast : k=Fin.last (3*(2*m+1))
  · rw [hlast,coordinateFlag_last,coordinateFlag_last]
  · have hb : k.val<3*(2*m+1) := by
      have := k.isLt
      have hn : k.val≠3*(2*m+1) := fun h => hlast (Fin.ext h)
      omega
    by_cases hk : k.val%2=0
    · let i : Fin (3*m+2) := ⟨k.val/2,by omega⟩
      have he' : (⟨2*i.val,by omega⟩ : Fin (3*(2*m+1)+1))=k := Fin.ext (by dsimp [i]; omega)
      simpa only [he'] using hh i
    · let i : Fin (3*m+1) := ⟨k.val/2,by omega⟩
      have hk' : (⟨2*i.val+1,by omega⟩ : Fin (3*(2*m+1)+1))=k := Fin.ext (by dsimp [i]; omega)
      have hc0 := c.val.step (⟨2*i.val,by omega⟩ : Fin (3*(2*m+1)))
      have hc1 := c.val.step (⟨2*i.val+1,by omega⟩ : Fin (3*(2*m+1)))
      have he0 := e.val.step (⟨2*i.val,by omega⟩ : Fin (3*(2*m+1)))
      have he1 := e.val.step (⟨2*i.val+1,by omega⟩ : Fin (3*(2*m+1)))
      change UnitStep (c.val.states ⟨2*i.val,by omega⟩) (c.val.states ⟨2*i.val+1,by omega⟩) at hc0
      change UnitStep (c.val.states ⟨2*i.val+1,by omega⟩) (c.val.states ⟨2*i.val+2,by omega⟩) at hc1
      change UnitStep (e.val.states ⟨2*i.val,by omega⟩) (e.val.states ⟨2*i.val+1,by omega⟩) at he0
      change UnitStep (e.val.states ⟨2*i.val+1,by omega⟩) (e.val.states ⟨2*i.val+2,by omega⟩) at he1
      have h0 := hh i.castSucc
      change c.val.states ⟨2*i.val,by omega⟩=e.val.states ⟨2*i.val,by omega⟩ at h0
      have h1 := hh i.succ
      change c.val.states ⟨2*i.val+2,by omega⟩=e.val.states ⟨2*i.val+2,by omega⟩ at h1
      rw [← h0] at he0
      rw [← h1] at he1
      have hm := domino_middle_unique (c.property i) ⟨hc0,hc1⟩ ⟨he0,he1⟩
      simpa only [hk'] using hm

noncomputable def oddCompressionEquiv (m : ℕ) : OddCoordinateChains m ≃ OddTerminalPaths m :=
  Equiv.ofBijective compressOdd
    ⟨compressOdd_injective m,fun p => ⟨expandOdd p,compress_expand_odd p⟩⟩

#print axioms oddCompressionEquiv
end Kreweras
```

### `KrewerasOddDual.lean`

```lean
import KrewerasOddCompression
import KrewerasDominoSymmetry

namespace Kreweras
set_option linter.unusedSimpArgs false

def oddEndB (m : ℕ) : IdealState := ⟨2*m+1,2*m,2*m+1,by omega,le_rfl⟩
def oddEndC (m : ℕ) : IdealState := ⟨2*m+1,2*m+1,2*m,le_rfl,by omega⟩

theorem terminal_state_iff (m : ℕ) (s : IdealState) :
    UnitStep s (fullState (2*m+1)) ↔ s=oddEndB m ∨ s=oddEndC m := by
  constructor
  · intro h
    have hb := s.b_le_a
    have hc := s.c_le_a
    unfold UnitStep fullState at h
    dsimp at h
    by_cases he : s.b=2*m+1
    · right; apply IdealState.ext <;> dsimp [oddEndC] <;> omega
    · left; apply IdealState.ext <;> dsimp [oddEndB] <;> omega
  · rintro (rfl|rfl) <;> simp only [UnitStep,fullState,oddEndB,oddEndC] <;> omega

theorem oddEnds_ne (m : ℕ) : oddEndB m≠oddEndC m := by
  intro h
  have hh := congrArg IdealState.b h
  dsimp [oddEndB,oddEndC] at hh
  omega

noncomputable def terminalToSum {m : ℕ} (p : OddTerminalPaths m) :
    DominoPath (3*m+1) (oddEndB m) ⊕ DominoPath (3*m+1) (oddEndC m) := by
  classical
  exact if h : p.val.val (Fin.last (3*m+1))=oddEndB m then Sum.inl ⟨p.val,h⟩
    else Sum.inr ⟨p.val,((terminal_state_iff m _).mp p.property).resolve_left h⟩

def sumToTerminal {m : ℕ} :
    DominoPath (3*m+1) (oddEndB m) ⊕ DominoPath (3*m+1) (oddEndC m) → OddTerminalPaths m
  | .inl p => ⟨p.val,(terminal_state_iff m _).mpr (Or.inl p.property)⟩
  | .inr p => ⟨p.val,(terminal_state_iff m _).mpr (Or.inr p.property)⟩

noncomputable def oddTerminalSumEquiv (m : ℕ) : OddTerminalPaths m ≃
    DominoPath (3*m+1) (oddEndB m) ⊕ DominoPath (3*m+1) (oddEndC m) where
  toFun := terminalToSum
  invFun := sumToTerminal
  left_inv p := by
    classical
    unfold terminalToSum
    split <;> rfl
  right_inv p := by
    classical
    rcases p with p|p
    · unfold terminalToSum
      split
      · rfl
      · rename_i h
        exact False.elim (h p.property)
    · unfold terminalToSum
      split
      · rename_i h
        have he : oddEndC m=oddEndB m := p.property.symm.trans h
        exact False.elim ((oddEnds_ne m) he.symm)
      · rfl

theorem odd_dual_domino (m : ℕ) :
    Fintype.card {w : K (2*m+1) // dualEvac w=w}=2*D (2*m+1) (2*m+1) (2*m) := by
  have he := Fintype.card_congr
    (((oddDualCoordinateEquiv m).trans (oddCompressionEquiv m)).trans (oddTerminalSumEquiv m))
  rw [Fintype.card_sum] at he
  have hC : Fintype.card (DominoPath (3*m+1) (oddEndC m))=D (2*m+1) (2*m+1) (2*m) := by
    unfold D
    rw [dite_eq_left ⟨le_rfl,by omega⟩]
    have ht : (2*m+1+(2*m+1)+2*m)/2=3*m+1 := by omega
    rw [ht]; rfl
  have hB : Fintype.card (DominoPath (3*m+1) (oddEndB m))=
      Fintype.card (DominoPath (3*m+1) (oddEndC m)) :=
    Fintype.card_congr (swapDominoEquiv _ (oddEndB m))
  rw [hB,hC] at he
  omega

#print axioms oddTerminalSumEquiv
#print axioms odd_dual_domino
end Kreweras
```

### `KrewerasConstructiveLift.lean`

```lean
import KrewerasDominoPaths

namespace Kreweras
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

set_option maxHeartbeats 2000000 in
/-- A legal sector transition lifts to an actual five-move ideal transition. -/
theorem encode_lift {s : IdealState} (hs : HasSector s) (q : SectorPoint)
    (hq : SectorStep (encode s) q) : ∃ t, DominoStep s t ∧ encode t=q := by
  have sb := s.b_le_a
  have sc := s.c_le_a
  rcases q with ⟨r,x,y⟩
  rcases hq with ⟨hr,hxy⟩|hEX|hXE|hEY|hYE
  · rcases hxy with ⟨hx,hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
    · let t : IdealState := ⟨s.a+2,s.b,s.c,by omega,by omega⟩
      refine ⟨t,Or.inl ⟨rfl,rfl,rfl⟩,?_⟩
      unfold encode at hr hx hy ⊢
      dsimp [t] at *
      split_ifs at * <;> simp_all only [SectorPoint.mk.injEq,reduceCtorEq,true_and,false_and,and_true] <;> omega
    · have ht : s.b+2≤s.a := by
        unfold encode at hx
        unfold HasSector at hs
        dsimp at hx
        omega
      let t : IdealState := ⟨s.a,s.b+2,s.c,ht,sc⟩
      refine ⟨t,Or.inr (Or.inl ⟨rfl,rfl,rfl⟩),?_⟩
      unfold encode at hr hx hy ⊢
      dsimp [t] at *
      split_ifs at * <;> simp_all only [SectorPoint.mk.injEq,reduceCtorEq,true_and,false_and,and_true] <;> omega
    · have ht : s.c+2≤s.a := by
        unfold encode at hy
        unfold HasSector at hs
        dsimp at hy
        omega
      let t : IdealState := ⟨s.a,s.b,s.c+2,sb,ht⟩
      refine ⟨t,Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)),?_⟩
      unfold encode at hr hx hy ⊢
      dsimp [t] at *
      split_ifs at * <;> simp_all only [SectorPoint.mk.injEq,reduceCtorEq,true_and,false_and,and_true] <;> omega
  · rcases hEX with ⟨hsec,rfl,hzero,rfl,rfl⟩
    have he : s.a=s.b := by
      unfold encode at hsec hzero
      unfold HasSector at hs
      dsimp only at hzero hsec
      split_ifs at hsec <;> simp only [reduceCtorEq] at hsec <;> omega
    let t : IdealState := ⟨s.a+1,s.b+1,s.c,by omega,by omega⟩
    refine ⟨t,Or.inr (Or.inr (Or.inr (Or.inl ⟨he,rfl,rfl,rfl⟩))),?_⟩
    unfold encode at hsec hzero ⊢
    unfold HasSector at hs
    dsimp [t] at *
    split_ifs at * <;> simp only [SectorPoint.mk.injEq,reduceCtorEq,true_and,false_and,and_true] at * <;> omega
  · rcases hXE with ⟨hsec,rfl,hzero,rfl,rfl⟩
    have he : s.a=s.b := by
      unfold encode at hsec hzero
      unfold HasSector at hs
      dsimp only at hzero hsec
      split_ifs at hsec <;> simp only [reduceCtorEq] at hsec <;> omega
    let t : IdealState := ⟨s.a+1,s.b+1,s.c,by omega,by omega⟩
    refine ⟨t,Or.inr (Or.inr (Or.inr (Or.inl ⟨he,rfl,rfl,rfl⟩))),?_⟩
    unfold encode at hsec hzero ⊢
    unfold HasSector at hs
    dsimp [t] at *
    split_ifs at * <;> simp only [SectorPoint.mk.injEq,reduceCtorEq,true_and,false_and,and_true] at * <;> omega
  · rcases hEY with ⟨hsec,rfl,hzero,rfl,rfl⟩
    have he : s.a=s.c := by
      unfold encode at hsec hzero
      unfold HasSector at hs
      dsimp only at hzero hsec
      split_ifs at hsec <;> simp only [reduceCtorEq] at hsec <;> omega
    let t : IdealState := ⟨s.a+1,s.b,s.c+1,by omega,by omega⟩
    refine ⟨t,Or.inr (Or.inr (Or.inr (Or.inr ⟨he,rfl,rfl,rfl⟩))),?_⟩
    unfold encode at hsec hzero ⊢
    unfold HasSector at hs
    dsimp [t] at *
    split_ifs at * <;> simp only [SectorPoint.mk.injEq,reduceCtorEq,true_and,false_and,and_true] at * <;> omega
  · rcases hYE with ⟨hsec,rfl,hzero,rfl,rfl⟩
    have he : s.a=s.c := by
      unfold encode at hsec hzero
      unfold HasSector at hs
      dsimp only at hzero hsec
      split_ifs at hsec <;> simp only [reduceCtorEq] at hsec <;> omega
    let t : IdealState := ⟨s.a+1,s.b,s.c+1,by omega,by omega⟩
    refine ⟨t,Or.inr (Or.inr (Or.inr (Or.inr ⟨he,rfl,rfl,rfl⟩))),?_⟩
    unfold encode at hsec hzero ⊢
    unfold HasSector at hs
    dsimp [t] at *
    split_ifs at * <;> simp only [SectorPoint.mk.injEq,reduceCtorEq,true_and,false_and,and_true] at * <;> omega

#print axioms encode_lift
end Kreweras
```

### `KrewerasPathLift.lean`

```lean
import KrewerasConstructiveLift

namespace Kreweras
set_option linter.unusedSimpArgs false

def encodeWalk {d : ℕ} (p : AllDominoPaths d) : SectorWalk d :=
  ⟨fun i => encode (p.val i),by
    constructor
    · change encode (p.val 0)=_
      rw [p.property.1]; rfl
    · intro i
      exact encode_step (reachable_sector (path_reachable p i.castSucc)) (p.property.2 i)⟩

theorem encodeWalk_injective (d : ℕ) : Function.Injective (@encodeWalk d) := by
  intro p q h
  apply Subtype.ext
  funext i
  apply encode_time_injective (reachable_sector (path_reachable p i))
    (reachable_sector (path_reachable q i)) ((path_size p i).trans (path_size q i).symm)
  exact congrArg unfold (congrFun (congrArg Subtype.val h) i)

/-- Constructive existence is proved one transition at a time; it is not inferred
from injectivity of the unfolding map. -/
theorem sector_path_lift (d : ℕ) (p : SectorWalk d) :
    ∃ q : AllDominoPaths d, ∀ i, encode (q.val i)=p.val i := by
  induction d with
  | zero =>
    refine ⟨⟨fun _ => zeroState,⟨rfl,fun i => Fin.elim0 i⟩⟩,?_⟩
    intro i
    have hi : i=0 := Fin.eq_zero i
    rw [hi,p.property.1]; rfl
  | succ d ih =>
    let r : SectorWalk d := ⟨fun i => p.val i.castSucc,by
      constructor
      · exact p.property.1
      · intro i; exact p.property.2 i.castSucc⟩
    obtain ⟨q,hq⟩ := ih r
    have hlast := hq (Fin.last d)
    have hp := p.property.2 (Fin.last d)
    change SectorStep (p.val (Fin.last d).castSucc) (p.val (Fin.last (d+1))) at hp
    rw [← hlast] at hp
    obtain ⟨t,ht,he⟩ := encode_lift (reachable_sector (path_reachable q (Fin.last d)))
      (p.val (Fin.last (d+1))) hp
    let f : Fin (d+1+1) → IdealState := Fin.lastCases t q.val
    have hstart : f 0=zeroState := by
      change f (0 : Fin (d+1)).castSucc=zeroState
      simp only [f,Fin.lastCases_castSucc,q.property.1]
    have hstep (i : Fin (d+1)) : DominoStep (f i.castSucc) (f i.succ) := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change DominoStep (f (Fin.last d).castSucc) (f (Fin.last (d+1)))
        simpa only [f,Fin.lastCases_castSucc,Fin.lastCases_last] using ht
      · change DominoStep (f j.castSucc.castSucc) (f j.succ.castSucc)
        simpa only [f,Fin.lastCases_castSucc] using q.property.2 j
    refine ⟨⟨f,hstart,hstep⟩,?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [f,Fin.lastCases_last] using he
    · simpa only [f,Fin.lastCases_castSucc] using hq j

theorem encodeWalk_bijective (d : ℕ) : Function.Bijective (@encodeWalk d) := by
  refine ⟨encodeWalk_injective d,?_⟩
  intro p
  obtain ⟨q,hq⟩ := sector_path_lift d p
  exact ⟨q,Subtype.ext (funext hq)⟩

noncomputable def dominoSectorEquiv (d : ℕ) : AllDominoPaths d ≃ SectorWalk d :=
  Equiv.ofBijective encodeWalk (encodeWalk_bijective d)

noncomputable def dominoSlitEquiv (d : ℕ) : AllDominoPaths d ≃ SlitWalk d :=
  (dominoSectorEquiv d).trans (sectorSlitWalkEquiv d)

noncomputable instance (d : ℕ) : Fintype (SlitWalk d) :=
  Fintype.ofEquiv (AllDominoPaths d) (dominoSlitEquiv d)

noncomputable def originCount (d : ℕ) : ℕ := Fintype.card {p : SlitWalk d // p.val (Fin.last d)=(0,0)}
noncomputable def adjacentCount (d : ℕ) : ℕ := Fintype.card {p : SlitWalk d // p.val (Fin.last d)=(-1,0)}

#print axioms sector_path_lift
#print axioms dominoSlitEquiv
end Kreweras
```

### `KrewerasWalkEndpoints.lean`

```lean
import KrewerasPathLift
import KrewerasEvenDual
import KrewerasOddDual

namespace Kreweras

noncomputable def dominoSlitEndpointEquiv (d : ℕ) (s : IdealState)
    (hs : HasSector s) (hsize : s.a+s.b+s.c=2*d) :
    DominoPath d s ≃ {p : SlitWalk d // p.val (Fin.last d)=unfold (encode s)} :=
  Equiv.subtypeEquiv (dominoSlitEquiv d) (fun p => by
    change p.val (Fin.last d)=s ↔ unfold (encode (p.val (Fin.last d)))=unfold (encode s)
    constructor
    · intro h; rw [h]
    · intro h
      exact encode_time_injective (reachable_sector (path_reachable p (Fin.last d))) hs
        ((path_size p (Fin.last d)).trans hsize.symm) h)

theorem origin_endpoint (m : ℕ) : D (2*m) (2*m) (2*m)=originCount (3*m) := by
  unfold D
  rw [dite_eq_left ⟨le_rfl,le_rfl⟩]
  have ht : (2*m+2*m+2*m)/2=3*m := by omega
  rw [ht]
  let s : IdealState := ⟨2*m,2*m,2*m,le_rfl,le_rfl⟩
  have hs : HasSector s := Or.inl ⟨by dsimp [s]; omega,by dsimp [s]; omega,by dsimp [s]; omega⟩
  have he := dominoSlitEndpointEquiv (3*m) s hs (by dsimp [s]; omega)
  have hp : unfold (encode s)=(0,0) := even_diagonal_position m
  rw [hp] at he
  exact Fintype.card_congr he

theorem adjacent_endpoint (m : ℕ) : D (2*m+1) (2*m+1) (2*m)=adjacentCount (3*m+1) := by
  unfold D
  rw [dite_eq_left ⟨le_rfl,by omega⟩]
  have ht : (2*m+1+(2*m+1)+2*m)/2=3*m+1 := by omega
  rw [ht]
  let s : IdealState := ⟨2*m+1,2*m+1,2*m,le_rfl,by omega⟩
  have hs : HasSector s := Or.inr (Or.inl
    ⟨by dsimp [s]; omega,by dsimp [s]; omega,by dsimp [s]; omega⟩)
  have he := dominoSlitEndpointEquiv (3*m+1) s hs (by dsimp [s]; omega)
  have hp : unfold (encode s)=(-1,0) := odd_adjacent_position m
  rw [hp] at he
  exact Fintype.card_congr he

/-- Both positive even counts are the same literal slit-walk endpoint count. -/
theorem even_counts_walk (m : ℕ) :
    Fintype.card {w : K (2*m) // dualEvac w=w}=originCount (3*m) ∧
      Fintype.card {w : K (2*m) // evac w=w}=originCount (3*m) :=
  ⟨(even_dual_domino m).trans (origin_endpoint m),
    (even_evac_domino m).trans (origin_endpoint m)⟩

/-- The remaining odd positive count is twice the adjacent-endpoint count. -/
theorem odd_counts_walk (m : ℕ) :
    Fintype.card {w : K (2*m+1) // dualEvac w=w}=2*adjacentCount (3*m+1) ∧
      Fintype.card {w : K (2*m+1) // evac w=w}=0 :=
  ⟨(odd_dual_domino m).trans (congrArg (fun k => 2*k) (adjacent_endpoint m)),odd_evac_zero m⟩

#print axioms even_counts_walk
#print axioms odd_counts_walk

#print axioms dominoSlitEndpointEquiv
#print axioms origin_endpoint
#print axioms adjacent_endpoint
end Kreweras
```

### `KrewerasEnumerationHelpers.lean`

```lean
import KrewerasWalkEndpoints
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.LaurentSeries

namespace Kreweras

/-- The contiguous binomial identity used to match the two logarithms. -/
theorem choose_identity (j : ℕ) (hj : 0<j) :
    Nat.choose (3*j-1) j=2*Nat.choose (3*j-1) (j-1) := by
  have h := Nat.choose_succ_right_eq (3*j-1) (j-1)
  have h0 : j-1+1=j := by omega
  have h1 : 3*j-1-(j-1)=2*j := by omega
  rw [h0,h1] at h
  apply Nat.eq_of_mul_eq_mul_right hj
  calc
    Nat.choose (3*j-1) j*j=Nat.choose (3*j-1) (j-1)*(2*j) := h
    _=(2*Nat.choose (3*j-1) (j-1))*j := by ac_rfl

/-- Every Laurent derivative has zero residue. -/
theorem residue_derivative (F : LaurentSeries ℚ) :
    (LaurentSeries.derivative ℚ F).coeff (-1)=0 := by
  simp [LaurentSeries.derivative,LaurentSeries.hasseDeriv_coeff]

#print axioms choose_identity
#print axioms residue_derivative
end Kreweras
```

### `KrewerasProducts.lean`

```lean
import KrewerasStatement
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Kreweras
open scoped BigOperators

/-- Split the factorial into its three residue classes modulo three. -/
theorem factorial_residues (m : ℕ) : Nat.factorial (3*m) =
    3^m * Nat.factorial m *
      (∏ j ∈ Finset.Icc 1 m, (3*j-1)) *
      (∏ j ∈ Finset.Icc 1 m, (3*j-2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h0 : 3*(m+1)=3*m+2+1 := by omega
    have h1 : 3*(m+1)-1=3*m+2 := by omega
    have h2 : 3*(m+1)-2=3*m+1 := by omega
    rw [h0, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, ih,
      Nat.factorial_succ, pow_succ,
      Finset.prod_Icc_succ_top (by omega : 1≤m+1),
      Finset.prod_Icc_succ_top (by omega : 1≤m+1), h1, h2]
    ring

/-- The exact rational closed form needed at even size. -/
def evenProduct (m : ℕ) : ℚ :=
  (4^m * Nat.factorial (3*m) : ℕ) /
    (Nat.factorial m * Nat.factorial (2*m+1) : ℕ)

/-- The exact rational closed form needed at odd size (twice the adjacent count). -/
def oddProduct (m : ℕ) : ℚ :=
  (4^(m+1) * Nat.factorial (3*m+1) : ℕ) /
    (Nat.factorial m * Nat.factorial (2*m+2) : ℕ)

theorem P_even (m : ℕ) : P (2*m) = evenProduct m := by
  have h0 : 2*m/2=m := by omega
  have h1 : (2*m+1)/2=m := by omega
  unfold P evenProduct
  rw [h0,h1,factorial_residues]
  push_cast
  have hf : (Nat.factorial m : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

theorem P_odd (m : ℕ) : P (2*m+1) = oddProduct m := by
  have h0 : (2*m+1)/2=m := by omega
  have h1 : (2*m+1+1)/2=m+1 := by omega
  have h2 : 2*m+1+1=2*m+2 := by omega
  have h3 : 3*(m+1)-2=3*m+1 := by omega
  unfold P oddProduct
  rw [h0,h1,h2,Finset.prod_Icc_succ_top (by omega : 1≤m+1),h3,
    Nat.factorial_succ (3*m), factorial_residues]
  push_cast
  have hf : (Nat.factorial m : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

#print axioms factorial_residues
#print axioms P_even
#print axioms P_odd
end Kreweras
```

### `KrewerasAssembly.lean`

```lean
import KrewerasWalkEndpoints
import KrewerasProducts
import KrewerasSmallOne

namespace Kreweras

/-- These are the two outstanding walk evaluations, not assumed declarations. -/
def WalkEnumeration : Prop :=
  (∀ m : ℕ, (originCount (3*m) : ℚ)=evenProduct m) ∧
  (∀ m : ℕ, (2*adjacentCount (3*m+1) : ℚ)=oddProduct m)

theorem origin_count_zero : originCount 0=1 := by
  have h := (even_counts_walk 0).1
  have he : Fintype.card {w : K (2*0) // dualEvac w=w}=1 := by decide
  simpa using h.symm.trans he

theorem adjacent_count_one : adjacentCount 1=1 := by
  have h := (odd_counts_walk 0).1
  have he : Fintype.card {w : K 1 // dualEvac w=w}=2 := small_dual_one
  simp only [Nat.mul_zero,Nat.zero_add] at h
  rw [he] at h
  omega

/-- Complete final assembly, with the missing enumeration exposed as a hypothesis. -/
theorem literal_of_walk_enumeration (h : WalkEnumeration) : LiteralEndpoint := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨m,rfl⟩|⟨m,rfl⟩
  · have hh := even_counts_walk m
    have hp := h.1 m
    have he : Even (m+m) := ⟨m,rfl⟩
    have hm : m+m=2*m := by omega
    rw [hm] at he ⊢
    rw [ite_eq_left he,hh.1,hh.2,P_even]
    exact ⟨hp,hp⟩
  · have hh := odd_counts_walk m
    have he : ¬Even (2*m+1) := by
      rintro ⟨k,hk⟩; omega
    rw [ite_eq_right he,hh.1,hh.2,P_odd]
    exact ⟨by exact_mod_cast h.2 m,by norm_num⟩

/-- Conversely, the literal source claim entails both walk evaluations, including
m=0, where the even source claim does not itself apply. -/
theorem walk_enumeration_of_literal (h : LiteralEndpoint) : WalkEnumeration := by
  constructor
  · intro m
    by_cases hm : m=0
    · subst m
      norm_num [origin_count_zero,evenProduct]
    · have hh := (h (2*m) (by omega)).1
      rw [(even_counts_walk m).1,P_even] at hh
      exact hh
  · intro m
    have hh := (h (2*m+1) (by omega)).1
    rw [(odd_counts_walk m).1,P_odd] at hh
    exact_mod_cast hh

theorem literal_iff_walk_enumeration : LiteralEndpoint ↔ WalkEnumeration :=
  ⟨walk_enumeration_of_literal,literal_of_walk_enumeration⟩

#print axioms origin_count_zero
#print axioms adjacent_count_one
#print axioms literal_of_walk_enumeration
#print axioms walk_enumeration_of_literal
#print axioms literal_iff_walk_enumeration
end Kreweras
```

### `KrewerasProductRecurrences.lean`

```lean
import KrewerasProducts

namespace Kreweras

@[simp] theorem evenProduct_zero : evenProduct 0=1 := by norm_num [evenProduct]
@[simp] theorem oddProduct_zero : oddProduct 0=2 := by norm_num [oddProduct]

/-- Scalar algebra only; this does not assert a recurrence for walks. -/
theorem evenProduct_recurrence (m : ℕ) :
    ((m+1)*(2*m+3) : ℕ)*evenProduct (m+1) =
      (6*(3*m+1)*(3*m+2) : ℕ)*evenProduct m := by
  have h0 : 3*(m+1)=3*m+2+1 := by omega
  have h1 : 2*(m+1)+1=2*m+2+1 := by omega
  unfold evenProduct
  rw [h0,h1,Nat.factorial_succ (3*m+2),Nat.factorial_succ (3*m+1),
    Nat.factorial_succ (3*m),Nat.factorial_succ (2*m+2),Nat.factorial_succ (2*m+1),
    Nat.factorial_succ m,pow_succ]
  push_cast
  have f0 : (Nat.factorial m : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  have f1 : (Nat.factorial (2*m+1) : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*m+1)
  field_simp
  ring

/-- Twice the adjacent closed form obeys the same homogeneous recurrence. -/
theorem oddProduct_recurrence (m : ℕ) :
    ((m+2)*(2*m+3) : ℕ)*oddProduct (m+1) =
      (6*(3*m+2)*(3*m+4) : ℕ)*oddProduct m := by
  have h0 : 3*(m+1)+1=3*m+3+1 := by omega
  have h1 : 2*(m+1)+2=2*m+3+1 := by omega
  unfold oddProduct
  rw [h0,h1,Nat.factorial_succ (3*m+3),Nat.factorial_succ (3*m+2),
    Nat.factorial_succ (3*m+1),Nat.factorial_succ (2*m+3),Nat.factorial_succ (2*m+2),
    Nat.factorial_succ m,pow_succ]
  push_cast
  have f0 : (Nat.factorial m : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  have f1 : (Nat.factorial (2*m+2) : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*m+2)
  field_simp
  ring

#print axioms evenProduct_recurrence
#print axioms oddProduct_recurrence
end Kreweras
```

### `KrewerasRecurrenceReduction.lean`

```lean
import KrewerasAssembly
import KrewerasProductRecurrences

namespace Kreweras

/-- An alternative exact remaining obligation: these recurrences for the actual
walk counts have NOT been proved. The predicate supplies no assumption globally. -/
def WalkRecurrences : Prop :=
  (∀ m : ℕ, ((m+1)*(2*m+3) : ℕ)*(originCount (3*(m+1)) : ℚ) =
    (6*(3*m+1)*(3*m+2) : ℕ)*(originCount (3*m) : ℚ)) ∧
  (∀ m : ℕ, ((m+2)*(2*m+3) : ℕ)*(2*adjacentCount (3*(m+1)+1) : ℚ) =
    (6*(3*m+2)*(3*m+4) : ℕ)*(2*adjacentCount (3*m+1) : ℚ))

theorem walk_enumeration_of_recurrences (h : WalkRecurrences) : WalkEnumeration := by
  constructor
  · intro m
    induction m with
    | zero => norm_num [origin_count_zero]
    | succ m ih =>
      have hc : (((m+1)*(2*m+3) : ℕ) : ℚ)≠0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega)) :
          (m+1)*(2*m+3)≠0)
      have hh := h.1 m
      rw [ih] at hh
      exact mul_left_cancel₀ hc (hh.trans (evenProduct_recurrence m).symm)
  · intro m
    induction m with
    | zero => norm_num [adjacent_count_one]
    | succ m ih =>
      have hc : (((m+2)*(2*m+3) : ℕ) : ℚ)≠0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega)) :
          (m+2)*(2*m+3)≠0)
      have hh := h.2 m
      rw [ih] at hh
      exact mul_left_cancel₀ hc (hh.trans (oddProduct_recurrence m).symm)

theorem walk_recurrences_of_enumeration (h : WalkEnumeration) : WalkRecurrences := by
  constructor
  · intro m
    rw [h.1 (m+1),h.1 m]
    exact evenProduct_recurrence m
  · intro m
    rw [h.2 (m+1),h.2 m]
    exact oddProduct_recurrence m

theorem literal_iff_walk_recurrences : LiteralEndpoint ↔ WalkRecurrences :=
  literal_iff_walk_enumeration.trans
    ⟨walk_recurrences_of_enumeration,walk_enumeration_of_recurrences⟩

#print axioms walk_enumeration_of_recurrences
#print axioms walk_recurrences_of_enumeration
#print axioms literal_iff_walk_recurrences
end Kreweras
```

### `KrewerasWalkSupport.lean`

```lean
import KrewerasAssembly

namespace Kreweras

/-- Every step increases u+v+time by either zero or three. -/
theorem walk_time_mod {d : ℕ} (p : SlitWalk d) (i : Fin (d+1)) :
    ((p.val i).1+(p.val i).2+(i.val : ℤ))%3=0 := by
  induction i using Fin.induction with
  | zero => rw [p.property.1]; norm_num
  | succ i ih =>
    have h := p.property.2.2 i
    simp only [Fin.val_castSucc] at ih
    change ((p.val i.succ).1+(p.val i.succ).2+(i.val+1 : ℕ))%3=0
    rcases h with ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩ <;> push_cast <;> omega

theorem origin_time {d : ℕ} (p : SlitWalk d) (h : p.val (Fin.last d)=(0,0)) :
    d%3=0 := by
  have ht := walk_time_mod p (Fin.last d)
  rw [h] at ht
  dsimp at ht
  omega

theorem adjacent_time {d : ℕ} (p : SlitWalk d) (h : p.val (Fin.last d)=(-1,0)) :
    d%3=1 := by
  have ht := walk_time_mod p (Fin.last d)
  rw [h] at ht
  dsimp at ht
  omega

theorem origin_count_other (d : ℕ) (h : d%3≠0) : originCount d=0 := by
  classical
  unfold originCount
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun p => h (origin_time p.val p.property)⟩

theorem adjacent_count_other (d : ℕ) (h : d%3≠1) : adjacentCount d=0 := by
  classical
  unfold adjacentCount
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun p => h (adjacent_time p.val p.property)⟩

#print axioms walk_time_mod
#print axioms origin_count_other
#print axioms adjacent_count_other
end Kreweras
```

### `KrewerasEndpointSeries.lean`

```lean
import KrewerasWalkSupport
import Mathlib.RingTheory.PowerSeries.Basic

namespace Kreweras

/-- Independently defined series of actual slit-walk cardinalities. -/
noncomputable def L : PowerSeries ℚ := PowerSeries.mk fun d => (originCount d : ℚ)
noncomputable def J : PowerSeries ℚ := PowerSeries.mk fun d => (adjacentCount d : ℚ)

@[simp] theorem L_coeff (d : ℕ) : PowerSeries.coeff d L=(originCount d : ℚ) :=
  PowerSeries.coeff_mk _ _
@[simp] theorem J_coeff (d : ℕ) : PowerSeries.coeff d J=(adjacentCount d : ℚ) :=
  PowerSeries.coeff_mk _ _

theorem L_coeff_other (d : ℕ) (h : d%3≠0) : PowerSeries.coeff d L=0 := by
  simp [origin_count_other d h]
theorem J_coeff_other (d : ℕ) (h : d%3≠1) : PowerSeries.coeff d J=0 := by
  simp [adjacent_count_other d h]

@[simp] theorem L_constant : PowerSeries.constantCoeff L=1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,L_coeff,origin_count_zero]
  rfl
@[simp] theorem J_constant : PowerSeries.constantCoeff J=0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact J_coeff_other 0 (by decide)
@[simp] theorem J_linear : PowerSeries.coeff 1 J=1 := by
  rw [J_coeff,adjacent_count_one]; rfl

#print axioms L_coeff
#print axioms J_coeff
#print axioms L_coeff_other
#print axioms J_coeff_other
#print axioms L_constant
#print axioms J_constant
#print axioms J_linear
end Kreweras
```

### `KrewerasCubicDifferential.lean`

```lean
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Kreweras
open PowerSeries

@[simp] theorem derivative_ofNat {n : ℕ} [Nat.AtLeastTwo n] :
    derivative (ofNat(n) : PowerSeries ℚ)=0 := derivative_C

/-- The generic cubic used in the coefficient extraction; no walk assertion. -/
def Cubic (f : PowerSeries ℚ) : Prop := f = 1 + 4 * X * f^3

theorem cubic_constant {f : PowerSeries ℚ} (h : Cubic f) :
    constantCoeff f = 1 := by
  have hh := congrArg (constantCoeff (R := ℚ)) h
  simpa using hh

theorem cubic_first_derivative {f : PowerSeries ℚ} (h : Cubic f) :
    (1-12*X*f^2)*derivative f = 4*f^3 := by
  change f = 1+4*X*f^3 at h
  have hh := congrArg (fun g : PowerSeries ℚ => derivative g) h
  simp [Derivation.leibniz, smul_eq_mul] at hh
  linear_combination hh

theorem cubic_second_derivative {f : PowerSeries ℚ} (h : Cubic f) :
    (1-12*X*f^2)*derivative (derivative f) =
      24*f^2*derivative f+24*X*f*(derivative f)^2 := by
  have hh := congrArg (fun g : PowerSeries ℚ => derivative g)
    (cubic_first_derivative h)
  simp [Derivation.leibniz, smul_eq_mul] at hh
  linear_combination hh

theorem cubic_origin_ode {f : PowerSeries ℚ} (h : Cubic f) :
    (2*X-54*X^2)*derivative (derivative f) +
      (3-108*X)*derivative f-12*f = 0 := by
  let q : PowerSeries ℚ := 1-12*X*f^2
  have hq : q ≠ 0 := by
    intro hh
    have hc := congrArg (constantCoeff (R := ℚ)) hh
    norm_num [q] at hc
  have hd : q*derivative f=4*f^3 := cubic_first_derivative h
  have hdd : q*derivative (derivative f) =
      24*f^2*derivative f+24*X*f*(derivative f)^2 := cubic_second_derivative h
  have hdd3 : q^3*derivative (derivative f) =
      24*f^2*(4*f^3)*q+24*X*f*(4*f^3)^2 := by
    calc
      _ = q^2*(24*f^2*derivative f+24*X*f*(derivative f)^2) := by rw [← hdd]; ring
      _ = 24*f^2*(q*derivative f)*q+24*X*f*(q*derivative f)^2 := by ring
      _ = _ := by rw [hd]
  have hc : 4*X*f^3-f+1=0 := by
    change f = 1+4*X*f^3 at h
    linear_combination -h
  apply (mul_left_cancel₀ (pow_ne_zero 3 hq))
  calc
    q^3*((2*X-54*X^2)*derivative (derivative f) +
        (3-108*X)*derivative f-12*f) =
      (-12*f-12*f^2+48*X*f^4)*(4*X*f^3-f+1) := by
        dsimp [q] at hd hdd3 ⊢
        linear_combination (2*X-54*X^2)*hdd3 +
          (3-108*X)*(1-12*X*f^2)^2*hd
    _ = q^3*0 := by rw [hc]; ring

theorem cubic_square_ode {f : PowerSeries ℚ} (h : Cubic f) :
    (2*X^2-54*X^3)*derivative (derivative (f^2)) +
      (5*X-162*X^2)*derivative (f^2)+(1-48*X)*f^2-1=0 := by
  let q : PowerSeries ℚ := 1-12*X*f^2
  have hq : q ≠ 0 := by
    intro hh
    have hc := congrArg (constantCoeff (R := ℚ)) hh
    norm_num [q] at hc
  have hd : q*derivative f=4*f^3 := cubic_first_derivative h
  have hdd : q*derivative (derivative f) =
      24*f^2*derivative f+24*X*f*(derivative f)^2 := cubic_second_derivative h
  have hdd3 : q^3*derivative (derivative f) =
      24*f^2*(4*f^3)*q+24*X*f*(4*f^3)^2 := by
    calc
      _ = q^2*(24*f^2*derivative f+24*X*f*(derivative f)^2) := by rw [← hdd]; ring
      _ = 24*f^2*(q*derivative f)*q+24*X*f*(q*derivative f)^2 := by ring
      _ = _ := by rw [hd]
  have hd2 : q^2*(derivative f)^2=(4*f^3)^2 := by
    calc _ = (q*derivative f)^2 := by ring
         _ = _ := by rw [hd]
  have dsq : derivative (f^2)=2*f*derivative f := by
    simpa using derivative_pow f 2
  have ddsq : derivative (derivative (f^2)) =
      2*(derivative f)^2+2*f*derivative (derivative f) := by
    rw [dsq]
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hc : 4*X*f^3-f+1=0 := by
    change f = 1+4*X*f^3 at h
    linear_combination -h
  apply (mul_left_cancel₀ (pow_ne_zero 3 hq))
  calc
    q^3*((2*X^2-54*X^3)*derivative (derivative (f^2)) +
        (5*X-162*X^2)*derivative (f^2)+(1-48*X)*f^2-1) =
      (-1-f-12*X*f^2-8*X*f^3+48*X^2*f^5)*(4*X*f^3-f+1) := by
        rw [ddsq,dsq]
        dsimp [q] at hd hd2 hdd3 ⊢
        linear_combination (2*X^2-54*X^3)*2*f*hdd3 +
          (2*X^2-54*X^3)*2*(1-12*X*f^2)*hd2 +
          (5*X-162*X^2)*2*f*(1-12*X*f^2)^2*hd
    _ = q^3*0 := by rw [hc]; ring

#print axioms cubic_constant
#print axioms cubic_first_derivative
#print axioms cubic_second_derivative
#print axioms cubic_origin_ode
#print axioms cubic_square_ode
end Kreweras
```

### `KrewerasCubicCoefficients.lean`

```lean
import KrewerasCubicDifferential
import Mathlib.Tactic.NormNum

namespace Kreweras
open PowerSeries

/-- An affine polynomial in the Euler derivation X D. -/
noncomputable def eulerLinear (a b : ℕ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  (a : PowerSeries ℚ)*(X*derivative f)+(b : PowerSeries ℚ)*f

theorem coeff_eulerLinear (a b n : ℕ) (f : PowerSeries ℚ) :
    coeff n (eulerLinear a b f) = ((a*n+b : ℕ) : ℚ)*coeff n f := by
  cases n with
  | zero => simp [eulerLinear, coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    simp only [eulerLinear, map_add, coeff_natCast_mul, coeff_succ_X_mul,
      coeff_derivative, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring

theorem cubic_origin_euler {f : PowerSeries ℚ} (h : Cubic f) :
    eulerLinear 2 1 (eulerLinear 1 0 f) =
      6*X*eulerLinear 3 1 (eulerLinear 3 2 f) := by
  have hh := cubic_origin_ode h
  simp [eulerLinear, Derivation.leibniz, smul_eq_mul]
  linear_combination X*hh

theorem cubic_square_euler {f : PowerSeries ℚ} (h : Cubic f) :
    eulerLinear 2 1 (eulerLinear 1 1 (f^2))-1 =
      6*X*eulerLinear 3 2 (eulerLinear 3 4 (f^2)) := by
  have hh := cubic_square_ode h
  generalize f^2=g at hh ⊢
  simp only [eulerLinear]
  simp [Derivation.leibniz, smul_eq_mul]
  linear_combination hh

/-- Coefficient extraction from the proved differential identity. -/
theorem cubic_origin_recurrence {f : PowerSeries ℚ} (h : Cubic f) (m : ℕ) :
    (((m+1)*(2*m+3) : ℕ) : ℚ)*coeff (m+1) f =
      ((6*(3*m+1)*(3*m+2) : ℕ) : ℚ)*coeff m f := by
  have hh := congrArg (coeff (m+1)) (cubic_origin_euler h)
  have hm : 2*(m+1)+1=2*m+3 := by omega
  simp only [coeff_eulerLinear, mul_assoc, coeff_ofNat_mul, coeff_succ_X_mul,
    Nat.one_mul, Nat.add_zero, hm] at hh
  push_cast at hh ⊢
  linear_combination hh

theorem cubic_square_recurrence {f : PowerSeries ℚ} (h : Cubic f) (m : ℕ) :
    (((m+2)*(2*m+3) : ℕ) : ℚ)*coeff (m+1) (f^2) =
      ((6*(3*m+2)*(3*m+4) : ℕ) : ℚ)*coeff m (f^2) := by
  have hh := congrArg (coeff (m+1)) (cubic_square_euler h)
  have hm : 2*(m+1)+1=2*m+3 := by omega
  have hm' : 1*(m+1)+1=m+2 := by omega
  simp only [map_sub, coeff_one, Nat.add_one_ne_zero, ite_false, sub_zero,
    mul_assoc, coeff_ofNat_mul, coeff_succ_X_mul, coeff_eulerLinear, hm,hm'] at hh
  push_cast at hh ⊢
  linear_combination hh

#print axioms coeff_eulerLinear
#print axioms cubic_origin_euler
#print axioms cubic_square_euler
#print axioms cubic_origin_recurrence
#print axioms cubic_square_recurrence
end Kreweras
```

### `KrewerasTernarySeries.lean`

```lean
import KrewerasCubicCoefficients
import KrewerasProductRecurrences

namespace Kreweras
open PowerSeries

/-- Recursive coefficients, specified without the factorial evaluation. -/
noncomputable def ternaryCoeff (n : ℕ) : ℚ :=
  if _hn : n=0 then 1 else
    4*coeff (n-1) ((mk fun i => if _hi : i<n then ternaryCoeff i else 0)^3)
termination_by n

theorem ternaryCoeff_zero : ternaryCoeff 0=1 := by
  rw [ternaryCoeff]; simp

theorem ternaryCoeff_succ (n : ℕ) :
    ternaryCoeff (n+1) =
      4*coeff n ((mk fun i => if i<n+1 then ternaryCoeff i else 0)^3) := by
  rw [ternaryCoeff]; simp

noncomputable def Ternary : PowerSeries ℚ := mk ternaryCoeff

theorem coeff_pow_congr_upto (f g : PowerSeries ℚ) (k n : ℕ)
    (h : ∀ i, i≤n → coeff i f=coeff i g) :
    coeff n (f^k)=coeff n (g^k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ,pow_succ,coeff_mul,coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hsum := Finset.mem_antidiagonal.mp hp
    rw [ih p.1 (fun i hi => h i (by omega)),h p.2 (by omega)]

theorem ternary_cubic : Cubic Ternary := by
  change Ternary=1+4*X*Ternary^3
  ext n
  cases n with
  | zero =>
    simp [Ternary,coeff_zero_eq_constantCoeff_apply,ternaryCoeff_zero]
  | succ n =>
    simp only [Ternary,coeff_mk,ternaryCoeff_succ,map_add,
      coeff_one,Nat.add_one_ne_zero,ite_false,zero_add,mul_assoc,
      coeff_ofNat_mul,coeff_succ_X_mul]
    congr 1
    apply coeff_pow_congr_upto
    intro i hi
    simp [coeff_mk,hi]

/-- The closed coefficient formula, derived from the cubic, not postulated. -/
theorem ternary_coeff (m : ℕ) : coeff m Ternary=evenProduct m := by
  induction m with
  | zero => simp [Ternary,ternaryCoeff_zero]
  | succ m ih =>
    have hc : (((m+1)*(2*m+3) : ℕ) : ℚ) ≠ 0 := by positivity
    have hh := cubic_origin_recurrence ternary_cubic m
    rw [ih] at hh
    exact mul_left_cancel₀ hc (hh.trans (evenProduct_recurrence m).symm)

theorem ternary_square_coeff (m : ℕ) : 2*coeff m (Ternary^2)=oddProduct m := by
  induction m with
  | zero =>
    have h0 : coeff 0 (Ternary^2)=1 := by
      simp [coeff_zero_eq_constantCoeff_apply,cubic_constant ternary_cubic]
    rw [h0,oddProduct_zero]; norm_num
  | succ m ih =>
    have hc : (((m+2)*(2*m+3) : ℕ) : ℚ) ≠ 0 := by positivity
    have hh := cubic_square_recurrence ternary_cubic m
    apply mul_left_cancel₀ hc
    calc
      _ = ((6*(3*m+2)*(3*m+4) : ℕ) : ℚ)*(2*coeff m (Ternary^2)) := by
        linear_combination 2*hh
      _ = _ := by rw [ih,oddProduct_recurrence]

theorem cubic_unique {f g : PowerSeries ℚ} (hf : Cubic f) (hg : Cubic g) : f=g := by
  ext m
  induction m with
  | zero =>
    simp [coeff_zero_eq_constantCoeff_apply,cubic_constant hf,cubic_constant hg]
  | succ m ih =>
    have hc : (((m+1)*(2*m+3) : ℕ) : ℚ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hc
    rw [cubic_origin_recurrence hf,cubic_origin_recurrence hg,ih]

theorem evenProduct_ternary_convolution (m : ℕ) :
    evenProduct (m+1) = 4*∑ p ∈ Finset.antidiagonal m,
      (∑ q ∈ Finset.antidiagonal p.1, evenProduct q.1*evenProduct q.2)*
        evenProduct p.2 := by
  have hh := congrArg (coeff (m+1)) ternary_cubic
  simp only [map_add,coeff_one,Nat.add_one_ne_zero,ite_false,zero_add,
    mul_assoc,coeff_ofNat_mul,coeff_succ_X_mul] at hh
  rw [pow_succ,pow_two,coeff_mul] at hh
  simpa only [coeff_mul,ternary_coeff] using hh

theorem oddProduct_square_convolution (m : ℕ) :
    oddProduct m = 2*∑ p ∈ Finset.antidiagonal m,
      evenProduct p.1*evenProduct p.2 := by
  rw [← ternary_square_coeff,pow_two,coeff_mul]
  simp only [ternary_coeff]

#print axioms ternaryCoeff_zero
#print axioms ternaryCoeff_succ
#print axioms coeff_pow_congr_upto
#print axioms ternary_cubic
#print axioms ternary_coeff
#print axioms ternary_square_coeff
#print axioms cubic_unique
#print axioms evenProduct_ternary_convolution
#print axioms oddProduct_square_convolution
end Kreweras
```

### `KrewerasSeriesReduction.lean`

```lean
import KrewerasTernarySeries
import KrewerasEndpointSeries
import KrewerasRecurrenceReduction

namespace Kreweras
open PowerSeries

/-- Actual origin counts, with the proved residue class compressed. -/
noncomputable def U : PowerSeries ℚ := mk fun m => (originCount (3*m) : ℚ)
/-- Actual adjacent counts, with the proved residue class compressed. -/
noncomputable def V : PowerSeries ℚ := mk fun m => (adjacentCount (3*m+1) : ℚ)

@[simp] theorem U_coeff (m : ℕ) : coeff m U=(originCount (3*m) : ℚ) := coeff_mk _ _
@[simp] theorem V_coeff (m : ℕ) : coeff m V=(adjacentCount (3*m+1) : ℚ) := coeff_mk _ _

/-- Exact missing geometric identities, not a proved hypothesis. -/
def WalkSeriesEquations : Prop := Cubic U ∧ V=U^2

theorem walk_recurrences_of_series_equations (h : WalkSeriesEquations) :
    WalkRecurrences := by
  constructor
  · intro m
    simpa using cubic_origin_recurrence h.1 m
  · intro m
    have hh := cubic_square_recurrence h.1 m
    rw [← h.2,V_coeff,V_coeff] at hh
    linear_combination 2*hh

theorem literal_of_series_equations (h : WalkSeriesEquations) : LiteralEndpoint :=
  literal_iff_walk_recurrences.mpr (walk_recurrences_of_series_equations h)

theorem walk_series_identification_of_enumeration (h : WalkEnumeration) :
    U=Ternary ∧ V=Ternary^2 := by
  constructor
  · ext m
    rw [U_coeff,ternary_coeff,h.1]
  · ext m
    apply mul_left_cancel₀ (show (2 : ℚ)≠0 by norm_num)
    rw [V_coeff,ternary_square_coeff,h.2]

theorem series_equations_of_walk_enumeration (h : WalkEnumeration) :
    WalkSeriesEquations := by
  obtain ⟨hu,hv⟩ := walk_series_identification_of_enumeration h
  exact ⟨hu ▸ ternary_cubic,by rw [hu,hv]⟩

theorem literal_iff_walk_series_equations :
    LiteralEndpoint ↔ WalkSeriesEquations :=
  ⟨fun h => series_equations_of_walk_enumeration
    (walk_enumeration_of_literal h),literal_of_series_equations⟩

theorem walk_enumeration_iff_series_identification :
    WalkEnumeration ↔ U=Ternary ∧ V=Ternary^2 := by
  constructor
  · exact walk_series_identification_of_enumeration
  · rintro ⟨hu,hv⟩
    constructor
    · intro m
      rw [← U_coeff,hu,ternary_coeff]
    · intro m
      rw [← V_coeff,hv,ternary_square_coeff]

#print axioms U_coeff
#print axioms V_coeff
#print axioms walk_recurrences_of_series_equations
#print axioms literal_of_series_equations
#print axioms walk_series_identification_of_enumeration
#print axioms series_equations_of_walk_enumeration
#print axioms literal_iff_walk_series_equations
#print axioms walk_enumeration_iff_series_identification
end Kreweras
```

### `KrewerasKernelFactor.lean`

```lean
import KrewerasTernarySeries
import Mathlib.RingTheory.PowerSeries.Expand

namespace Kreweras
open PowerSeries

/-- The cubic solution in the original time variable. -/
noncomputable def T : PowerSeries ℚ := expand 3 (by decide) Ternary

theorem T_cubic : T=1+4*X^3*T^3 := by
  have hh := congrArg (expand 3 (by decide) (R := ℚ)) ternary_cubic
  simpa only [map_add,map_mul,map_one,map_ofNat,map_pow,expand_X,T] using hh

theorem T_coeff (m : ℕ) : coeff (3*m) T=evenProduct m := by
  rw [T,coeff_expand_mul,ternary_coeff]

theorem T_square_coeff (m : ℕ) : 2*coeff (3*m) (T^2)=oddProduct m := by
  rw [T,← map_pow,coeff_expand_mul,ternary_square_coeff]

theorem T_coeff_other (d : ℕ) (h : d%3≠0) : coeff d T=0 := by
  apply coeff_expand_of_not_dvd
  exact fun hh => h (Nat.mod_eq_zero_of_dvd hh)

/-- An explicit kernel factorization requiring no logarithm/exponential calculus.
Here z*w=1 encodes the Laurent variable and its inverse. -/
theorem slit_kernel_factor {R : Type*} [CommRing R] (t z w f : R)
    (hz : z*w=1) (hf : f=1+4*t^3*f^3) :
    f^2*((1-t*z)^2-4*t^2*w) =
      (1-4*t^2*f^2*w)*(1+(-2*t*f^2+4*t^4*f^4)*z+t^2*f^2*z^2) := by
  have hh : f-4*t^3*f^3=1 := by linear_combination hf
  have hs : (f-4*t^3*f^3)^2=1 := by rw [hh]; ring
  linear_combination hs +
    (-8*t^3*f^4+16*t^6*f^6+4*t^4*f^4*z)*hz

#print axioms T_cubic
#print axioms T_coeff
#print axioms T_square_coeff
#print axioms T_coeff_other
#print axioms slit_kernel_factor
end Kreweras
```

### `KrewerasTimeExpansion.lean`

```lean
import KrewerasSeriesReduction
import KrewerasKernelFactor

namespace Kreweras
open PowerSeries

theorem L_expand_U : L=expand 3 (by decide) U := by
  ext d
  by_cases hd : d%3=0
  · obtain ⟨m,rfl⟩ := Nat.dvd_of_mod_eq_zero hd
    rw [coeff_expand_mul,L_coeff,U_coeff]
  · rw [L_coeff_other d hd,coeff_expand_of_not_dvd]
    exact fun hh => hd (Nat.mod_eq_zero_of_dvd hh)

theorem J_expand_V : J=X*expand 3 (by decide) V := by
  ext d
  cases d with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ d =>
    rw [coeff_succ_X_mul]
    by_cases hd : d%3=0
    · obtain ⟨m,rfl⟩ := Nat.dvd_of_mod_eq_zero hd
      rw [coeff_expand_mul,J_coeff,V_coeff]
    · rw [J_coeff_other (d+1) (by omega),coeff_expand_of_not_dvd]
      exact fun hh => hd (Nat.mod_eq_zero_of_dvd hh)

theorem literal_iff_original_series :
    LiteralEndpoint ↔ L=T ∧ J=X*T^2 := by
  constructor
  · intro h
    obtain ⟨hu,hv⟩ := walk_series_identification_of_enumeration
      (walk_enumeration_of_literal h)
    constructor
    · rw [L_expand_U,hu]; rfl
    · rw [J_expand_V,hv,map_pow]; rfl
  · rintro ⟨hl,hj⟩
    apply literal_of_walk_enumeration
    constructor
    · intro m
      rw [← L_coeff,hl,T_coeff]
    · intro m
      rw [← J_coeff,hj,coeff_succ_X_mul,T_square_coeff]

#print axioms L_expand_U
#print axioms J_expand_V
#print axioms literal_iff_original_series
end Kreweras
```

### `KrewerasWalkRecursion.lean`

```lean
import KrewerasEndpointSeries
import Mathlib.Data.Fin.Tuple.Basic

namespace Kreweras

abbrev EndpointWalk (d : ℕ) (q : ℤ × ℤ) :=
  {p : SlitWalk d // p.val (Fin.last d) = q}

noncomputable def endpointCount (d : ℕ) (q : ℤ × ℤ) : ℕ :=
  Fintype.card (EndpointWalk d q)

def stepPred (q : ℤ × ℤ) (s : Fin 3) : ℤ × ℤ :=
  if s = 0 then (q.1-1,q.2-1) else
  if s = 1 then (q.1+1,q.2) else (q.1,q.2+1)

theorem stepPred_step (q : ℤ × ℤ) (s : Fin 3) :
    PlaneStep (stepPred q s) q := by
  fin_cases s <;> simp [stepPred, PlaneStep]

theorem stepPred_injective (q : ℤ × ℤ) : Function.Injective (stepPred q) := by
  intro s t h
  fin_cases s <;> fin_cases t <;> simp [stepPred, Prod.mk.injEq] at h ⊢ <;> omega

theorem stepPred_exists {p q : ℤ × ℤ} (h : PlaneStep p q) :
    ∃ s : Fin 3, stepPred q s = p := by
  rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact ⟨0, by simp [stepPred, Prod.ext_iff]; omega⟩
  · exact ⟨1, by simp [stepPred, Prod.ext_iff]; omega⟩
  · exact ⟨2, by simp [stepPred, Prod.ext_iff]; omega⟩

def dropLastWalk {d : ℕ} (p : SlitWalk (d+1)) : SlitWalk d :=
  ⟨fun i => p.val i.castSucc, by
    refine ⟨p.property.1, fun i => p.property.2.1 i.castSucc, ?_⟩
    intro i
    exact p.property.2.2 i.castSucc⟩

def snocWalk {d : ℕ} (p : SlitWalk d) (q : ℤ × ℤ)
    (hq : Slit q) (hs : PlaneStep (p.val (Fin.last d)) q) : SlitWalk (d+1) :=
  ⟨Fin.snoc p.val q, by
    refine ⟨?_, ?_, ?_⟩
    · simpa using p.property.1
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hq
      · simpa using p.property.2.1 j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hs
      · have hi : (j.castSucc.succ : Fin (d+2)) = j.succ.castSucc := rfl
        simpa only [hi, Fin.snoc_castSucc] using p.property.2.2 j⟩

@[simp] theorem snocWalk_last {d : ℕ} (p : SlitWalk d) (q : ℤ × ℤ)
    (hq : Slit q) (hs : PlaneStep (p.val (Fin.last d)) q) :
    (snocWalk p q hq hs).val (Fin.last (d+1)) = q := by
  simp [snocWalk]

@[simp] theorem dropLast_snocWalk {d : ℕ} (p : SlitWalk d) (q : ℤ × ℤ)
    (hq : Slit q) (hs : PlaneStep (p.val (Fin.last d)) q) :
    dropLastWalk (snocWalk p q hq hs) = p := by
  apply Subtype.ext
  funext i
  simp [dropLastWalk, snocWalk]

theorem snoc_dropLastWalk {d : ℕ} (p : SlitWalk (d+1)) :
    snocWalk (dropLastWalk p) (p.val (Fin.last (d+1)))
      (p.property.2.1 _) (p.property.2.2 (Fin.last d)) = p := by
  apply Subtype.ext
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [snocWalk, dropLastWalk]

def endpointSnoc {d : ℕ} {q : ℤ × ℤ} (hq : Slit q)
    (p : (s : Fin 3) × EndpointWalk d (stepPred q s)) : EndpointWalk (d+1) q :=
  ⟨snocWalk p.2.val q hq (by rw [p.2.property]; exact stepPred_step q p.1),
    snocWalk_last _ _ _ _⟩

theorem endpointSnoc_bijective (d : ℕ) (q : ℤ × ℤ) (hq : Slit q) :
    Function.Bijective (@endpointSnoc d q hq) := by
  constructor
  · rintro ⟨s,p⟩ ⟨t,r⟩ h
    have he : p.val = r.val := by
      simpa only [endpointSnoc, dropLast_snocWalk] using congrArg dropLastWalk (congrArg Subtype.val h)
    have hs : s=t := stepPred_injective q
      (p.property.symm.trans ((congrArg (fun w : SlitWalk d => w.val (Fin.last d)) he).trans r.property))
    subst t
    congr 1
    exact Subtype.ext he
  · intro p
    let r := dropLastWalk p.val
    have hs : PlaneStep (r.val (Fin.last d)) q := by
      rw [← p.property]
      exact p.val.property.2.2 (Fin.last d)
    obtain ⟨s,he⟩ := stepPred_exists hs
    refine ⟨⟨s,⟨r,he.symm⟩⟩,?_⟩
    apply Subtype.ext
    change snocWalk r q hq hs = p.val
    simpa only [← p.property] using snoc_dropLastWalk p.val

noncomputable def endpointLastStepEquiv (d : ℕ) (q : ℤ × ℤ) (hq : Slit q) :
    ((s : Fin 3) × EndpointWalk d (stepPred q s)) ≃ EndpointWalk (d+1) q :=
  Equiv.ofBijective (endpointSnoc hq) (endpointSnoc_bijective d q hq)

theorem endpointCount_forbidden (d : ℕ) (q : ℤ × ℤ) (hq : ¬ Slit q) :
    endpointCount d q = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun p => hq (p.property ▸ p.val.property.2.1 (Fin.last d))⟩

open scoped Classical in
theorem endpointCount_succ (d : ℕ) (u v : ℤ) :
    endpointCount (d+1) (u,v) =
      if Slit (u,v) then
        endpointCount d (u-1,v-1) + endpointCount d (u+1,v) +
          endpointCount d (u,v+1)
      else 0 := by
  classical
  by_cases h : Slit (u,v)
  · rw [ite_eq_left h]
    unfold endpointCount
    rw [← Fintype.card_congr (endpointLastStepEquiv d (u,v) h), Fintype.card_sigma]
    simp [Fin.sum_univ_succ, stepPred, add_assoc]
  · rw [ite_eq_right h]
    exact endpointCount_forbidden (d+1) (u,v) h

open scoped Classical in
theorem endpointCount_zero (q : ℤ × ℤ) :
    endpointCount 0 q = if q=(0,0) then 1 else 0 := by
  classical
  by_cases h : q=(0,0)
  · subst q
    rw [ite_eq_left rfl]
    change Fintype.card (EndpointWalk 0 (0,0))=1
    apply Fintype.card_eq_one_iff.mpr
    let p : SlitWalk 0 := ⟨fun _ => (0,0), by
      refine ⟨rfl, fun _ => ?_, fun i => Fin.elim0 i⟩
      simp [Slit]⟩
    refine ⟨⟨p,rfl⟩,fun y => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have hi : i=0 := by apply Fin.ext; omega
    rw [hi]
    exact y.val.property.1
  · rw [ite_eq_right h]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun p => h ?_⟩
    exact p.property.symm.trans p.val.property.1

/-- Rational coefficient array in the line-height coordinates. -/
noncomputable def shearedCount (d : ℕ) (h r : ℤ) : ℚ :=
  endpointCount d (h+r,r)

open scoped Classical in
/-- The full slit-plane recurrence, with no enumeration assumption. -/
def SlitRecurrence (a : ℕ → ℤ → ℤ → ℚ) : Prop :=
  (∀ h r, a 0 h r = if h=0 ∧ r=0 then 1 else 0) ∧
  ∀ d h r, a (d+1) h r =
    if h=0 ∧ r<0 then 0 else
      a d h (r-1) + a d (h+1) r + a d (h-1) (r+1)

theorem shearedCount_recurrence : SlitRecurrence shearedCount := by
  classical
  constructor
  · intro h r
    simp only [shearedCount, endpointCount_zero]
    have hc : ((h+r,r)=(0,0)) ↔ h=0 ∧ r=0 := by
      simp only [Prod.mk.injEq]
      omega
    simp only [hc]
    split_ifs <;> rfl
  · intro d h r
    rw [shearedCount, endpointCount_succ]
    simp only [Nat.cast_ite, Nat.cast_zero, Nat.cast_add, shearedCount]
    have hs : Slit (h+r,r) ↔ ¬(h=0 ∧ r<0) := by
      simp only [Slit]; omega
    by_cases hh : h=0 ∧ r<0
    · rw [ite_eq_left hh, ite_eq_right (fun hsl => (hs.mp hsl) hh)]
    · rw [ite_eq_right hh, ite_eq_left (hs.mpr hh)]
      have h₁ : (h+(r-1),r-1)=(h+r-1,r-1) := by ext <;> omega
      have h₂ : (h+1+r,r)=(h+r+1,r) := by ext <;> omega
      have h₃ : (h-1+(r+1),r+1)=(h+r,r+1) := by ext <;> omega
      rw [h₁,h₂,h₃]

theorem slitRecurrence_unique {a b : ℕ → ℤ → ℤ → ℚ}
    (ha : SlitRecurrence a) (hb : SlitRecurrence b) : a=b := by
  funext d
  induction d with
  | zero => funext h r; rw [ha.1, hb.1]
  | succ d ih =>
    funext h r
    rw [ha.2, hb.2]
    exact congrArg (fun c : ℤ → ℤ → ℚ =>
      if h=0 ∧ r<0 then 0 else c h (r-1)+c (h+1) r+c (h-1) (r+1)) ih

theorem solution_eq_shearedCount {a : ℕ → ℤ → ℤ → ℚ}
    (ha : SlitRecurrence a) : a=shearedCount :=
  slitRecurrence_unique ha shearedCount_recurrence

theorem L_of_slitRecurrence {a : ℕ → ℤ → ℤ → ℚ}
    (ha : SlitRecurrence a) : L=PowerSeries.mk (fun d => a d 0 0) := by
  rw [solution_eq_shearedCount ha]
  apply PowerSeries.ext
  intro d
  simp only [L_coeff, PowerSeries.coeff_mk, shearedCount, zero_add]
  rfl

theorem J_of_slitRecurrence {a : ℕ → ℤ → ℤ → ℚ}
    (ha : SlitRecurrence a) : J=PowerSeries.mk (fun d => a d (-1) 0) := by
  rw [solution_eq_shearedCount ha]
  apply PowerSeries.ext
  intro d
  simp only [J_coeff, PowerSeries.coeff_mk, shearedCount, add_zero]
  rfl

#print axioms endpointLastStepEquiv
#print axioms endpointCount_zero
#print axioms endpointCount_succ
#print axioms shearedCount_recurrence
#print axioms slitRecurrence_unique
#print axioms L_of_slitRecurrence
#print axioms J_of_slitRecurrence
end Kreweras
```

### `KrewerasSquareRoots.lean`

```lean
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace Kreweras
open PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The t-adic square root with constant term one. -/
noncomputable def formalSqrt (p : PowerSeries R) : PowerSeries R :=
  subst p (binomialSeries R (1/2 : ℚ))

theorem formalSqrt_constant {p : PowerSeries R} (hp : constantCoeff p=0) :
    constantCoeff (formalSqrt p)=1 := by
  rw [formalSqrt]
  exact (constantCoeff_subst_of_constantCoeff_zero hp _).trans (by simp)

theorem formalSqrt_sq {p : PowerSeries R} (hp : constantCoeff p=0) :
    (formalSqrt p)^2=1+p := by
  have hs : HasSubst p := HasSubst.of_constantCoeff_zero' hp
  have h : (binomialSeries R (1/2 : ℚ))^2=1+X := by
    rw [pow_two, ← binomialSeries_add]
    convert (binomialSeries_nat (R := ℚ) (A := R) 1) using 1 <;> norm_num
  have hh := congrArg (substAlgHom (R := R) hs) h
  simpa only [formalSqrt, map_pow, map_add, map_one, substAlgHom_X, coe_substAlgHom] using hh

theorem square_root_unique {f g : PowerSeries R}
    (hf : constantCoeff f=1) (hg : constantCoeff g=1) (h : f^2=g^2) :
    f=g := by
  have hu : IsUnit (f+g) := isUnit_iff_constantCoeff.mpr (by
    rw [map_add,hf,hg]
    have htwo : IsUnit (2 : R) :=
      by simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
    simpa only [one_add_one_eq_two] using htwo)
  have hp : (f+g)*(f-g)=0 := by linear_combination h
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hp)

omit [Algebra ℚ R] in
theorem constantCoeff_map_apply {S : Type*} [CommRing S]
    (f : R →+* S) (p : PowerSeries R) :
    constantCoeff (PowerSeries.map f p)=f (constantCoeff p) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]

theorem map_formalSqrt {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →+* S) {p : PowerSeries R} (hp : constantCoeff p=0) :
    PowerSeries.map f (formalSqrt p)=formalSqrt (PowerSeries.map f p) := by
  have hmp : constantCoeff (PowerSeries.map f p)=0 := by rw [constantCoeff_map_apply, hp, map_zero]
  apply square_root_unique
  · rw [constantCoeff_map_apply, formalSqrt_constant hp, map_one]
  · exact formalSqrt_constant hmp
  · rw [← map_pow, formalSqrt_sq hp, formalSqrt_sq hmp]
    simp

noncomputable def formalInvSqrt (p : PowerSeries R) : PowerSeries R :=
  subst p (binomialSeries R (-1/2 : ℚ))

theorem formalInvSqrt_constant {p : PowerSeries R} (hp : constantCoeff p=0) :
    constantCoeff (formalInvSqrt p)=1 := by
  rw [formalInvSqrt]
  exact (constantCoeff_subst_of_constantCoeff_zero hp _).trans (by simp)

theorem formalInvSqrt_mul {p : PowerSeries R} (hp : constantCoeff p=0) :
    formalInvSqrt p*formalSqrt p=1 := by
  have hs : HasSubst p := HasSubst.of_constantCoeff_zero' hp
  have h : binomialSeries R (-1/2 : ℚ)*binomialSeries R (1/2 : ℚ)=1 := by
    rw [← binomialSeries_add]
    norm_num
  have hh := congrArg (substAlgHom (R := R) hs) h
  simpa only [formalInvSqrt,formalSqrt,map_mul,map_one,coe_substAlgHom] using hh

theorem formalSqrt_zero : formalSqrt (0 : PowerSeries R)=1 := by
  apply square_root_unique (formalSqrt_constant rfl) (by simp)
  rw [formalSqrt_sq rfl]
  simp

theorem formalInvSqrt_zero : formalInvSqrt (0 : PowerSeries R)=1 := by
  have h := formalInvSqrt_mul (R := R) (p := 0) rfl
  simpa only [formalSqrt_zero,mul_one] using h

theorem map_formalInvSqrt {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →+* S) {p : PowerSeries R} (hp : constantCoeff p=0) :
    PowerSeries.map f (formalInvSqrt p)=formalInvSqrt (PowerSeries.map f p) := by
  have hmp : constantCoeff (PowerSeries.map f p)=0 := by
    rw [constantCoeff_map_apply,hp,map_zero]
  have ha : PowerSeries.map f (formalInvSqrt p)*formalSqrt (PowerSeries.map f p)=1 := by
    rw [← map_formalSqrt f hp,← map_mul,formalInvSqrt_mul hp,map_one]
  have hb : formalSqrt (PowerSeries.map f p)*formalInvSqrt (PowerSeries.map f p)=1 := by
    rw [mul_comm,formalInvSqrt_mul hmp]
  calc
    _ = PowerSeries.map f (formalInvSqrt p)*
        (formalSqrt (PowerSeries.map f p)*formalInvSqrt (PowerSeries.map f p)) := by
      rw [hb,mul_one]
    _ = _ := by rw [← mul_assoc,ha,one_mul]

#print axioms formalSqrt_constant
#print axioms map_formalSqrt
#print axioms formalInvSqrt_constant
#print axioms formalInvSqrt_mul
#print axioms map_formalInvSqrt
#print axioms formalSqrt_sq
#print axioms square_root_unique
end Kreweras
```

### `KrewerasKernelRoots.lean`

```lean
import KrewerasSquareRoots
import KrewerasKernelFactor
import Mathlib.Algebra.Polynomial.Laurent

namespace Kreweras
open PowerSeries

abbrev LaurentTime := PowerSeries (LaurentPolynomial ℚ)
noncomputable def scalarT : LaurentTime := PowerSeries.map LaurentPolynomial.C T
noncomputable def zmark (i : ℤ) : LaurentTime := C (LaurentPolynomial.T i)

@[simp] theorem zmark_add (i j : ℤ) : zmark i*zmark j=zmark (i+j) := by
  simp only [zmark, ← map_mul, ← LaurentPolynomial.T_add]
@[simp] theorem zmark_zero : zmark 0=1 := by simp [zmark]

theorem scalarT_cubic : scalarT=1+4*X^3*scalarT^3 := by
  have h := congrArg (PowerSeries.map (LaurentPolynomial.C (R := ℚ))) T_cubic
  simpa only [map_add, map_one, map_mul, map_pow, map_ofNat, PowerSeries.map_X, scalarT] using h

@[simp] theorem scalarT_constant : constantCoeff scalarT=1 := by
  have h : constantCoeff T=1 := by
    have hc := congrArg constantCoeff T_cubic
    simpa only [map_add,map_one,map_mul,map_pow,constantCoeff_X,zero_pow (by decide : 3≠0),
      mul_zero,zero_mul,add_zero] using hc
  rw [scalarT,constantCoeff_map_apply,h,map_one]

noncomputable def slitKernel : LaurentTime :=
  (1-X*zmark 1)^2-4*X^2*zmark (-1)
noncomputable def positiveKernel : LaurentTime :=
  1+(-2*X*scalarT^2+4*X^4*scalarT^4)*zmark 1+
    X^2*scalarT^2*(zmark 1)^2
noncomputable def negativeKernel : LaurentTime :=
  1-4*X^2*scalarT^2*zmark (-1)

noncomputable def kernelRoot : LaurentTime := formalSqrt (slitKernel-1)
noncomputable def positiveRoot : LaurentTime := formalSqrt (positiveKernel-1)
noncomputable def negativeRoot : LaurentTime := formalSqrt (negativeKernel-1)

@[simp] theorem slitKernel_constant : constantCoeff slitKernel=1 := by
  simp [slitKernel]
@[simp] theorem positiveKernel_constant : constantCoeff positiveKernel=1 := by
  simp [positiveKernel]
@[simp] theorem negativeKernel_constant : constantCoeff negativeKernel=1 := by
  simp [negativeKernel]

theorem kernelRoot_sq : kernelRoot^2=slitKernel := by
  rw [kernelRoot, formalSqrt_sq (by simp)]
  abel
theorem positiveRoot_sq : positiveRoot^2=positiveKernel := by
  rw [positiveRoot, formalSqrt_sq (by simp)]
  abel
theorem negativeRoot_sq : negativeRoot^2=negativeKernel := by
  rw [negativeRoot, formalSqrt_sq (by simp)]
  abel

@[simp] theorem kernelRoot_constant : constantCoeff kernelRoot=1 :=
  formalSqrt_constant (by simp)
@[simp] theorem positiveRoot_constant : constantCoeff positiveRoot=1 :=
  formalSqrt_constant (by simp)
@[simp] theorem negativeRoot_constant : constantCoeff negativeRoot=1 :=
  formalSqrt_constant (by simp)

theorem kernel_root_factorization :
    scalarT*kernelRoot=negativeRoot*positiveRoot := by
  apply square_root_unique (by simp) (by simp)
  rw [mul_pow, mul_pow, kernelRoot_sq, negativeRoot_sq, positiveRoot_sq]
  exact slit_kernel_factor X (zmark 1) (zmark (-1)) scalarT (by simp) scalarT_cubic

#print axioms kernelRoot_sq
#print axioms positiveRoot_sq
#print axioms negativeRoot_sq
#print axioms kernel_root_factorization
end Kreweras
```

### `KrewerasLaurentSupport.lean`

```lean
import KrewerasSquareRoots
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Finsupp.Basic

namespace Kreweras
open PowerSeries

/-- A polynomial embedded into Laurent polynomials has no negative powers. -/
theorem toLaurent_negative (p : Polynomial ℚ) (j : ℤ) (hj : j<0) :
    (p.toLaurent).coeff j=0 := by
  by_contra h
  have hm : j ∈ p.toLaurent.coeff.support := Finsupp.mem_support_iff.mpr h
  rw [LaurentPolynomial.support_coeff_toLaurent] at hm
  obtain ⟨n,_,hn⟩ := Finset.mem_map.mp hm
  change (n : ℤ)=j at hn
  omega

@[simp] theorem toLaurent_coeff_nat (p : Polynomial ℚ) (n : ℕ) :
    p.toLaurent.coeff (n : ℤ)=p.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective (Nat.cast_injective (R := ℤ)) _ n

abbrev PolynomialTime := PowerSeries (Polynomial ℚ)
abbrev LaurentSeries := PowerSeries (LaurentPolynomial ℚ)

noncomputable def positiveEmbed : PolynomialTime →+* LaurentSeries :=
  PowerSeries.map Polynomial.toLaurent

noncomputable def negativeEmbed : PolynomialTime →+* LaurentSeries :=
  PowerSeries.map ((LaurentPolynomial.invert (R := ℚ)).toRingHom.comp Polynomial.toLaurent)

theorem positiveEmbed_support (p : PolynomialTime) (d : ℕ) (j : ℤ) (hj : j<0) :
    (coeff d (positiveEmbed p)).coeff j=0 := by
  exact toLaurent_negative (coeff d p) j hj

theorem negativeEmbed_support (p : PolynomialTime) (d : ℕ) (j : ℤ) (hj : 0<j) :
    (coeff d (negativeEmbed p)).coeff j=0 := by
  change (LaurentPolynomial.invert (coeff d p).toLaurent).coeff j=0
  rw [LaurentPolynomial.invert_apply]
  exact toLaurent_negative (coeff d p) (-j) (by omega)

theorem positiveEmbed_coeff_zero (p : PolynomialTime) (d : ℕ) :
    (coeff d (positiveEmbed p)).coeff 0=(coeff d p).coeff 0 :=
  toLaurent_coeff_nat (coeff d p) 0

theorem negativeEmbed_coeff_zero (p : PolynomialTime) (d : ℕ) :
    (coeff d (negativeEmbed p)).coeff 0=(coeff d p).coeff 0 := by
  change (LaurentPolynomial.invert (coeff d p).toLaurent).coeff 0=_
  rw [LaurentPolynomial.invert_apply, neg_zero]
  exact toLaurent_coeff_nat (coeff d p) 0

/-- Any zero-constant polynomial-time input has a one-sided square root. -/
theorem positiveEmbed_sqrt (p : PolynomialTime) (hp : constantCoeff p=0) :
    positiveEmbed (formalSqrt p)=formalSqrt (positiveEmbed p) :=
  map_formalSqrt (R := Polynomial ℚ) (S := LaurentPolynomial ℚ) (Polynomial.toLaurent (R := ℚ)) hp

theorem negativeEmbed_sqrt (p : PolynomialTime) (hp : constantCoeff p=0) :
    negativeEmbed (formalSqrt p)=formalSqrt (negativeEmbed p) :=
  map_formalSqrt (R := Polynomial ℚ) (S := LaurentPolynomial ℚ)
    ((LaurentPolynomial.invert (R := ℚ)).toRingHom.comp Polynomial.toLaurent) hp

#print axioms toLaurent_negative
#print axioms positiveEmbed_support
#print axioms negativeEmbed_support
#print axioms positiveEmbed_sqrt
#print axioms negativeEmbed_sqrt
end Kreweras
```

### `KrewerasRootSupport.lean`

```lean
import KrewerasKernelRoots
import KrewerasLaurentSupport

namespace Kreweras
open PowerSeries

noncomputable def polyT : PolynomialTime := PowerSeries.map Polynomial.C T
noncomputable def polyZ : PolynomialTime := C Polynomial.X

noncomputable def posInput : PolynomialTime :=
  (-2*X*polyT^2+4*X^4*polyT^4)*polyZ+X^2*polyT^2*polyZ^2
noncomputable def negInput : PolynomialTime := -4*X^2*polyT^2*polyZ

@[simp] theorem posInput_constant : constantCoeff posInput=0 := by simp [posInput]
@[simp] theorem negInput_constant : constantCoeff negInput=0 := by simp [negInput]

theorem positiveEmbed_polyT : positiveEmbed polyT=scalarT := by
  apply PowerSeries.ext
  intro d
  simp only [positiveEmbed,polyT,scalarT,coeff_map,Polynomial.toLaurent_C]

theorem negativeEmbed_polyT : negativeEmbed polyT=scalarT := by
  apply PowerSeries.ext
  intro d
  change (LaurentPolynomial.invert (Polynomial.C (coeff d T)).toLaurent) =
    LaurentPolynomial.C (coeff d T)
  rw [Polynomial.toLaurent_C,LaurentPolynomial.invert_C]

theorem positiveEmbed_polyZ : positiveEmbed polyZ=zmark 1 := by
  simp only [positiveEmbed,polyZ,PowerSeries.map_C,Polynomial.toLaurent_X,zmark]

theorem negativeEmbed_polyZ : negativeEmbed polyZ=zmark (-1) := by
  simp only [negativeEmbed,polyZ,PowerSeries.map_C,RingHom.comp_apply,
    Polynomial.toLaurent_X]
  change C (LaurentPolynomial.invert (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℚ))=_
  rw [LaurentPolynomial.invert_T]
  rfl

theorem positiveEmbed_X : positiveEmbed X=X := PowerSeries.map_X _
theorem negativeEmbed_X : negativeEmbed X=X := PowerSeries.map_X _

theorem positiveEmbed_input : positiveEmbed posInput=positiveKernel-1 := by
  simp only [posInput,map_add,map_mul,map_pow,map_neg,map_ofNat,
    positiveEmbed_X,positiveEmbed_polyT,positiveEmbed_polyZ,positiveKernel]
  ring

theorem negativeEmbed_input : negativeEmbed negInput=negativeKernel-1 := by
  simp only [negInput,map_mul,map_pow,map_neg,map_ofNat,
    negativeEmbed_X,negativeEmbed_polyT,negativeEmbed_polyZ,negativeKernel]
  ring

theorem positiveRoot_polynomial :
    positiveRoot=positiveEmbed (formalSqrt posInput) := by
  rw [positiveEmbed_sqrt _ posInput_constant,positiveEmbed_input]
  rfl

theorem negativeRoot_polynomial :
    negativeRoot=negativeEmbed (formalSqrt negInput) := by
  rw [negativeEmbed_sqrt _ negInput_constant,negativeEmbed_input]
  rfl

theorem positiveRoot_support (d : ℕ) (j : ℤ) (hj : j<0) :
    (coeff d positiveRoot).coeff j=0 := by
  rw [positiveRoot_polynomial]
  exact positiveEmbed_support _ d j hj

theorem negativeRoot_support (d : ℕ) (j : ℤ) (hj : 0<j) :
    (coeff d negativeRoot).coeff j=0 := by
  rw [negativeRoot_polynomial]
  exact negativeEmbed_support _ d j hj

noncomputable def positiveInverse : LaurentSeries := formalInvSqrt (positiveKernel-1)
noncomputable def negativeInverse : LaurentSeries := formalInvSqrt (negativeKernel-1)

theorem positiveInverse_mul : positiveInverse*positiveRoot=1 :=
  formalInvSqrt_mul (by simp)
theorem negativeInverse_mul : negativeInverse*negativeRoot=1 :=
  formalInvSqrt_mul (by simp)

theorem positiveInverse_polynomial :
    positiveInverse=positiveEmbed (formalInvSqrt posInput) := by
  rw [positiveInverse,← positiveEmbed_input]
  exact (map_formalInvSqrt (R := Polynomial ℚ) (S := LaurentPolynomial ℚ)
    (Polynomial.toLaurent (R := ℚ)) posInput_constant).symm

theorem negativeInverse_polynomial :
    negativeInverse=negativeEmbed (formalInvSqrt negInput) := by
  rw [negativeInverse,← negativeEmbed_input]
  exact (map_formalInvSqrt (R := Polynomial ℚ) (S := LaurentPolynomial ℚ)
    ((LaurentPolynomial.invert (R := ℚ)).toRingHom.comp Polynomial.toLaurent)
    negInput_constant).symm

theorem positiveInverse_support (d : ℕ) (j : ℤ) (hj : j<0) :
    (coeff d positiveInverse).coeff j=0 := by
  rw [positiveInverse_polynomial]
  exact positiveEmbed_support _ d j hj

theorem negativeInverse_support (d : ℕ) (j : ℤ) (hj : 0<j) :
    (coeff d negativeInverse).coeff j=0 := by
  rw [negativeInverse_polynomial]
  exact negativeEmbed_support _ d j hj

noncomputable def evalZZero : PolynomialTime →+* PowerSeries ℚ :=
  PowerSeries.map (Polynomial.evalRingHom (0 : ℚ))

theorem evalZZero_polyZ : evalZZero polyZ=0 := by
  simp only [evalZZero,polyZ,PowerSeries.map_C,Polynomial.coe_evalRingHom,
    Polynomial.eval_X,map_zero]

theorem evalZZero_posInput : evalZZero posInput=0 := by
  simp only [posInput,map_add,map_mul,map_pow,evalZZero_polyZ,mul_zero,
    zero_pow (by decide : 2≠0),add_zero]

theorem evalZZero_negInput : evalZZero negInput=0 := by
  simp only [negInput,map_mul,evalZZero_polyZ,mul_zero]

theorem evalZZero_coeff (p : PolynomialTime) (d : ℕ) :
    coeff d (evalZZero p)=(coeff d p).coeff 0 := by
  simp only [evalZZero,coeff_map,Polynomial.coe_evalRingHom,← Polynomial.coeff_zero_eq_eval_zero]

theorem posSqrt_scalar :
    evalZZero (formalSqrt posInput)=1 := by
  rw [evalZZero,map_formalSqrt _ posInput_constant,← evalZZero,evalZZero_posInput,
    formalSqrt_zero]

theorem negSqrt_scalar :
    evalZZero (formalSqrt negInput)=1 := by
  rw [evalZZero,map_formalSqrt _ negInput_constant,← evalZZero,evalZZero_negInput,
    formalSqrt_zero]

theorem posInvSqrt_scalar :
    evalZZero (formalInvSqrt posInput)=1 := by
  rw [evalZZero,map_formalInvSqrt _ posInput_constant,← evalZZero,evalZZero_posInput,
    formalInvSqrt_zero]

theorem negInvSqrt_scalar :
    evalZZero (formalInvSqrt negInput)=1 := by
  rw [evalZZero,map_formalInvSqrt _ negInput_constant,← evalZZero,evalZZero_negInput,
    formalInvSqrt_zero]

theorem positiveRoot_scalar (d : ℕ) :
    (coeff d positiveRoot).coeff 0=coeff d (1 : PowerSeries ℚ) := by
  rw [positiveRoot_polynomial,positiveEmbed_coeff_zero,← evalZZero_coeff,posSqrt_scalar]

theorem negativeRoot_scalar (d : ℕ) :
    (coeff d negativeRoot).coeff 0=coeff d (1 : PowerSeries ℚ) := by
  rw [negativeRoot_polynomial,negativeEmbed_coeff_zero,← evalZZero_coeff,negSqrt_scalar]

theorem positiveInverse_scalar (d : ℕ) :
    (coeff d positiveInverse).coeff 0=coeff d (1 : PowerSeries ℚ) := by
  rw [positiveInverse_polynomial,positiveEmbed_coeff_zero,← evalZZero_coeff,posInvSqrt_scalar]

theorem negativeInverse_scalar (d : ℕ) :
    (coeff d negativeInverse).coeff 0=coeff d (1 : PowerSeries ℚ) := by
  rw [negativeInverse_polynomial,negativeEmbed_coeff_zero,← evalZZero_coeff,negInvSqrt_scalar]

#print axioms positiveInverse_mul
#print axioms negativeInverse_mul
#print axioms positiveInverse_support
#print axioms negativeInverse_support
#print axioms positiveRoot_scalar
#print axioms negativeRoot_scalar
#print axioms positiveInverse_scalar
#print axioms negativeInverse_scalar
#print axioms positiveRoot_polynomial
#print axioms negativeRoot_polynomial
#print axioms positiveRoot_support
#print axioms negativeRoot_support
end Kreweras
```

### `KrewerasRootExtraction.lean`

```lean
import KrewerasRootSupport

namespace Kreweras
open PowerSeries

noncomputable def polyFirst (p : PolynomialTime) : PowerSeries ℚ :=
  mk (fun d => (coeff d p).coeff 1)

theorem polyFirst_add (p q : PolynomialTime) :
    polyFirst (p+q)=polyFirst p+polyFirst q := by
  apply PowerSeries.ext
  intro d
  simp [polyFirst]

theorem polyFirst_one : polyFirst (1 : PolynomialTime)=0 := by
  apply PowerSeries.ext
  intro d
  cases d <;> norm_num [polyFirst,coeff_zero_eq_constantCoeff_apply,Polynomial.coeff_one]

theorem polyFirst_mul (p q : PolynomialTime) :
    polyFirst (p*q)=evalZZero p*polyFirst q+polyFirst p*evalZZero q := by
  apply PowerSeries.ext
  intro d
  simp only [polyFirst,coeff_mk,map_add,PowerSeries.coeff_mul,
    Polynomial.finsetSum_coeff,Polynomial.mul_coeff_one,Finset.sum_add_distrib,
    evalZZero_coeff]

theorem polyFirst_mul_Z (p : PolynomialTime) :
    polyFirst (p*polyZ)=evalZZero p := by
  apply PowerSeries.ext
  intro d
  simp only [polyFirst,polyZ,coeff_mk,PowerSeries.coeff_mul_C,
    Polynomial.coeff_mul_X,evalZZero_coeff]

theorem evalZZero_polyT : evalZZero polyT=T := by
  apply PowerSeries.ext
  intro d
  simp only [evalZZero,polyT,coeff_map,Polynomial.coe_evalRingHom,Polynomial.eval_C]

theorem polyFirst_negInput : polyFirst negInput=-4*X^2*T^2 := by
  rw [negInput,polyFirst_mul_Z]
  simp only [map_mul,map_neg,map_pow,map_ofNat,evalZZero_polyT]
  rw [show evalZZero X=X from PowerSeries.map_X _]

theorem negativeRoot_polynomial_first :
    polyFirst (formalSqrt negInput)=-2*X^2*T^2 := by
  have h := congrArg polyFirst (formalSqrt_sq negInput_constant)
  rw [pow_two,polyFirst_mul,polyFirst_add,polyFirst_one,zero_add,
    negSqrt_scalar,one_mul,mul_one,polyFirst_negInput] at h
  have htwo : 2*polyFirst (formalSqrt negInput)=-4*X^2*T^2 := by
    linear_combination h
  apply PowerSeries.ext
  intro d
  have hd := congrArg (coeff d) htwo
  simp only [mul_assoc,neg_mul,map_neg,coeff_ofNat_mul] at hd ⊢
  linear_combination (1/2 : ℚ)*hd

theorem negativeRoot_adjacent (d : ℕ) :
    (coeff d negativeRoot).coeff (-1)=coeff d (-2*X^2*T^2) := by
  rw [negativeRoot_polynomial]
  change (LaurentPolynomial.invert (coeff d (formalSqrt negInput)).toLaurent).coeff (-1)=_
  rw [LaurentPolynomial.invert_apply]
  change ((coeff d (formalSqrt negInput)).toLaurent).coeff (1 : ℕ)=_
  rw [toLaurent_coeff_nat]
  simpa only [polyFirst,coeff_mk] using congrArg (coeff d) negativeRoot_polynomial_first

#print axioms polyFirst_mul
#print axioms negativeRoot_polynomial_first
#print axioms negativeRoot_adjacent
end Kreweras
```

### `KrewerasLineCandidate.lean`

```lean
import KrewerasRootExtraction

namespace Kreweras
open PowerSeries

/-- Algebraic candidate for the series of slit walks ending on the line.
It is not yet identified with actual walk counts. -/
noncomputable def lineCandidate : LaurentTime := scalarT*positiveInverse

theorem lineCandidate_polynomial :
    lineCandidate=positiveEmbed (polyT*formalInvSqrt posInput) := by
  rw [map_mul,positiveEmbed_polyT,← positiveInverse_polynomial]
  rfl

theorem lineCandidate_support (d : ℕ) (j : ℤ) (hj : j<0) :
    (coeff d lineCandidate).coeff j=0 := by
  rw [lineCandidate_polynomial]
  exact positiveEmbed_support _ d j hj

theorem lineCandidate_scalar (d : ℕ) :
    (coeff d lineCandidate).coeff 0=coeff d T := by
  rw [lineCandidate_polynomial,positiveEmbed_coeff_zero,← evalZZero_coeff,
    map_mul,evalZZero_polyT,posInvSqrt_scalar,mul_one]

theorem kernelRoot_lineCandidate : kernelRoot*lineCandidate=negativeRoot := by
  calc
    _ = (scalarT*kernelRoot)*positiveInverse := by unfold lineCandidate; ring
    _ = (negativeRoot*positiveRoot)*positiveInverse := by rw [kernel_root_factorization]
    _ = _ := by rw [mul_assoc,mul_comm positiveRoot,positiveInverse_mul,mul_one]

theorem lineCandidate_kernel_equation :
    lineCandidate=negativeRoot+(1-kernelRoot)*lineCandidate := by
  rw [← kernelRoot_lineCandidate]
  ring

/-- Coefficient form of the projected last-piece equation for the candidate.
The piece series is algebraically 1-kernelRoot. -/
theorem lineCandidate_projected (d : ℕ) (j : ℤ) :
    (coeff d lineCandidate).coeff j =
      (if d=0 ∧ j=0 then 1 else 0) +
      if 0≤j then (coeff d ((1-kernelRoot)*lineCandidate)).coeff j else 0 := by
  classical
  by_cases hj : 0≤j
  · rw [ite_eq_left hj]
    have h := congrArg (fun p : LaurentTime => (coeff d p).coeff j)
      lineCandidate_kernel_equation
    simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply] at h
    rw [h]
    congr 1
    by_cases hz : j=0
    · subst j
      rw [negativeRoot_scalar,PowerSeries.coeff_one]
      simp
    · rw [negativeRoot_support d j (by omega)]
      simp [hz]
  · rw [ite_eq_right hj,lineCandidate_support d j (by omega)]
    have hz : j≠0 := by omega
    simp [hz]

#print axioms lineCandidate_scalar
#print axioms lineCandidate_support
#print axioms kernelRoot_lineCandidate
#print axioms lineCandidate_projected
end Kreweras
```

### `KrewerasMotzkinSeries.lean`

```lean
import KrewerasLineCandidate

namespace Kreweras
open PowerSeries

noncomputable def motzkinCoeff (n : ℕ) : LaurentPolynomial ℚ :=
  if _hn : n=0 then 1 else
    coeff (n-1) (C (LaurentPolynomial.T 1)*
      (mk fun i => if _hi : i<n then motzkinCoeff i else 0) +
      X*C (LaurentPolynomial.T (-1))*
      (mk fun i => if _hi : i<n then motzkinCoeff i else 0)^2)
termination_by n

noncomputable def Motzkin : LaurentTime := mk motzkinCoeff

@[simp] theorem motzkinCoeff_zero : motzkinCoeff 0=1 := by
  rw [motzkinCoeff]
  simp

theorem motzkinCoeff_succ (n : ℕ) :
    motzkinCoeff (n+1)=coeff n
      (zmark 1*(mk fun i => if i<n+1 then motzkinCoeff i else 0)+
       X*zmark (-1)*(mk fun i => if i<n+1 then motzkinCoeff i else 0)^2) := by
  rw [motzkinCoeff]
  simp [zmark]

theorem motzkin_trunc_square (n k : ℕ) (hk : k<n) :
    coeff k ((mk fun i => if i<n then motzkinCoeff i else 0)^2)=
      coeff k (Motzkin^2) := by
  simp only [pow_two,coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hs := Finset.mem_antidiagonal.mp hp
  simp only [coeff_mk,Motzkin,ite_eq_left (show p.1<n by omega),
    ite_eq_left (show p.2<n by omega)]

theorem motzkin_equation :
    Motzkin=1+X*zmark 1*Motzkin+X^2*zmark (-1)*Motzkin^2 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Motzkin,coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [show 1+X*zmark 1*Motzkin+X^2*zmark (-1)*Motzkin^2 =
        1+X*(zmark 1*Motzkin+X*zmark (-1)*Motzkin^2) by ring]
    simp only [Motzkin,coeff_mk,motzkinCoeff_succ,map_add,coeff_one,
      Nat.add_one_ne_zero,ite_false,zero_add,coeff_succ_X_mul]
    cases n with
    | zero => simp [zmark,coeff_zero_eq_constantCoeff_apply]
    | succ n =>
      simp only [zmark,coeff_C_mul,coeff_mk,
        ite_eq_left (show n+1<n+1+1 by omega),mul_assoc,coeff_succ_X_mul]
      rw [motzkin_trunc_square (n+1+1) n (by omega)]
      rfl

@[simp] theorem motzkin_constant : constantCoeff Motzkin=1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp only [Motzkin,coeff_mk,motzkinCoeff_zero]

theorem kernelRoot_motzkin :
    kernelRoot=1-X*zmark 1-2*X^2*zmark (-1)*Motzkin := by
  apply square_root_unique kernelRoot_constant (by simp)
  rw [kernelRoot_sq]
  unfold slitKernel
  have hm : (1-X*zmark 1)*Motzkin=1+X^2*zmark (-1)*Motzkin^2 := by
    linear_combination motzkin_equation
  linear_combination (4*X^2*zmark (-1))*hm

#print axioms motzkin_equation
#print axioms motzkin_constant
#print axioms kernelRoot_motzkin
end Kreweras
```

### `KrewerasWalkCandidate.lean`

```lean
import KrewerasMotzkinSeries
import KrewerasWalkRecursion

namespace Kreweras
open PowerSeries

noncomputable def upperRow (k : ℕ) : LaurentTime :=
  lineCandidate*(X*zmark (-1)*Motzkin)^k
noncomputable def lowerRow (k : ℕ) : LaurentTime :=
  lineCandidate*(X*Motzkin)^k
noncomputable def candidateRow (h : ℤ) : LaurentTime :=
  if 0≤h then upperRow h.toNat else lowerRow (-h).toNat
noncomputable def candidateCount (d : ℕ) (h r : ℤ) : ℚ :=
  (coeff d (candidateRow h)).coeff r

@[simp] theorem candidateRow_nat (k : ℕ) : candidateRow (k : ℤ)=upperRow k := by
  simp [candidateRow]
@[simp] theorem candidateRow_neg (k : ℕ) : candidateRow (-(k : ℤ))=lowerRow k := by
  cases k with
  | zero => simp [candidateRow,upperRow,lowerRow]
  | succ k =>
    have hn : ¬0≤-((k+1 : ℕ) : ℤ) := by omega
    rw [candidateRow,ite_eq_right hn,neg_neg,Int.toNat_natCast]

@[simp] theorem candidateRow_zero : candidateRow 0=lineCandidate := by
  change candidateRow ((0 : ℕ) : ℤ)=_
  rw [candidateRow_nat,upperRow,pow_zero,mul_one]

theorem upperRow_recurrence (k : ℕ) :
    upperRow (k+1)=X*zmark 1*upperRow (k+1)+X*upperRow (k+2)+
      X*zmark (-1)*upperRow k := by
  unfold upperRow
  simp only [pow_succ]
  linear_combination (lineCandidate*(X*zmark (-1)*Motzkin)^k*X*zmark (-1))*
    motzkin_equation

theorem lowerRow_recurrence (k : ℕ) :
    lowerRow (k+1)=X*zmark 1*lowerRow (k+1)+X*lowerRow k+
      X*zmark (-1)*lowerRow (k+2) := by
  unfold lowerRow
  simp only [pow_succ]
  linear_combination (lineCandidate*(X*Motzkin)^k*X)*motzkin_equation

theorem candidateRow_recurrence (h : ℤ) (hh : h≠0) :
    candidateRow h=X*zmark 1*candidateRow h+X*candidateRow (h+1)+
      X*zmark (-1)*candidateRow (h-1) := by
  rcases h with k | k
  · cases k with
    | zero => exact False.elim (hh rfl)
    | succ k =>
      change candidateRow ((k+1 : ℕ) : ℤ)=X*zmark 1*candidateRow ((k+1 : ℕ) : ℤ)+
        X*candidateRow (((k+1 : ℕ) : ℤ)+1)+X*zmark (-1)*candidateRow (((k+1 : ℕ) : ℤ)-1)
      rw [show (((k+1 : ℕ) : ℤ)+1)=((k+2 : ℕ) : ℤ) by omega,
        show (((k+1 : ℕ) : ℤ)-1)=(k : ℤ) by omega]
      simpa only [candidateRow_nat] using upperRow_recurrence k
  · have h₀ : Int.negSucc k=-((k+1 : ℕ) : ℤ) := by omega
    rw [h₀, show -((k+1 : ℕ) : ℤ)+1=-(k : ℤ) by omega,
      show -((k+1 : ℕ) : ℤ)-1=-((k+2 : ℕ) : ℤ) by omega]
    simpa only [candidateRow_neg] using lowerRow_recurrence k

theorem coeff_zmark_mul (i r : ℤ) (p : LaurentTime) (d : ℕ) :
    (coeff d (zmark i*p)).coeff r=(coeff d p).coeff (r-i) := by
  rw [zmark,coeff_C_mul,LaurentPolynomial.T]
  have h := AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff
    (x := coeff d p) (r := (1 : ℚ)) (m := i) (m₁ := r) (r-i)
    (fun m _ => by omega)
  simpa only [one_mul] using h

@[simp] theorem lineCandidate_constant : constantCoeff lineCandidate=1 := by
  simp [lineCandidate,positiveInverse,formalInvSqrt_constant]

theorem candidateRow_constant (h : ℤ) :
    constantCoeff (candidateRow h)=if h=0 then 1 else 0 := by
  classical
  by_cases hh : 0≤h
  · rw [candidateRow,ite_eq_left hh]
    by_cases hz : h=0
    · subst h; simp [upperRow]
    · have hn : h.toNat≠0 := by omega
      simp [upperRow,hz,hn]
  · rw [candidateRow,ite_eq_right hh]
    have hz : h≠0 := by omega
    have hn : (-h).toNat≠0 := by omega
    simp [lowerRow,hz,hn]

theorem candidateCount_zero (h r : ℤ) :
    candidateCount 0 h r=if h=0 ∧ r=0 then 1 else 0 := by
  classical
  rw [candidateCount,coeff_zero_eq_constantCoeff_apply,candidateRow_constant]
  by_cases hh : h=0
  · rw [ite_eq_left hh]
    have hone : (1 : LaurentPolynomial ℚ).coeff r=if r=0 then 1 else 0 := by
      change (LaurentPolynomial.T (0 : ℤ) : LaurentPolynomial ℚ).coeff r=
        if r=0 then 1 else 0
      rw [LaurentPolynomial.T_apply]
      simp only [eq_comm]
    rw [hone]
    simp [hh]
  · simp [hh]

theorem candidateCount_offline (d : ℕ) (h r : ℤ) (hh : h≠0) :
    candidateCount (d+1) h r=
      candidateCount d h (r-1)+candidateCount d (h+1) r+
      candidateCount d (h-1) (r+1) := by
  have he := congrArg (fun p : LaurentTime => (coeff (d+1) p).coeff r)
    (candidateRow_recurrence h hh)
  simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,mul_assoc,
    coeff_succ_X_mul,coeff_zmark_mul,sub_neg_eq_add] at he
  exact he

theorem candidateCount_online (d : ℕ) (r : ℤ) :
    candidateCount (d+1) 0 r=
      if r<0 then 0 else candidateCount d 0 (r-1)+
        candidateCount d 1 r+candidateCount d (-1) (r+1) := by
  classical
  have he := lineCandidate_projected (d+1) r
  have hs : (1-kernelRoot)*lineCandidate =
      X*(zmark 1*lineCandidate+candidateRow 1+zmark (-1)*candidateRow (-1)) := by
    have hp : candidateRow 1=upperRow 1 := candidateRow_nat 1
    have hn : candidateRow (-1)=lowerRow 1 := candidateRow_neg 1
    rw [kernelRoot_motzkin,hp,hn]
    unfold upperRow lowerRow
    simp only [pow_one]
    ring
  have hz : candidateRow 0=lineCandidate := candidateRow_zero
  unfold candidateCount
  rw [hz]
  by_cases hr : r<0
  · rw [ite_eq_left hr]
    exact lineCandidate_support (d+1) r hr
  · rw [ite_eq_right hr]
    rw [hs] at he
    simp only [Nat.add_one_ne_zero,false_and,ite_false,zero_add,
      ite_eq_left (show 0≤r by omega),coeff_succ_X_mul,map_add,
      AddMonoidAlgebra.coeff_add,Finsupp.add_apply,coeff_zmark_mul] at he
    simpa only [hz,sub_neg_eq_add] using he

theorem candidateCount_recurrence : SlitRecurrence candidateCount := by
  classical
  refine ⟨candidateCount_zero,?_⟩
  intro d h r
  by_cases hh : h=0
  · subst h
    simpa using candidateCount_online d r
  · rw [ite_eq_right (by simp [hh])]
    exact candidateCount_offline d h r hh

theorem origin_series : L=T := by
  rw [L_of_slitRecurrence candidateCount_recurrence]
  apply PowerSeries.ext
  intro d
  simp only [coeff_mk,candidateCount,candidateRow_zero]
  exact lineCandidate_scalar d

#print axioms candidateCount_recurrence
#print axioms origin_series
end Kreweras
```

### `KrewerasFinalEnumeration.lean`

```lean
import KrewerasWalkCandidate
import KrewerasTimeExpansion

namespace Kreweras
open PowerSeries

theorem motzkin_candidate_product :
    2*X^2*lineCandidate*Motzkin =
      zmark 1*lineCandidate-X*(zmark 2*lineCandidate)-zmark 1*negativeRoot := by
  have hm := kernelRoot_lineCandidate
  rw [kernelRoot_motzkin] at hm
  have hz : zmark 1*zmark (-1)=1 := by simp
  have hzz : zmark 2=zmark 1*zmark 1 := by rw [zmark_add]; rfl
  rw [hzz]
  linear_combination -(zmark 1)*hm -
    (2*X^2*lineCandidate*Motzkin)*hz

theorem motzkin_candidate_scalar (d : ℕ) :
    (coeff d (lineCandidate*Motzkin)).coeff 0=coeff d (T^2) := by
  have he := congrArg (fun p : LaurentTime => (coeff (d+1+1) p).coeff (0 : ℤ))
    motzkin_candidate_product
  rw [show 2*X^2*lineCandidate*Motzkin =
    2*(X*(X*(lineCandidate*Motzkin))) by ring] at he
  simp only [map_add,map_sub,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
    two_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,coeff_succ_X_mul,coeff_zmark_mul,zero_sub] at he
  rw [lineCandidate_support (d+1+1) (-1) (by decide),
    lineCandidate_support (d+1) (-2) (by decide),
    negativeRoot_adjacent (d+1+1)] at he
  have hcoef : coeff (d+1+1) (-2*X^2*T^2) = -2*coeff d (T^2) := by
    rw [show -2*X^2*T^2 = -(2*(X*(X*T^2))) by ring]
    simp only [map_neg,coeff_ofNat_mul,coeff_succ_X_mul,neg_mul]
  rw [hcoef] at he
  linarith

theorem adjacent_series : J=X*T^2 := by
  rw [J_of_slitRecurrence candidateCount_recurrence]
  apply PowerSeries.ext
  intro d
  have hn : candidateRow (-1)=lineCandidate*(X*Motzkin) := by
    have h := candidateRow_neg 1
    simpa only [lowerRow,pow_one,Nat.cast_one] using h
  cases d with
  | zero =>
    simp only [coeff_mk,candidateCount,hn]
    rw [show lineCandidate*(X*Motzkin)=X*(lineCandidate*Motzkin) by ring]
    simp [coeff_zero_eq_constantCoeff_apply]
  | succ d =>
    simp only [coeff_mk,candidateCount,hn]
    rw [show lineCandidate*(X*Motzkin)=X*(lineCandidate*Motzkin) by ring]
    rw [coeff_succ_X_mul,coeff_succ_X_mul]
    exact motzkin_candidate_scalar d

/-- The literal Hopkins–Rubey evacuation and dual evacuation formulas. -/
theorem mathdb346681 : LiteralEndpoint :=
  literal_iff_original_series.mpr ⟨origin_series,adjacent_series⟩

#check origin_series
#check adjacent_series
#print mathdb346681
#print axioms origin_series
#print axioms adjacent_series
#print axioms mathdb346681
end Kreweras
```

### `KrewerasPacket.lean`

```lean
import KrewerasWalkRecursion
import KrewerasSquareRoots
import KrewerasKernelRoots
import KrewerasLaurentSupport
import KrewerasRootSupport
import KrewerasRootExtraction
import KrewerasLineCandidate
import KrewerasMotzkinSeries
import KrewerasWalkCandidate
import KrewerasFinalEnumeration
import KrewerasCubicDifferential
import KrewerasCubicCoefficients
import KrewerasTernarySeries
import KrewerasSeriesReduction
import KrewerasKernelFactor
import KrewerasTimeExpansion
import KrewerasProducts
import KrewerasAssembly
import KrewerasProductRecurrences
import KrewerasRecurrenceReduction
import KrewerasWalkSupport
import KrewerasEndpointSeries
import KrewerasRefinement
import KrewerasPathRefinement
import KrewerasEvenCompression
import KrewerasDualPairs
import KrewerasEvenDual
import KrewerasTerminalPairs
import KrewerasOddCompression
import KrewerasOddDual
import KrewerasConstructiveLift
import KrewerasPathLift
import KrewerasWalkEndpoints
import KrewerasEnumerationHelpers
import KrewerasSanity
import KrewerasChains
import KrewerasNonempty
import KrewerasWalks

import KrewerasDominoBridge
import KrewerasDominoSymmetry

#eval Lean.versionString
#check Kreweras.wordExtensionEquiv
#check Kreweras.tau_bridge
#check Kreweras.evac_bridge
#check Kreweras.dualEvac_bridge
#check Kreweras.swap_valid_iff_incomparable
#check Kreweras.small_literal_one
#check Kreweras.small_literal_two
#check Kreweras.ideal_coordinates
#check Kreweras.stateIdeal_card
#check Kreweras.sectorSlitWalkEquiv
#check Kreweras.encode_time_injective
#print Kreweras.LiteralEndpoint
#print Kreweras.DominoConjugationGoal
#print axioms Kreweras.wordExtensionEquiv
#print axioms Kreweras.tau_bridge
#print axioms Kreweras.evac_bridge
#print axioms Kreweras.dualEvac_bridge
#print axioms Kreweras.swap_valid_iff_incomparable
#print axioms Kreweras.small_literal_one
#print axioms Kreweras.small_literal_two
#print axioms Kreweras.ideal_coordinates
#print axioms Kreweras.stateIdeal_card
#print axioms Kreweras.prefixIdeal_coordinates
#print axioms Kreweras.sector_closed
#print axioms Kreweras.singleton_sector_closed
#print axioms Kreweras.unfold_injective
#print axioms Kreweras.unfold_surjective
#print axioms Kreweras.unfold_step_iff
#print axioms Kreweras.lift_unique
#print axioms Kreweras.encode_step
#print axioms Kreweras.encode_time_injective
#print axioms Kreweras.even_diagonal_position
#print axioms Kreweras.odd_adjacent_position
#print axioms Kreweras.sectorSlitWalkEquiv

#check Kreweras.K_nonempty
#print axioms Kreweras.K_nonempty
#print axioms Kreweras.source_minimal_element
#print axioms Kreweras.dual_initial_singleton

#check Kreweras.sourceTau_distant
#print axioms Kreweras.sourceTau_distant
#check Kreweras.domino_conjugation
#print axioms Kreweras.domino_conjugation
#check Kreweras.source_domino_conjugation
#print axioms Kreweras.source_domino_conjugation
#check Kreweras.pairFixedEvacEquiv
#print axioms Kreweras.pairFixedEvacEquiv
#check Kreweras.source_pair_fixed_iff
#print axioms Kreweras.source_pair_fixed_iff
#check Kreweras.evacPairedEquiv
#print axioms Kreweras.evacPairedEquiv
#check Kreweras.domino_step_iff
#print axioms Kreweras.domino_step_iff
#check Kreweras.uncapped_step_counterexample
#print axioms Kreweras.uncapped_step_counterexample
#check Kreweras.paired_prefix_domino
#print axioms Kreweras.paired_prefix_domino
#check Kreweras.extensionIdealFlagEquiv
#print axioms Kreweras.extensionIdealFlagEquiv
#check Kreweras.evacDominoEquiv
#print axioms Kreweras.evacDominoEquiv
#check Kreweras.initial_singleton
#print axioms Kreweras.initial_singleton
#check Kreweras.odd_evac_zero
#print axioms Kreweras.odd_evac_zero
#check Kreweras.domino_cap_irrelevant
#print axioms Kreweras.domino_cap_irrelevant
#check Kreweras.D_swap
#print axioms Kreweras.D_swap
#check Kreweras.D_odd_zero
#print axioms Kreweras.D_odd_zero

-- Stage 3 endpoints and every new named declaration
#check Kreweras.UnitStep
#print axioms Kreweras.UnitStep
#check Kreweras.domino_middle_unique
#print axioms Kreweras.domino_middle_unique
#check Kreweras.domino_middle_exists
#print axioms Kreweras.domino_middle_exists
#check Kreweras.dominoMiddle
#print axioms Kreweras.dominoMiddle
#check Kreweras.dominoMiddle_spec
#print axioms Kreweras.dominoMiddle_spec
#check Kreweras.CoordinateFlag
#print axioms Kreweras.CoordinateFlag
#check Kreweras.CoordinateFlag.ext
#print axioms Kreweras.CoordinateFlag.ext
#check Kreweras.coordinateFlag_mono
#print axioms Kreweras.coordinateFlag_mono
#check Kreweras.stateIdeal_mono
#print axioms Kreweras.stateIdeal_mono
#check Kreweras.coordinateIdealFlag
#print axioms Kreweras.coordinateIdealFlag
#check Kreweras.idealCoordinateFlag
#print axioms Kreweras.idealCoordinateFlag
#check Kreweras.idealCoordinateEquiv
#print axioms Kreweras.idealCoordinateEquiv
#check Kreweras.refineState
#print axioms Kreweras.refineState
#check Kreweras.refineState_even
#print axioms Kreweras.refineState_even
#check Kreweras.refineState_odd
#print axioms Kreweras.refineState_odd
#check Kreweras.refineState_step
#print axioms Kreweras.refineState_step
#check Kreweras.refineState_size
#print axioms Kreweras.refineState_size
#check Kreweras.refineState_cap
#print axioms Kreweras.refineState_cap
#check Kreweras.pairSchedule_mem_iff
#print axioms Kreweras.pairSchedule_mem_iff
#check Kreweras.EvenCoordinateChains
#print axioms Kreweras.EvenCoordinateChains
#check Kreweras.flag_even_coordinate_iff
#print axioms Kreweras.flag_even_coordinate_iff
#check Kreweras.sourceEvenCoordinateEquiv
#print axioms Kreweras.sourceEvenCoordinateEquiv
#check Kreweras.coordinateFlag_zero
#print axioms Kreweras.coordinateFlag_zero
#check Kreweras.coordinateFlag_last
#print axioms Kreweras.coordinateFlag_last
#check Kreweras.compressEven
#print axioms Kreweras.compressEven
#check Kreweras.expandEven
#print axioms Kreweras.expandEven
#check Kreweras.compress_expand_even
#print axioms Kreweras.compress_expand_even
#check Kreweras.compressEven_injective
#print axioms Kreweras.compressEven_injective
#check Kreweras.evenCompressionEquiv
#print axioms Kreweras.evenCompressionEquiv
#check Kreweras.even_evac_domino
#print axioms Kreweras.even_evac_domino
#check Kreweras.sourceRun_bijective
#print axioms Kreweras.sourceRun_bijective
#check Kreweras.sourceConjugatorEquiv
#print axioms Kreweras.sourceConjugatorEquiv
#check Kreweras.sourceEvacPairedEquiv
#print axioms Kreweras.sourceEvacPairedEquiv
#check Kreweras.reverseLinearEquiv
#print axioms Kreweras.reverseLinearEquiv
#check Kreweras.extensionLinearEquiv
#print axioms Kreweras.extensionLinearEquiv
#check Kreweras.wordDualEquiv
#print axioms Kreweras.wordDualEquiv
#check Kreweras.wordDualEquiv_bridge
#print axioms Kreweras.wordDualEquiv_bridge
#check Kreweras.dualFixedSourceEquiv
#print axioms Kreweras.dualFixedSourceEquiv
#check Kreweras.paired_reverse_even_forward
#print axioms Kreweras.paired_reverse_even_forward
#check Kreweras.paired_reverse_even_iff
#print axioms Kreweras.paired_reverse_even_iff
#check Kreweras.dualFixedPairedEquiv
#print axioms Kreweras.dualFixedPairedEquiv
#check Kreweras.evenPairedDualEquiv
#print axioms Kreweras.evenPairedDualEquiv
#check Kreweras.evenDualEvacEquiv
#print axioms Kreweras.evenDualEvacEquiv
#check Kreweras.even_dual_domino
#print axioms Kreweras.even_dual_domino
#check Kreweras.ForwardPaired
#print axioms Kreweras.ForwardPaired
#check Kreweras.paired_reverse_iff_forward
#print axioms Kreweras.paired_reverse_iff_forward
#check Kreweras.dualFixedForwardEquiv
#print axioms Kreweras.dualFixedForwardEquiv
#check Kreweras.OddCoordinateChains
#print axioms Kreweras.OddCoordinateChains
#check Kreweras.odd_forward_flag_iff
#print axioms Kreweras.odd_forward_flag_iff
#check Kreweras.oddForwardCoordinateEquiv
#print axioms Kreweras.oddForwardCoordinateEquiv
#check Kreweras.oddDualCoordinateEquiv
#print axioms Kreweras.oddDualCoordinateEquiv
#check Kreweras.fullState
#print axioms Kreweras.fullState
#check Kreweras.OddTerminalPaths
#print axioms Kreweras.OddTerminalPaths
#check Kreweras.compressOdd
#print axioms Kreweras.compressOdd
#check Kreweras.oddExpandedState
#print axioms Kreweras.oddExpandedState
#check Kreweras.oddExpandedState_prefix
#print axioms Kreweras.oddExpandedState_prefix
#check Kreweras.oddExpandedState_last
#print axioms Kreweras.oddExpandedState_last
#check Kreweras.oddExpandedState_step
#print axioms Kreweras.oddExpandedState_step
#check Kreweras.expandOdd
#print axioms Kreweras.expandOdd
#check Kreweras.compress_expand_odd
#print axioms Kreweras.compress_expand_odd
#check Kreweras.compressOdd_injective
#print axioms Kreweras.compressOdd_injective
#check Kreweras.oddCompressionEquiv
#print axioms Kreweras.oddCompressionEquiv
#check Kreweras.oddEndB
#print axioms Kreweras.oddEndB
#check Kreweras.oddEndC
#print axioms Kreweras.oddEndC
#check Kreweras.terminal_state_iff
#print axioms Kreweras.terminal_state_iff
#check Kreweras.oddEnds_ne
#print axioms Kreweras.oddEnds_ne
#check Kreweras.terminalToSum
#print axioms Kreweras.terminalToSum
#check Kreweras.sumToTerminal
#print axioms Kreweras.sumToTerminal
#check Kreweras.oddTerminalSumEquiv
#print axioms Kreweras.oddTerminalSumEquiv
#check Kreweras.odd_dual_domino
#print axioms Kreweras.odd_dual_domino
#check Kreweras.encode_lift
#print axioms Kreweras.encode_lift
#check Kreweras.encodeWalk
#print axioms Kreweras.encodeWalk
#check Kreweras.encodeWalk_injective
#print axioms Kreweras.encodeWalk_injective
#check Kreweras.sector_path_lift
#print axioms Kreweras.sector_path_lift
#check Kreweras.encodeWalk_bijective
#print axioms Kreweras.encodeWalk_bijective
#check Kreweras.dominoSectorEquiv
#print axioms Kreweras.dominoSectorEquiv
#check Kreweras.dominoSlitEquiv
#print axioms Kreweras.dominoSlitEquiv
#check Kreweras.originCount
#print axioms Kreweras.originCount
#check Kreweras.adjacentCount
#print axioms Kreweras.adjacentCount
#check Kreweras.dominoSlitEndpointEquiv
#print axioms Kreweras.dominoSlitEndpointEquiv
#check Kreweras.origin_endpoint
#print axioms Kreweras.origin_endpoint
#check Kreweras.adjacent_endpoint
#print axioms Kreweras.adjacent_endpoint
#check Kreweras.choose_identity
#print axioms Kreweras.choose_identity
#check Kreweras.residue_derivative
#print axioms Kreweras.residue_derivative

#check Kreweras.even_counts_walk
#print axioms Kreweras.even_counts_walk
#check Kreweras.odd_counts_walk
#print axioms Kreweras.odd_counts_walk

-- Stage 4 endpoints: conditional reductions, not the unproved literal theorem
#check Kreweras.factorial_residues
#print axioms Kreweras.factorial_residues
#check Kreweras.evenProduct
#print axioms Kreweras.evenProduct
#check Kreweras.oddProduct
#print axioms Kreweras.oddProduct
#check Kreweras.P_even
#print axioms Kreweras.P_even
#check Kreweras.P_odd
#print axioms Kreweras.P_odd
#check Kreweras.WalkEnumeration
#print axioms Kreweras.WalkEnumeration
#check Kreweras.origin_count_zero
#print axioms Kreweras.origin_count_zero
#check Kreweras.adjacent_count_one
#print axioms Kreweras.adjacent_count_one
#check Kreweras.literal_of_walk_enumeration
#print axioms Kreweras.literal_of_walk_enumeration
#check Kreweras.walk_enumeration_of_literal
#print axioms Kreweras.walk_enumeration_of_literal
#check Kreweras.literal_iff_walk_enumeration
#print axioms Kreweras.literal_iff_walk_enumeration
#check Kreweras.evenProduct_zero
#print axioms Kreweras.evenProduct_zero
#check Kreweras.oddProduct_zero
#print axioms Kreweras.oddProduct_zero
#check Kreweras.evenProduct_recurrence
#print axioms Kreweras.evenProduct_recurrence
#check Kreweras.oddProduct_recurrence
#print axioms Kreweras.oddProduct_recurrence
#check Kreweras.WalkRecurrences
#print axioms Kreweras.WalkRecurrences
#check Kreweras.walk_enumeration_of_recurrences
#print axioms Kreweras.walk_enumeration_of_recurrences
#check Kreweras.walk_recurrences_of_enumeration
#print axioms Kreweras.walk_recurrences_of_enumeration
#check Kreweras.literal_iff_walk_recurrences
#print axioms Kreweras.literal_iff_walk_recurrences
#check Kreweras.walk_time_mod
#print axioms Kreweras.walk_time_mod
#check Kreweras.origin_time
#print axioms Kreweras.origin_time
#check Kreweras.adjacent_time
#print axioms Kreweras.adjacent_time
#check Kreweras.origin_count_other
#print axioms Kreweras.origin_count_other
#check Kreweras.adjacent_count_other
#print axioms Kreweras.adjacent_count_other
#check Kreweras.L
#print axioms Kreweras.L
#check Kreweras.J
#print axioms Kreweras.J
#check Kreweras.L_coeff
#print axioms Kreweras.L_coeff
#check Kreweras.J_coeff
#print axioms Kreweras.J_coeff
#check Kreweras.L_coeff_other
#print axioms Kreweras.L_coeff_other
#check Kreweras.J_coeff_other
#print axioms Kreweras.J_coeff_other
#check Kreweras.L_constant
#print axioms Kreweras.L_constant
#check Kreweras.J_constant
#print axioms Kreweras.J_constant
#check Kreweras.J_linear
#print axioms Kreweras.J_linear
#print Kreweras.WalkEnumeration
#print Kreweras.WalkRecurrences

-- Stage 5: proved coefficient algebra; the walk-series equations remain open.
#check Kreweras.derivative_ofNat
#print axioms Kreweras.derivative_ofNat
#check Kreweras.Cubic
#print axioms Kreweras.Cubic
#check Kreweras.cubic_constant
#print axioms Kreweras.cubic_constant
#check Kreweras.cubic_first_derivative
#print axioms Kreweras.cubic_first_derivative
#check Kreweras.cubic_second_derivative
#print axioms Kreweras.cubic_second_derivative
#check Kreweras.cubic_origin_ode
#print axioms Kreweras.cubic_origin_ode
#check Kreweras.cubic_square_ode
#print axioms Kreweras.cubic_square_ode
#check Kreweras.eulerLinear
#print axioms Kreweras.eulerLinear
#check Kreweras.coeff_eulerLinear
#print axioms Kreweras.coeff_eulerLinear
#check Kreweras.cubic_origin_euler
#print axioms Kreweras.cubic_origin_euler
#check Kreweras.cubic_square_euler
#print axioms Kreweras.cubic_square_euler
#check Kreweras.cubic_origin_recurrence
#print axioms Kreweras.cubic_origin_recurrence
#check Kreweras.cubic_square_recurrence
#print axioms Kreweras.cubic_square_recurrence
#check Kreweras.ternaryCoeff
#print axioms Kreweras.ternaryCoeff
#check Kreweras.ternaryCoeff_zero
#print axioms Kreweras.ternaryCoeff_zero
#check Kreweras.ternaryCoeff_succ
#print axioms Kreweras.ternaryCoeff_succ
#check Kreweras.Ternary
#print axioms Kreweras.Ternary
#check Kreweras.coeff_pow_congr_upto
#print axioms Kreweras.coeff_pow_congr_upto
#check Kreweras.ternary_cubic
#print axioms Kreweras.ternary_cubic
#check Kreweras.ternary_coeff
#print axioms Kreweras.ternary_coeff
#check Kreweras.ternary_square_coeff
#print axioms Kreweras.ternary_square_coeff
#check Kreweras.cubic_unique
#print axioms Kreweras.cubic_unique
#check Kreweras.evenProduct_ternary_convolution
#print axioms Kreweras.evenProduct_ternary_convolution
#check Kreweras.oddProduct_square_convolution
#print axioms Kreweras.oddProduct_square_convolution
#check Kreweras.U
#print axioms Kreweras.U
#check Kreweras.V
#print axioms Kreweras.V
#check Kreweras.U_coeff
#print axioms Kreweras.U_coeff
#check Kreweras.V_coeff
#print axioms Kreweras.V_coeff
#check Kreweras.WalkSeriesEquations
#print axioms Kreweras.WalkSeriesEquations
#check Kreweras.walk_recurrences_of_series_equations
#print axioms Kreweras.walk_recurrences_of_series_equations
#check Kreweras.literal_of_series_equations
#print axioms Kreweras.literal_of_series_equations
#check Kreweras.walk_series_identification_of_enumeration
#print axioms Kreweras.walk_series_identification_of_enumeration
#check Kreweras.series_equations_of_walk_enumeration
#print axioms Kreweras.series_equations_of_walk_enumeration
#check Kreweras.literal_iff_walk_series_equations
#print axioms Kreweras.literal_iff_walk_series_equations
#check Kreweras.walk_enumeration_iff_series_identification
#print axioms Kreweras.walk_enumeration_iff_series_identification
#check Kreweras.T
#print axioms Kreweras.T
#check Kreweras.T_cubic
#print axioms Kreweras.T_cubic
#check Kreweras.T_coeff
#print axioms Kreweras.T_coeff
#check Kreweras.T_square_coeff
#print axioms Kreweras.T_square_coeff
#check Kreweras.T_coeff_other
#print axioms Kreweras.T_coeff_other
#check Kreweras.slit_kernel_factor
#print axioms Kreweras.slit_kernel_factor
#check Kreweras.L_expand_U
#print axioms Kreweras.L_expand_U
#check Kreweras.J_expand_V
#print axioms Kreweras.J_expand_V
#check Kreweras.literal_iff_original_series
#print axioms Kreweras.literal_iff_original_series

#print Kreweras.Cubic
#print Kreweras.U
#print Kreweras.V
#print Kreweras.WalkSeriesEquations

-- Stage 6: complete unconditional enumeration and literal endpoint.
#check Kreweras.EndpointWalk
#print axioms Kreweras.EndpointWalk
#check Kreweras.endpointCount
#print axioms Kreweras.endpointCount
#check Kreweras.stepPred
#print axioms Kreweras.stepPred
#check Kreweras.stepPred_step
#print axioms Kreweras.stepPred_step
#check Kreweras.stepPred_injective
#print axioms Kreweras.stepPred_injective
#check Kreweras.stepPred_exists
#print axioms Kreweras.stepPred_exists
#check Kreweras.dropLastWalk
#print axioms Kreweras.dropLastWalk
#check Kreweras.snocWalk
#print axioms Kreweras.snocWalk
#check Kreweras.snocWalk_last
#print axioms Kreweras.snocWalk_last
#check Kreweras.dropLast_snocWalk
#print axioms Kreweras.dropLast_snocWalk
#check Kreweras.snoc_dropLastWalk
#print axioms Kreweras.snoc_dropLastWalk
#check Kreweras.endpointSnoc
#print axioms Kreweras.endpointSnoc
#check Kreweras.endpointSnoc_bijective
#print axioms Kreweras.endpointSnoc_bijective
#check Kreweras.endpointLastStepEquiv
#print axioms Kreweras.endpointLastStepEquiv
#check Kreweras.endpointCount_forbidden
#print axioms Kreweras.endpointCount_forbidden
#check Kreweras.endpointCount_succ
#print axioms Kreweras.endpointCount_succ
#check Kreweras.endpointCount_zero
#print axioms Kreweras.endpointCount_zero
#check Kreweras.shearedCount
#print axioms Kreweras.shearedCount
#check Kreweras.SlitRecurrence
#print axioms Kreweras.SlitRecurrence
#check Kreweras.shearedCount_recurrence
#print axioms Kreweras.shearedCount_recurrence
#check Kreweras.slitRecurrence_unique
#print axioms Kreweras.slitRecurrence_unique
#check Kreweras.solution_eq_shearedCount
#print axioms Kreweras.solution_eq_shearedCount
#check Kreweras.L_of_slitRecurrence
#print axioms Kreweras.L_of_slitRecurrence
#check Kreweras.J_of_slitRecurrence
#print axioms Kreweras.J_of_slitRecurrence
#check Kreweras.formalSqrt
#print axioms Kreweras.formalSqrt
#check Kreweras.formalSqrt_constant
#print axioms Kreweras.formalSqrt_constant
#check Kreweras.formalSqrt_sq
#print axioms Kreweras.formalSqrt_sq
#check Kreweras.square_root_unique
#print axioms Kreweras.square_root_unique
#check Kreweras.constantCoeff_map_apply
#print axioms Kreweras.constantCoeff_map_apply
#check Kreweras.map_formalSqrt
#print axioms Kreweras.map_formalSqrt
#check Kreweras.formalInvSqrt
#print axioms Kreweras.formalInvSqrt
#check Kreweras.formalInvSqrt_constant
#print axioms Kreweras.formalInvSqrt_constant
#check Kreweras.formalInvSqrt_mul
#print axioms Kreweras.formalInvSqrt_mul
#check Kreweras.formalSqrt_zero
#print axioms Kreweras.formalSqrt_zero
#check Kreweras.formalInvSqrt_zero
#print axioms Kreweras.formalInvSqrt_zero
#check Kreweras.map_formalInvSqrt
#print axioms Kreweras.map_formalInvSqrt
#check Kreweras.LaurentTime
#print axioms Kreweras.LaurentTime
#check Kreweras.scalarT
#print axioms Kreweras.scalarT
#check Kreweras.zmark
#print axioms Kreweras.zmark
#check Kreweras.zmark_add
#print axioms Kreweras.zmark_add
#check Kreweras.zmark_zero
#print axioms Kreweras.zmark_zero
#check Kreweras.scalarT_cubic
#print axioms Kreweras.scalarT_cubic
#check Kreweras.scalarT_constant
#print axioms Kreweras.scalarT_constant
#check Kreweras.slitKernel
#print axioms Kreweras.slitKernel
#check Kreweras.positiveKernel
#print axioms Kreweras.positiveKernel
#check Kreweras.negativeKernel
#print axioms Kreweras.negativeKernel
#check Kreweras.kernelRoot
#print axioms Kreweras.kernelRoot
#check Kreweras.positiveRoot
#print axioms Kreweras.positiveRoot
#check Kreweras.negativeRoot
#print axioms Kreweras.negativeRoot
#check Kreweras.slitKernel_constant
#print axioms Kreweras.slitKernel_constant
#check Kreweras.positiveKernel_constant
#print axioms Kreweras.positiveKernel_constant
#check Kreweras.negativeKernel_constant
#print axioms Kreweras.negativeKernel_constant
#check Kreweras.kernelRoot_sq
#print axioms Kreweras.kernelRoot_sq
#check Kreweras.positiveRoot_sq
#print axioms Kreweras.positiveRoot_sq
#check Kreweras.negativeRoot_sq
#print axioms Kreweras.negativeRoot_sq
#check Kreweras.kernelRoot_constant
#print axioms Kreweras.kernelRoot_constant
#check Kreweras.positiveRoot_constant
#print axioms Kreweras.positiveRoot_constant
#check Kreweras.negativeRoot_constant
#print axioms Kreweras.negativeRoot_constant
#check Kreweras.kernel_root_factorization
#print axioms Kreweras.kernel_root_factorization
#check Kreweras.toLaurent_negative
#print axioms Kreweras.toLaurent_negative
#check Kreweras.toLaurent_coeff_nat
#print axioms Kreweras.toLaurent_coeff_nat
#check Kreweras.PolynomialTime
#print axioms Kreweras.PolynomialTime
#check Kreweras.LaurentSeries
#print axioms Kreweras.LaurentSeries
#check Kreweras.positiveEmbed
#print axioms Kreweras.positiveEmbed
#check Kreweras.negativeEmbed
#print axioms Kreweras.negativeEmbed
#check Kreweras.positiveEmbed_support
#print axioms Kreweras.positiveEmbed_support
#check Kreweras.negativeEmbed_support
#print axioms Kreweras.negativeEmbed_support
#check Kreweras.positiveEmbed_coeff_zero
#print axioms Kreweras.positiveEmbed_coeff_zero
#check Kreweras.negativeEmbed_coeff_zero
#print axioms Kreweras.negativeEmbed_coeff_zero
#check Kreweras.positiveEmbed_sqrt
#print axioms Kreweras.positiveEmbed_sqrt
#check Kreweras.negativeEmbed_sqrt
#print axioms Kreweras.negativeEmbed_sqrt
#check Kreweras.polyT
#print axioms Kreweras.polyT
#check Kreweras.polyZ
#print axioms Kreweras.polyZ
#check Kreweras.posInput
#print axioms Kreweras.posInput
#check Kreweras.negInput
#print axioms Kreweras.negInput
#check Kreweras.posInput_constant
#print axioms Kreweras.posInput_constant
#check Kreweras.negInput_constant
#print axioms Kreweras.negInput_constant
#check Kreweras.positiveEmbed_polyT
#print axioms Kreweras.positiveEmbed_polyT
#check Kreweras.negativeEmbed_polyT
#print axioms Kreweras.negativeEmbed_polyT
#check Kreweras.positiveEmbed_polyZ
#print axioms Kreweras.positiveEmbed_polyZ
#check Kreweras.negativeEmbed_polyZ
#print axioms Kreweras.negativeEmbed_polyZ
#check Kreweras.positiveEmbed_X
#print axioms Kreweras.positiveEmbed_X
#check Kreweras.negativeEmbed_X
#print axioms Kreweras.negativeEmbed_X
#check Kreweras.positiveEmbed_input
#print axioms Kreweras.positiveEmbed_input
#check Kreweras.negativeEmbed_input
#print axioms Kreweras.negativeEmbed_input
#check Kreweras.positiveRoot_polynomial
#print axioms Kreweras.positiveRoot_polynomial
#check Kreweras.negativeRoot_polynomial
#print axioms Kreweras.negativeRoot_polynomial
#check Kreweras.positiveRoot_support
#print axioms Kreweras.positiveRoot_support
#check Kreweras.negativeRoot_support
#print axioms Kreweras.negativeRoot_support
#check Kreweras.positiveInverse
#print axioms Kreweras.positiveInverse
#check Kreweras.negativeInverse
#print axioms Kreweras.negativeInverse
#check Kreweras.positiveInverse_mul
#print axioms Kreweras.positiveInverse_mul
#check Kreweras.negativeInverse_mul
#print axioms Kreweras.negativeInverse_mul
#check Kreweras.positiveInverse_polynomial
#print axioms Kreweras.positiveInverse_polynomial
#check Kreweras.negativeInverse_polynomial
#print axioms Kreweras.negativeInverse_polynomial
#check Kreweras.positiveInverse_support
#print axioms Kreweras.positiveInverse_support
#check Kreweras.negativeInverse_support
#print axioms Kreweras.negativeInverse_support
#check Kreweras.evalZZero
#print axioms Kreweras.evalZZero
#check Kreweras.evalZZero_polyZ
#print axioms Kreweras.evalZZero_polyZ
#check Kreweras.evalZZero_posInput
#print axioms Kreweras.evalZZero_posInput
#check Kreweras.evalZZero_negInput
#print axioms Kreweras.evalZZero_negInput
#check Kreweras.evalZZero_coeff
#print axioms Kreweras.evalZZero_coeff
#check Kreweras.posSqrt_scalar
#print axioms Kreweras.posSqrt_scalar
#check Kreweras.negSqrt_scalar
#print axioms Kreweras.negSqrt_scalar
#check Kreweras.posInvSqrt_scalar
#print axioms Kreweras.posInvSqrt_scalar
#check Kreweras.negInvSqrt_scalar
#print axioms Kreweras.negInvSqrt_scalar
#check Kreweras.positiveRoot_scalar
#print axioms Kreweras.positiveRoot_scalar
#check Kreweras.negativeRoot_scalar
#print axioms Kreweras.negativeRoot_scalar
#check Kreweras.positiveInverse_scalar
#print axioms Kreweras.positiveInverse_scalar
#check Kreweras.negativeInverse_scalar
#print axioms Kreweras.negativeInverse_scalar
#check Kreweras.polyFirst
#print axioms Kreweras.polyFirst
#check Kreweras.polyFirst_add
#print axioms Kreweras.polyFirst_add
#check Kreweras.polyFirst_one
#print axioms Kreweras.polyFirst_one
#check Kreweras.polyFirst_mul
#print axioms Kreweras.polyFirst_mul
#check Kreweras.polyFirst_mul_Z
#print axioms Kreweras.polyFirst_mul_Z
#check Kreweras.evalZZero_polyT
#print axioms Kreweras.evalZZero_polyT
#check Kreweras.polyFirst_negInput
#print axioms Kreweras.polyFirst_negInput
#check Kreweras.negativeRoot_polynomial_first
#print axioms Kreweras.negativeRoot_polynomial_first
#check Kreweras.negativeRoot_adjacent
#print axioms Kreweras.negativeRoot_adjacent
#check Kreweras.lineCandidate
#print axioms Kreweras.lineCandidate
#check Kreweras.lineCandidate_polynomial
#print axioms Kreweras.lineCandidate_polynomial
#check Kreweras.lineCandidate_support
#print axioms Kreweras.lineCandidate_support
#check Kreweras.lineCandidate_scalar
#print axioms Kreweras.lineCandidate_scalar
#check Kreweras.kernelRoot_lineCandidate
#print axioms Kreweras.kernelRoot_lineCandidate
#check Kreweras.lineCandidate_kernel_equation
#print axioms Kreweras.lineCandidate_kernel_equation
#check Kreweras.lineCandidate_projected
#print axioms Kreweras.lineCandidate_projected
#check Kreweras.motzkinCoeff
#print axioms Kreweras.motzkinCoeff
#check Kreweras.Motzkin
#print axioms Kreweras.Motzkin
#check Kreweras.motzkinCoeff_zero
#print axioms Kreweras.motzkinCoeff_zero
#check Kreweras.motzkinCoeff_succ
#print axioms Kreweras.motzkinCoeff_succ
#check Kreweras.motzkin_trunc_square
#print axioms Kreweras.motzkin_trunc_square
#check Kreweras.motzkin_equation
#print axioms Kreweras.motzkin_equation
#check Kreweras.motzkin_constant
#print axioms Kreweras.motzkin_constant
#check Kreweras.kernelRoot_motzkin
#print axioms Kreweras.kernelRoot_motzkin
#check Kreweras.upperRow
#print axioms Kreweras.upperRow
#check Kreweras.lowerRow
#print axioms Kreweras.lowerRow
#check Kreweras.candidateRow
#print axioms Kreweras.candidateRow
#check Kreweras.candidateCount
#print axioms Kreweras.candidateCount
#check Kreweras.candidateRow_nat
#print axioms Kreweras.candidateRow_nat
#check Kreweras.candidateRow_neg
#print axioms Kreweras.candidateRow_neg
#check Kreweras.candidateRow_zero
#print axioms Kreweras.candidateRow_zero
#check Kreweras.upperRow_recurrence
#print axioms Kreweras.upperRow_recurrence
#check Kreweras.lowerRow_recurrence
#print axioms Kreweras.lowerRow_recurrence
#check Kreweras.candidateRow_recurrence
#print axioms Kreweras.candidateRow_recurrence
#check Kreweras.coeff_zmark_mul
#print axioms Kreweras.coeff_zmark_mul
#check Kreweras.lineCandidate_constant
#print axioms Kreweras.lineCandidate_constant
#check Kreweras.candidateRow_constant
#print axioms Kreweras.candidateRow_constant
#check Kreweras.candidateCount_zero
#print axioms Kreweras.candidateCount_zero
#check Kreweras.candidateCount_offline
#print axioms Kreweras.candidateCount_offline
#check Kreweras.candidateCount_online
#print axioms Kreweras.candidateCount_online
#check Kreweras.candidateCount_recurrence
#print axioms Kreweras.candidateCount_recurrence
#check Kreweras.origin_series
#print axioms Kreweras.origin_series
#check Kreweras.motzkin_candidate_product
#print axioms Kreweras.motzkin_candidate_product
#check Kreweras.motzkin_candidate_scalar
#print axioms Kreweras.motzkin_candidate_scalar
#check Kreweras.adjacent_series
#print axioms Kreweras.adjacent_series
#check Kreweras.mathdb346681
#print axioms Kreweras.mathdb346681
#print Kreweras.mathdb346681
```

