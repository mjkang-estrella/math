# MathDB 362601 Frozen Lean source appendix

The fourteen canonical modules are listed in checked dependency order.

## Version.lean

```lean
import Lean
#eval Lean.versionString
```

## Base.lean

```lean
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Roy362601

def Sq (q : ℕ) : Prop := ∃ r : ℕ, 1 ≤ r ∧ q = r*r
def Big (q : ℕ) : Prop := ∃ r : ℕ, 2 ≤ r ∧ q = r*r

theorem sq_mono {a b : ℕ} (h : a ≤ b) : a*a ≤ b*b := Nat.mul_le_mul h h
theorem sq_strict {a b : ℕ} (h : a < b) : a*a < b*b := by
  have hb : 0 < b := by omega
  exact (Nat.mul_le_mul_right a (Nat.le_of_lt h)).trans_lt (Nat.mul_lt_mul_of_pos_left h hb)

theorem sq_le_iff {a b : ℕ} : a*a ≤ b*b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hn
    exact (Nat.not_lt_of_ge h) (sq_strict (Nat.lt_of_not_ge hn))
  · exact sq_mono

theorem big_four {q : ℕ} (h : Big q) : 4 ≤ q := by
  obtain ⟨r,hr,rfl⟩ := h
  exact sq_mono hr

theorem sq_cases {q : ℕ} (h : Sq q) : q = 1 ∨ Big q := by
  obtain ⟨r,hr,rfl⟩ := h
  by_cases h : r = 1
  · simp [h]
  · exact Or.inr ⟨r, by omega, rfl⟩

theorem big_sq {q : ℕ} (h : Big q) : Sq q := by
  obtain ⟨r,hr,hq⟩ := h
  exact ⟨r,by omega,hq⟩

abbrev Squares (t : ℕ) := {p : Nat.Partition t // ∀ q ∈ p.parts, Sq q}
noncomputable instance (t : ℕ) : Fintype (Squares t) := by
  classical
  unfold Squares
  infer_instance

noncomputable def P (t : ℕ) : ℕ := Fintype.card (Squares t)

abbrev F (t : ℕ) := {x : Multiset ℕ // (∀ q ∈ x, Big q) ∧ x.sum ≤ t}

def fours (k : ℕ) : Multiset ℕ := Multiset.replicate k 4
def one (q : ℕ) : Multiset ℕ := {q}

noncomputable def strip {t : ℕ} (p : Squares t) : F t := by
  classical
  refine ⟨p.val.parts.filter (· ≠ 1), ?_, ?_⟩
  · intro q hq
    obtain ⟨hmem,hne⟩ := Multiset.mem_filter.mp hq
    exact (sq_cases (p.property q hmem)).resolve_left hne
  · have h := congrArg Multiset.sum (Multiset.filter_add_not (· ≠ 1) p.val.parts)
    rw [Multiset.sum_add, p.val.parts_sum] at h
    omega

def pad {t : ℕ} (x : F t) : Squares t := by
  let y := x.val + Multiset.replicate (t-x.val.sum) 1
  have hq : ∀ q ∈ y, Sq q := by
    intro q h
    rcases Multiset.mem_add.mp h with h | h
    · exact big_sq (x.property.1 q h)
    · have e := (Multiset.mem_replicate.mp h).2
      subst q
      exact ⟨1, by decide, rfl⟩
  refine ⟨⟨y, ?_, ?_⟩, hq⟩
  · intro q h
    obtain ⟨r,hr,rfl⟩ := hq q h
    exact Nat.mul_pos hr hr
  · simp [y, Nat.add_sub_of_le x.property.2]

theorem strip_pad {t : ℕ} (x : F t) : strip (pad x) = x := by
  apply Subtype.ext
  change Multiset.filter (· ≠ 1) (x.val + Multiset.replicate (t-x.val.sum) 1) = x.val
  rw [Multiset.filter_add, Multiset.filter_eq_self.mpr]
  · simp only [add_eq_left, Multiset.filter_eq_nil]
    exact fun _ h hh => hh (Multiset.mem_replicate.mp h).2
  · intro q hq
    have := big_four (x.property.1 q hq)
    omega

theorem pad_strip {t : ℕ} (p : Squares t) : pad (strip p) = p := by
  classical
  apply Subtype.ext
  apply Nat.Partition.ext
  let x := p.val.parts.filter (· ≠ 1)
  let y := p.val.parts.filter (· = 1)
  have hy : y = Multiset.replicate y.card 1 := by
    apply Multiset.eq_replicate_card.mpr
    exact fun q h => (Multiset.mem_filter.mp h).2
  have e : x + y = p.val.parts := by
    simpa [x,y] using (Multiset.filter_add_not (· ≠ 1) p.val.parts)
  have hs : x.sum + y.card = t := by
    calc
      x.sum + y.card = (x+y).sum := by
        rw [Multiset.sum_add, hy]
        simp
      _ = t := by rw [e, p.val.parts_sum]
  change x + Multiset.replicate (t-x.sum) 1 = p.val.parts
  rwa [show t-x.sum = y.card by omega, ← hy]

noncomputable def padding (t : ℕ) : F t ≃ Squares t :=
  ⟨pad, strip, strip_pad, pad_strip⟩

noncomputable instance (t : ℕ) : Fintype (F t) :=
  Fintype.ofEquiv (Squares t) (padding t).symm

theorem card_F (t : ℕ) : Fintype.card (F t) = P t :=
  Fintype.card_congr (padding t)

def F.embed {a b : ℕ} (h : a ≤ b) : F a ↪ F b where
  toFun x := ⟨x.val, x.property.1, x.property.2.trans h⟩
  inj' := fun _ _ e => Subtype.ext (congrArg (fun z : F b => z.val) e)

theorem P_mono {a b : ℕ} (h : a ≤ b) : P a ≤ P b := by
  rw [← card_F, ← card_F]
  exact Fintype.card_le_of_injective _ (F.embed h).injective

theorem card_lt_omit {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
    (hi : Function.Injective f) (z : β) (hz : ∀ x, f x ≠ z) :
    Fintype.card α < Fintype.card β :=
  Fintype.card_lt_of_injective_not_surjective f hi (fun h => by
    obtain ⟨x,e⟩ := h z
    exact hz x e)

theorem P_succ_lt_iff (t : ℕ) :
    P t < P (t+1) ↔ ∃ x : F (t+1), x.val.sum = t+1 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    let f : F (t+1) → F t :=
      fun x => ⟨x.val, x.property.1, by have := x.property.2; have := hn x; omega⟩
    have hf : Function.Injective f := fun _ _ e => Subtype.ext (congrArg (fun z : F t => z.val) e)
    have hc := Fintype.card_le_of_injective f hf
    rw [card_F, card_F] at hc
    omega
  · rintro ⟨x,hx⟩
    rw [← card_F, ← card_F]
    apply card_lt_omit (F.embed (Nat.le_succ t)) (F.embed (Nat.le_succ t)).injective x
    intro y h
    have e : y.val = x.val := congrArg Subtype.val h
    have := y.property.2
    rw [e,hx] at this
    omega

end Roy362601
```

## Cut.lean

```lean
import Base
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Find

namespace Roy362601

theorem list_cut {n : ℕ} (l : List ℕ) (h : n < l.sum) :
    ∃ U w y, l = U ++ w :: y ∧ y.sum ≤ n ∧ n < w + y.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases hl : l.sum ≤ n
    · exact ⟨[],a,l,rfl,hl,by simpa using h⟩
    · obtain ⟨U,w,y,e,hy,hw⟩ := ih (by omega)
      exact ⟨a::U,w,y,congrArg (a :: ·) e,hy,hw⟩

theorem earlier_suffix {n : ℕ} (v y : List ℕ) (w : ℕ) (h : n < w + y.sum) :
    n < (v ++ w :: y).sum := by
  simp only [List.sum_append, List.sum_cons]
  omega

structure Crossing (n m : ℕ) (x : Multiset ℕ) where
  y : F n
  U : Multiset ℕ
  b : ℕ
  b_ge : 2 ≤ b
  U_big : ∀ q ∈ U, Big q
  U_ge : ∀ q ∈ U, b*b ≤ q
  y_le : ∀ q ∈ y.val, q ≤ b*b
  cross : n < y.val.sum + b*b
  budget : U.sum + b*b + y.val.sum ≤ n+m
  reconstruct : x = U + one (b*b) + y.val

theorem exists_crossing {n m : ℕ} (x : F (n+m)) (h : n < x.val.sum) :
    Nonempty (Crossing n m x.val) := by
  let l := x.val.sort (· ≥ ·)
  have he : (↑l : Multiset ℕ) = x.val := Multiset.sort_eq _ _
  have hs : l.sum = x.val.sum := by rw [← he, Multiset.sum_coe]
  obtain ⟨U,w,y,e,hy,hw⟩ := list_cut l (by omega : n < l.sum)
  have hp : l.Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
  rw [e, List.pairwise_append, List.pairwise_cons] at hp
  have conv : ∀ q ∈ U ++ w :: y, Big q := by
    intro q hq
    apply x.property.1
    rw [← he, Multiset.mem_coe, e]
    exact hq
  obtain ⟨b,hb,rfl⟩ := conv w (by simp)
  have hbgt : ∀ q ∈ U, b*b ≤ q := fun q hq => hp.2.2 q hq _ (by simp)
  have hylt : ∀ q ∈ y, q ≤ b*b := hp.2.1.1
  have hre : x.val = (↑U : Multiset ℕ) + one (b*b) + (↑y : Multiset ℕ) := by
    rw [← he,e]
    simp [one,add_assoc]
  refine ⟨⟨⟨↑y,?_,by simpa using hy⟩,↑U,b,hb,?_,?_,?_,?_,?_,hre⟩⟩
  · intro q hq
    exact conv q (by simp_all)
  · intro q hq
    exact conv q (by simp_all)
  · exact hbgt
  · exact hylt
  · simp only [Multiset.sum_coe]
    omega
  · have hh := x.property.2
    rwa [hre, Multiset.sum_add, Multiset.sum_add, show (one (b*b)).sum = b*b by simp [one]] at hh

def Admissible {n : ℕ} (y : F n) (s : ℕ) : Prop :=
  2 ≤ s ∧ n < y.val.sum + s*s ∧ ∀ q ∈ y.val, q ≤ s*s

theorem admissible_exists {n : ℕ} (y : F n) : ∃ s, Admissible y s := by
  refine ⟨n+2,by omega,?_,?_⟩
  · have hh : n+2 ≤ (n+2)*(n+2) := by
      exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  · intro q hq
    have h := (Multiset.le_sum_of_mem hq).trans y.property.2
    exact h.trans ((show n ≤ n+2 by omega).trans (by
      exact Nat.le_mul_of_pos_right _ (by omega)))

noncomputable def root {n : ℕ} (y : F n) : ℕ := by
  classical
  exact Nat.find (admissible_exists y)

theorem root_spec {n : ℕ} (y : F n) : Admissible y (root y) := by
  classical
  exact Nat.find_spec (admissible_exists y)

theorem root_min {n : ℕ} (y : F n) {b : ℕ} (hb : Admissible y b) : root y ≤ b := by
  classical
  exact Nat.find_min' (admissible_exists y) hb

theorem Crossing.offset {n m : ℕ} {x : Multiset ℕ} (c : Crossing n m x) :
    ∃! j, c.b = root c.y + j := by
  have h := root_min c.y ⟨c.b_ge,c.cross,c.y_le⟩
  exact ⟨c.b-root c.y,by omega,fun _ hj => by omega⟩

@[simp] theorem sum_one (q : ℕ) : (one q).sum = q := by simp [one]
@[simp] theorem sum_fours (k : ℕ) : (fours k).sum = 4*k := by simp [fours,Nat.mul_comm]
@[simp] theorem card_one (q : ℕ) : (one q).card = 1 := by simp [one]
@[simp] theorem card_fours (k : ℕ) : (fours k).card = k := by simp [fours]
@[simp] theorem mem_one {q a : ℕ} : q ∈ one a ↔ q = a := by simp [one]
theorem mem_fours {q k : ℕ} (h : q ∈ fours k) : q = 4 :=
  (Multiset.mem_replicate.mp h).2

theorem big_fours (k : ℕ) : ∀ q ∈ fours k, Big q := by
  intro q h
  rw [mem_fours h]
  exact ⟨2,by decide,rfl⟩

def y₀ (n : ℕ) : F n := ⟨fours (n/4),big_fours _,by simp; omega⟩

theorem root_two {n : ℕ} (y : F n) : root y = 2 ↔ y = y₀ n := by
  constructor
  · intro h
    obtain ⟨_,hs,hq⟩ := root_spec y
    rw [h] at hs hq
    have hr : y.val = fours y.val.card := Multiset.eq_replicate_card.mpr fun q hq' => by
      have := hq q hq'
      have := big_four (y.property.1 q hq')
      omega
    have hw := y.property.2
    rw [hr,sum_fours] at hs hw
    have hc : y.val.card = n/4 := by omega
    exact Subtype.ext (hr.trans (congrArg fours hc))
  · rintro rfl
    have hh : Admissible (y₀ n) 2 := by
      refine ⟨by decide, ?_, fun q h => by rw [mem_fours h]⟩
      change n < (fours (n/4)).sum + 2*2
      rw [sum_fours]
      omega
    have := root_min (y₀ n) hh
    have := (root_spec (y₀ n)).1
    omega

theorem cross_card {n m : ℕ}
    (f : F (n+m) → F n × F m) (hi : Function.Injective f)
    (z : F n × F m) (hz : ∀ x, f x ≠ z) : P (n+m) < P m * P n := by
  have := card_lt_omit f hi z hz
  simpa [Fintype.card_prod,card_F,Nat.mul_comm] using this

end Roy362601
```

## Code.lean

```lean
import Cut

namespace Roy362601

def zeroF (n : ℕ) : F n := ⟨0,by simp⟩
def fourF {n : ℕ} (k : ℕ) (h : 4*k ≤ n) : F n :=
  ⟨fours k,big_fours k,by simpa only [sum_fours] using h⟩

theorem exists_mem_of_nonzero {U : Multiset ℕ} (h : U ≠ 0) : ∃ q, q ∈ U := by
  by_contra hn
  push Not at hn
  exact h (Multiset.eq_zero_of_forall_notMem hn)

theorem sum_ge_of_nonzero {U : Multiset ℕ} {w : ℕ} (h : U ≠ 0)
    (hu : ∀ q ∈ U, w ≤ q) : w ≤ U.sum := by
  obtain ⟨q,hq⟩ := exists_mem_of_nonzero h
  exact (hu q hq).trans (Multiset.le_sum_of_mem hq)

theorem eq_zero_of_sum_lt_four {U : Multiset ℕ} (hb : ∀ q ∈ U, Big q)
    (h : U.sum < 4) : U = 0 := by
  by_contra hn
  have := sum_ge_of_nonzero hn (fun q hq => big_four (hb q hq))
  omega

theorem eq_one_four_of_small {U : Multiset ℕ} (hb : ∀ q ∈ U, Big q)
    (h : U.sum < 8) (hn : U ≠ 0) : U = one 4 := by
  obtain ⟨q,hq⟩ := exists_mem_of_nonzero hn
  obtain ⟨r,hr,rfl⟩ := hb q hq
  have hsum := Multiset.le_sum_of_mem hq
  have he : r = 2 := by
    by_contra hn'
    have := sq_mono (show 3 ≤ r by omega)
    omega
  subst r
  have e := Multiset.cons_erase hq
  have es := congrArg Multiset.sum e
  simp only [Multiset.sum_cons] at es
  have hv := eq_zero_of_sum_lt_four
    (fun q hq' => hb q (Multiset.erase_subset _ _ hq'))
    (show (U.erase (2*2)).sum < 4 by omega)
  rw [hv] at e
  exact e.symm

@[simp] theorem fours_zero : fours 0 = 0 := rfl
@[simp] theorem fours_one : fours 1 = one 4 := rfl

theorem pair_ne_left {n m : ℕ} {x y : F n} (h : x ≠ y) (a b : F m) :
    (x,a) ≠ (y,b) := fun e => h (congrArg Prod.fst e)

theorem y₀_cross {n m : ℕ} {x : Multiset ℕ} (c : Crossing n m x)
    (he : c.y = y₀ n) : c.U.sum + c.b*c.b ≤ m + 3 := by
  have h := c.budget
  rw [he] at h
  change c.U.sum + c.b*c.b + (fours (n/4)).sum ≤ n+m at h
  rw [sum_fours] at h
  omega

end Roy362601
```

## Increment.lean

```lean
import Base

namespace Roy362601

set_option linter.style.haveILetI false

theorem P_restricted (t : ℕ) [DecidablePred Sq] :
    P t = (Nat.Partition.restricted t Sq).card := by
  classical
  let R := Nat.Partition.restricted t Sq
  have hr (p : Nat.Partition t) : p ∈ R ↔ ∀ q ∈ p.parts, Sq q := by
    simp [R,Nat.Partition.restricted]
  let e : Squares t ≃ ↥R :=
    ⟨fun p => ⟨p.val,(hr _).mpr p.property⟩,
    fun p => ⟨p.val,(hr _).mp p.property⟩,
    fun _ => rfl,fun _ => rfl⟩
  exact (Fintype.card_congr e).trans (Fintype.card_coe R)

abbrev WithOne (t : ℕ) := {p : Squares t // 1 ∈ p.val.parts}
abbrev WithoutOne (t : ℕ) := {p : Squares t // 1 ∉ p.val.parts}
abbrev ExactWeight (t : ℕ) := {x : F t // x.val.sum = t}

def removeOne {t : ℕ} (ht : 1 ≤ t) : WithOne t ≃ Squares (t-1) := by
  let e := Nat.Partition.partitionWithPartEquiv (by decide : 1 ≤ 1) ht
  let forward (p : WithOne t) : {p : Nat.Partition t // 1 ∈ p.parts} :=
    ⟨p.val.val,p.property⟩
  refine ⟨fun p => ⟨e (forward p),?_⟩, fun p => ⟨⟨(e.symm p.val).val,?_⟩,
    (e.symm p.val).property⟩,?_,?_⟩
  · intro q hq
    rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at hq
    exact p.val.property q (Multiset.erase_subset _ _ hq)
  · intro q hq
    rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts] at hq
    rcases Multiset.mem_cons.mp hq with rfl | h
    · exact ⟨1,by decide,rfl⟩
    · exact p.property q h
  · intro p
    exact Subtype.ext (Subtype.ext (congrArg (fun z : {p : Nat.Partition t // 1 ∈ p.parts} => z.val) (e.symm_apply_apply (forward p))))
  · intro p
    exact Subtype.ext (e.apply_symm_apply p.val)

noncomputable def noOnes (t : ℕ) : WithoutOne t ≃ ExactWeight t := by
  classical
  have hp (p : WithoutOne t) : (strip p.val).val = p.val.val.parts := by
    apply Multiset.filter_eq_self.mpr
    intro q hq h
    subst q
    exact p.property hq
  refine ⟨fun p => ⟨strip p.val,(congrArg Multiset.sum (hp p)).trans p.val.val.parts_sum⟩,
    fun x => ⟨pad x.val,?_⟩,fun p => Subtype.ext (pad_strip p.val),
    fun x => Subtype.ext (strip_pad x.val)⟩
  change 1 ∉ x.val.val + Multiset.replicate (t - x.val.val.sum) 1
  rw [x.property,Nat.sub_self]
  simp only [Multiset.replicate_zero,add_zero]
  intro h
  have := big_four (x.val.property.1 1 h)
  omega

theorem P_add_exact (t : ℕ) :
    P (t+1) = P t + @Fintype.card (ExactWeight (t+1)) (by classical infer_instance) := by
  classical
  let e := (Equiv.sumCompl (fun x : Squares (t+1) => 1 ∈ x.val.parts)).symm
  have h := Fintype.card_congr e
  have hyes := Fintype.card_congr (removeOne (t := t+1) (by omega))
  have hno := Fintype.card_congr (noOnes (t+1))
  simp only [Nat.add_sub_cancel] at hyes
  rw [Fintype.card_sum,hyes,hno] at h
  exact h

end Roy362601
```

## OrdinaryCode.lean

```lean
import Code
import Mathlib.Data.Nat.Sqrt

namespace Roy362601

def dropFour : ℕ → Multiset ℕ → Multiset ℕ
  | 0, c => c
  | k+1, c => dropFour k (c.erase 4)

@[simp] theorem dropFour_add (U : Multiset ℕ) (k : ℕ) :
    dropFour k (U + fours k) = U := by
  induction k with
  | zero => simp [dropFour]
  | succ k ih => simpa [dropFour,fours,Multiset.replicate_succ,Multiset.add_cons] using ih

@[simp] theorem count_fours (k : ℕ) : (fours k).count 4 = k := by
  induction k with
  | zero => simp
  | succ k ih => simp [fours,Multiset.replicate_succ] at ih ⊢

@[simp] theorem count_one (a : ℕ) : (one a).count 4 = if 4 = a then 1 else 0 :=
  Multiset.count_singleton _ _

theorem erase_one_add (U : Multiset ℕ) (a : ℕ) : (U + one a).erase a = U := by
  rw [show U + one a = a ::ₘ U by change U + (a ::ₘ 0) = _; rw [Multiset.add_cons,add_zero]]
  exact Multiset.erase_cons_head _ _

noncomputable def minPart (U : Multiset ℕ) : ℕ := by
  classical
  exact if h : ∃ q, q ∈ U then Nat.find h else 0

theorem minPart_add (U : Multiset ℕ) (a : ℕ) (hU : ∀ q ∈ U, a ≤ q) :
    minPart (U + one a) = a := by
  classical
  have h : ∃ q, q ∈ U + one a := ⟨a,by simp⟩
  simp only [minPart,dite_eq_left h]
  apply le_antisymm
  · exact Nat.find_min' h (by simp)
  · rcases Multiset.mem_add.mp (Nat.find_spec h) with hq | hq
    · exact hU _ hq
    · simpa only [mem_one] using (mem_one.mp hq).ge

theorem big_one {q : ℕ} (h : Big q) : ∀ a ∈ one q, Big a := by
  intro a ha
  rwa [mem_one.mp ha]

theorem big_add {u v : Multiset ℕ} (hu : ∀ a ∈ u, Big a) (hv : ∀ a ∈ v, Big a) :
    ∀ a ∈ u+v, Big a := fun a h => (Multiset.mem_add.mp h).elim (hu a) (hv a)

def markers (s : ℕ) : ℕ := if s < 5 then 1 else 2

noncomputable def ordinaryDecode {n : ℕ} (y : F n) (C : Multiset ℕ) : Multiset ℕ :=
  let s := root y
  if C = one 4 then one (s*s) + y.val
  else if C.count 4 = 0 then C + one (s*s) + y.val
  else
    let u := dropFour (markers s) C
    let v := minPart u
    let b := s + (v.sqrt - 1)
    u.erase v + one (b*b) + y.val

structure OrdinaryFormat (s : ℕ) (C : Multiset ℕ) : Prop where
  nonempty : C ≠ 0
  atThree : s = 3 → C.count 4 ≤ 2
  noDouble : 5 ≤ s → C ≠ fours 2
  oneMarker : 5 ≤ s → C.count 4 = 1 → C = one 4

theorem ordinary_cover {n m : ℕ} {x : Multiset ℕ} (c : Crossing n m x)
    (hm : 4 ≤ m) (hs : 3 ≤ root c.y) :
    ∃ C : F m, ordinaryDecode c.y C.val = x ∧ OrdinaryFormat (root c.y) C.val := by
  let s := root c.y
  have hb := root_min c.y ⟨c.b_ge,c.cross,c.y_le⟩
  change s ≤ c.b at hb
  have hsq := sq_mono (show 3 ≤ c.b by omega)
  have hn4 : 4 ∉ c.U := by
    intro h
    have := c.U_ge 4 h
    omega
  have hzero : c.U.count 4 = 0 := Multiset.count_eq_zero.mpr hn4
  have cross := c.cross
  have budget := c.budget
  by_cases e : c.b = s
  · by_cases hU : c.U = 0
    · let z : F m := fourF 1 (by omega)
      have hz : z.val = one 4 := rfl
      refine ⟨z,?_,?_⟩
      · simpa [ordinaryDecode,hz,← e,s,hU] using c.reconstruct.symm
      · rw [hz]
        exact ⟨by simp [one],fun _ => by decide,
          fun _ h => by have := congrArg Multiset.card h; simp at this,
          fun _ _ => rfl⟩
    · let z : F m := ⟨c.U,c.U_big,by omega⟩
      have hz : z.val = c.U := rfl
      have hne : c.U ≠ one 4 := by
        intro he
        rw [he] at hzero
        simp at hzero
      refine ⟨z,?_,?_⟩
      · simpa [ordinaryDecode,hz,hne,hzero,← e,s] using c.reconstruct.symm
      · rw [hz]
        refine ⟨hU,fun _ => by omega,fun _ h => ?_,fun _ h => by omega⟩
        rw [h,count_fours] at hzero
        omega
  · let j := c.b - s
    let v := (j+1)*(j+1)
    let k := markers s
    have hj : 1 ≤ j := by omega
    have eb : c.b = s+j := by omega
    have hvlt : v < c.b*c.b := sq_strict (by omega)
    have hv : Big v := ⟨j+1,by omega,rfl⟩
    have hk : 1 ≤ k ∧ k ≤ 2 := by
      dsimp [k,markers]
      split <;> omega
    have hmarker : 4*k ≤ (2*s-2)*j := by
      have bound := Nat.mul_le_mul_left (2*s-2) hj
      by_cases h : s < 5
      · simp [k,markers,h]
        omega
      · simp [k,markers,h]
        omega
    have hexpand : c.b*c.b+1 = s*s+v+(2*s-2)*j := by
      have he := congrArg (fun u : ℕ => u*j) (show 2*s-2+2 = 2*s by omega)
      rw [Nat.add_mul] at he
      rw [eb]
      dsimp [v]
      nlinarith
    have hcut := (root_spec c.y).2.1
    change n < c.y.val.sum + s*s at hcut
    let C := c.U + one v + fours k
    have hsum : C.sum ≤ m := by
      simp only [C,Multiset.sum_add,sum_one,sum_fours]
      omega
    let z : F m := ⟨C,big_add (big_add c.U_big (big_one hv)) (big_fours _),hsum⟩
    have hc : C.count 4 = (if 4 = v then 1 else 0) + k := by
      simp [C,Multiset.count_add,hzero]
    have hcard : C.card = c.U.card + 1 + k := by simp [C]
    have hpos : 0 < C.count 4 := by
      rw [hc]
      omega
    have hne : C ≠ one 4 := by
      intro h
      rw [h,card_one] at hcard
      omega
    refine ⟨z,?_,?_⟩
    · change ordinaryDecode c.y C = x
      have hmin : minPart (c.U + one v) = v :=
        minPart_add _ _ (fun q hq => (Nat.le_of_lt hvlt).trans (c.U_ge q hq))
      have hb' : root c.y + (v.sqrt-1) = c.b := by
        dsimp [v]
        rw [Nat.sqrt_eq]
        change s + (j+1-1) = c.b
        omega
      unfold ordinaryDecode
      rw [ite_eq_right hne, ite_eq_right (show C.count 4 ≠ 0 by omega)]
      change (dropFour k C).erase (minPart (dropFour k C)) +
        one ((root c.y + ((minPart (dropFour k C)).sqrt-1)) *
          (root c.y + ((minPart (dropFour k C)).sqrt-1))) + c.y.val = x
      rw [show dropFour k C = c.U + one v by exact dropFour_add _ _,
        hmin,hb',erase_one_add]
      exact c.reconstruct.symm
    · change OrdinaryFormat s C
      refine ⟨?_,?_,?_,?_⟩
      · intro h
        rw [h] at hcard
        simp only [Multiset.card_zero] at hcard
        omega
      · intro h
        have hk' : k = 1 := by simp [k,markers,h]
        rw [hc,hk']
        split <;> omega
      · intro h he
        have hk' : k = 2 := by simp [k,markers,show ¬s < 5 by omega]
        rw [he,card_fours,hk'] at hcard
        omega
      · intro h he
        have hk' : k = 2 := by simp [k,markers,show ¬s < 5 by omega]
        rw [hc,hk'] at he
        omega

end Roy362601
```

## Bulk.lean

```lean
import OrdinaryCode

namespace Roy362601

set_option linter.unusedSimpArgs false

def prevY {n : ℕ} (hn : 24 ≤ n) : F n :=
  fourF (n/4-1) (by omega)

def smallY {n : ℕ} (hn : 24 ≤ n) (k : ℕ) (hk : k ≤ 2) : F n :=
  fourF k (by omega)

@[simp] theorem card_prevY {n : ℕ} (hn : 24 ≤ n) : (prevY hn).val.card = n/4-1 := by
  simp [prevY,fourF]

@[simp] theorem card_smallY {n : ℕ} (hn : 24 ≤ n) (k : ℕ) (hk : k ≤ 2) :
    (smallY hn k hk).val.card = k := by simp [smallY,fourF]

@[simp] theorem card_y₀ (n : ℕ) : (y₀ n).val.card = n/4 := by simp [y₀]

theorem root_prevY {n : ℕ} (hn : 24 ≤ n) : root (prevY hn) = 3 := by
  have e : prevY hn ≠ y₀ n := by
    intro e
    have h := congrArg (fun y : F n => y.val.card) e
    simp only [card_prevY,card_y₀] at h
    omega
  have h2 : root (prevY hn) ≠ 2 := fun h => e ((root_two _).mp h)
  have hmin := (root_spec (prevY hn)).1
  have h3 : Admissible (prevY hn) 3 := by
    refine ⟨by decide,?_,?_⟩
    · change n < (fours (n/4-1)).sum + 3*3
      rw [sum_fours]
      omega
    · intro q hq
      rw [mem_fours hq]
      decide
  have := root_min (prevY hn) h3
  omega

theorem root_smallY {n : ℕ} (hn : 24 ≤ n) (k : ℕ) (hk : k ≤ 2) :
    5 ≤ root (smallY hn k hk) := by
  have hs := (root_spec (smallY hn k hk)).2.1
  change n < (fours k).sum + root (smallY hn k hk) * root (smallY hn k hk) at hs
  rw [sum_fours] at hs
  by_contra h
  have := sq_mono (show root (smallY hn k hk) ≤ 4 by omega)
  omega

noncomputable def prevDecode (Y C : Multiset ℕ) : Multiset ℕ :=
  if C.count 4 = 3 then
    let U := dropFour 3 C
    if 9 ∈ U then U.erase 9 + one 25 + Y else U + one 16 + Y
  else
    let U := dropFour 4 C
    let v := minPart U
    U.erase v + one ((v.sqrt+2)*(v.sqrt+2)) + Y

noncomputable def bulkDecode {n m : ℕ} (hn : 24 ≤ n) (p : F n × F m) : Multiset ℕ := by
  classical
  let y := p.1
  let C := p.2.val
  let Y := (y₀ n).val
  exact if C = 0 then y.val
    else if y = y₀ n then C + one 4 + Y
    else if y = prevY hn ∧ 3 ≤ C.count 4 then prevDecode Y C
    else if y = smallY hn 0 (by decide) ∧ C = fours 2 then one 9 + Y
    else if y = smallY hn 1 (by decide) ∧ C = fours 2 then one 4 + Y
    else if y = smallY hn 0 (by decide) ∧ C.count 4 = 1 ∧ C ≠ one 4 then
      dropFour 1 C + one 9 + Y
    else ordinaryDecode y C

theorem bulk_on_ordinary {n m : ℕ} (hn : 24 ≤ n) (y : F n) (C : F m)
    (hy : y ≠ y₀ n) (hf : OrdinaryFormat (root y) C.val) :
    bulkDecode hn (y,C) = ordinaryDecode y C.val := by
  have hp : ¬ (y = prevY hn ∧ 3 ≤ C.val.count 4) := by
    rintro ⟨rfl,h⟩
    have := hf.atThree (root_prevY hn)
    omega
  have he : ¬ (y = smallY hn 0 (by decide) ∧ C.val = fours 2) := by
    rintro ⟨rfl,h⟩
    exact hf.noDouble (root_smallY hn 0 (by decide)) h
  have h1 : ¬ (y = smallY hn 1 (by decide) ∧ C.val = fours 2) := by
    rintro ⟨rfl,h⟩
    exact hf.noDouble (root_smallY hn 1 (by decide)) h
  have h01 : ¬ (y = smallY hn 0 (by decide) ∧ C.val.count 4 = 1 ∧ C.val ≠ one 4) := by
    rintro ⟨rfl,h,hne⟩
    exact hne (hf.oneMarker (root_smallY hn 0 (by decide)) h)
  simp [bulkDecode,hf.nonempty,hy,hp,he,h1,h01]

theorem bulk_exceptional {n m : ℕ} (hn : 24 ≤ n) (hm : 8 ≤ m)
    {x : Multiset ℕ} (c : Crossing n m x) (hy : c.y = y₀ n) :
    ∃ p : F n × F m, bulkDecode hn p = x ∧ p.1 ≠ smallY hn 2 (by decide) := by
  let d := fourF (n := m) 2 hm
  have hd : d.val = fours 2 := rfl
  have hd0 : d.val ≠ 0 := by
    intro h
    have := congrArg Multiset.card h
    simp [hd] at this
  have hdd : fours 2 ≠ 0 := hd ▸ hd0
  let z0 := smallY hn 0 (by decide)
  let z1 := smallY hn 1 (by decide)
  let z2 := smallY hn 2 (by decide)
  let zp := prevY hn
  have rk {y z : F n} (e : y = z) : y.val.card = z.val.card :=
    congrArg (fun y : F n => y.val.card) e
  have h0f : z0 ≠ y₀ n := by intro e; have := rk e; simp [z0] at this; omega
  have h1f : z1 ≠ y₀ n := by intro e; have := rk e; simp [z1] at this; omega
  have hpf : zp ≠ y₀ n := by intro e; have := rk e; simp [zp] at this; omega
  have h0p : z0 ≠ zp := by intro e; have := rk e; simp [z0,zp] at this; omega
  have h1p : z1 ≠ zp := by intro e; have := rk e; simp [z1,zp] at this; omega
  have h10 : smallY hn 1 (by decide) ≠ smallY hn 0 (by decide) := by
    intro e; have := rk e; simp at this
  have h02 : z0 ≠ z2 := by intro e; have := rk e; simp [z0,z2] at this
  have h12 : z1 ≠ z2 := by intro e; have := rk e; simp [z1,z2] at this
  have hp2 : zp ≠ z2 := by intro e; have := rk e; simp [zp,z2] at this; omega
  have hf2 : y₀ n ≠ z2 := by intro e; have := rk e; simp [z2] at this; omega
  have hs := y₀_cross c hy
  have hb := c.b_ge
  by_cases e2 : c.b = 2
  · by_cases hU : c.U = 0
    · refine ⟨(z1,d),?_,h12⟩
      simpa [bulkDecode,hd0,hdd,h1f,h1p,h10,z1,hd,hy,e2,hU] using c.reconstruct.symm
    · let C : F m := ⟨c.U,c.U_big,by rw [e2] at hs; omega⟩
      refine ⟨(y₀ n,C),?_,hf2⟩
      simpa [bulkDecode,C,hU,hy,e2] using c.reconstruct.symm
  · have h3 : 3 ≤ c.b := by omega
    have H (q : ℕ) (hq : q < c.b*c.b) : q ∉ c.U := by
      intro h
      exact (Nat.not_lt_of_ge (c.U_ge _ h)) hq
    have no4 : c.U.count 4 = 0 := Multiset.count_eq_zero.mpr (H 4
      (by have := sq_mono h3; omega))
    by_cases e3 : c.b = 3
    · by_cases hU : c.U = 0
      · refine ⟨(z0,d),?_,h02⟩
        simpa [bulkDecode,hd0,hdd,h0f,h0p,z0,hd,hy,e3,hU] using c.reconstruct.symm
      · let V := c.U + fours 1
        let C : F m := ⟨V,big_add c.U_big (big_fours 1),by
          simp [V]; rw [e3] at hs; omega⟩
        have cnt : V.count 4 = 1 := by simp [V,Multiset.count_add,no4]
        have len : V.card = c.U.card + 1 := by simp [V]
        have nz : V ≠ 0 := by
          intro e
          rw [e,Multiset.card_zero] at len
          omega
        have nd : V ≠ fours 2 := by
          intro e
          rw [e,count_fours] at cnt
          omega
        have ns : V ≠ one 4 := by
          intro e
          have h := congrArg (dropFour 1) e
          change dropFour 1 (c.U+fours 1) = dropFour 1 (0+fours 1) at h
          rw [dropFour_add,dropFour_add] at h
          exact hU h
        refine ⟨(z0,C),?_,h02⟩
        have h0p' : smallY hn 0 (by decide) ≠ prevY hn := h0p
        have h0f' : smallY hn 0 (by decide) ≠ y₀ n := h0f
        have hval : C.val = V := rfl
        simp only [bulkDecode,Prod.fst,Prod.snd,hval,z0,ite_eq_right nz,ite_eq_right h0f',
          h0p', false_and, ite_false,nd, and_false, cnt, ns, true_and, and_true, ↓reduceIte,
          V,dropFour_add]
        simpa [hy,e3,hU] using c.reconstruct.symm
    · have h4 : 4 ≤ c.b := by omega
      have step (U : Multiset ℕ) (k : ℕ) (hU : U.count 4 = 0) :
          (U + fours k).count 4 = k := by simp [Multiset.count_add,hU]
      have onPrev (C : F m) (hc : 3 ≤ C.val.count 4) :
          bulkDecode hn (zp,C) = prevDecode (y₀ n).val C.val := by
        have nz : C.val ≠ 0 := by
          intro e
          rw [e,Multiset.count_zero] at hc
          omega
        simp [bulkDecode,nz,hpf,zp,hc]
      by_cases e4 : c.b = 4
      · let C : F m := ⟨c.U+fours 3,big_add c.U_big (big_fours 3),by
          simp only [Multiset.sum_add,sum_fours]; rw [e4] at hs; omega⟩
        have hc : C.val.count 4 = 3 := step _ _ no4
        have no9 : 9 ∉ c.U := H 9 (by rw [e4]; decide)
        refine ⟨(zp,C),?_,hp2⟩
        rw [onPrev C (by omega)]
        simpa [prevDecode,hc,C,dropFour_add,no9,hy,e4] using c.reconstruct.symm
      · by_cases e5 : c.b = 5
        · let V := c.U + one 9
          have hv : V.count 4 = 0 := by simp [V,Multiset.count_add,no4]
          let C : F m := ⟨V+fours 3,big_add (big_add c.U_big
            (big_one ⟨3,by decide,rfl⟩)) (big_fours 3),by
            simp [V]; rw [e5] at hs; omega⟩
          have hc : C.val.count 4 = 3 := step _ _ hv
          have hm9 : 9 ∈ V := by simp [V]
          refine ⟨(zp,C),?_,hp2⟩
          rw [onPrev C (by omega)]
          rw [show C.val = V+fours 3 by rfl]
          have cnt : (V+fours 3).count 4 = 3 := hc
          simp only [prevDecode,cnt,↓reduceIte,dropFour_add,ite_eq_left hm9,V,erase_one_add]
          simpa [hy,e5] using c.reconstruct.symm
        · have h6 : 6 ≤ c.b := by omega
          let r := c.b-2
          let v := r*r
          have hr : 4 ≤ r := by omega
          have hvlt : v < c.b*c.b := sq_strict (by omega)
          have hv4 : 4 ≠ v := by have := sq_mono hr; omega
          let V := c.U + one v
          have hv : V.count 4 = 0 := by simp [V,Multiset.count_add,no4,hv4]
          have hfit : V.sum + 16 ≤ m := by
            simp only [V,Multiset.sum_add,sum_one]
            have he : c.b = r+2 := by omega
            have hdiff : v+20 ≤ c.b*c.b := by rw [he]; dsimp [v]; nlinarith
            omega
          let C : F m := ⟨V+fours 4,big_add (big_add c.U_big
            (big_one ⟨r,by omega,rfl⟩)) (big_fours 4),by
            simp only [Multiset.sum_add,sum_fours]; exact hfit⟩
          have hc : C.val.count 4 = 4 := step _ _ hv
          have hvmin : minPart V = v :=
            minPart_add _ _ (fun q hq => (Nat.le_of_lt hvlt).trans (c.U_ge q hq))
          refine ⟨(zp,C),?_,hp2⟩
          rw [onPrev C (by omega)]
          simp only [prevDecode,hc,show (4:ℕ) ≠ 3 by decide,ite_false]
          change (dropFour 4 (V+fours 4)).erase (minPart (dropFour 4 (V+fours 4))) + _ + _ = _
          rw [dropFour_add,hvmin]
          have hvroot : v.sqrt+2 = c.b := by dsimp [v]; rw [Nat.sqrt_eq]; omega
          rw [hvroot,show V.erase v = c.U by exact erase_one_add _ _]
          simpa [hy] using c.reconstruct.symm

def bulkUnused {n m : ℕ} (hn : 24 ≤ n) (hm : 8 ≤ m) : F n × F m :=
  (smallY hn 2 (by decide),fourF 2 hm)

theorem bulk_cover {n m : ℕ} (hn : 24 ≤ n) (hm : 8 ≤ m) (x : F (n+m)) :
    ∃ p, bulkDecode hn p = x.val ∧ p ≠ bulkUnused hn hm := by
  let y2 := smallY hn 2 (by decide)
  let d := fourF (n := m) 2 hm
  have hd : d.val = fours 2 := rfl
  have hd0 : d.val ≠ 0 := by
    intro h
    have := congrArg Multiset.card h
    simp [hd] at this
  change ∃ p, bulkDecode hn p = x.val ∧ p ≠ (y2,d)
  by_cases hx : x.val.sum ≤ n
  · let y : F n := ⟨x.val,x.property.1,hx⟩
    refine ⟨(y,zeroF m),by simp [bulkDecode,zeroF,y],?_⟩
    exact fun e => hd0 (congrArg (fun p : F n × F m => p.2.val) e).symm
  · obtain ⟨c⟩ := exists_crossing x (by omega)
    by_cases hy : c.y = y₀ n
    · obtain ⟨p,hp,hne⟩ := bulk_exceptional hn hm c hy
      exact ⟨p,hp,fun e => hne (congrArg Prod.fst e)⟩
    · have hs : 3 ≤ root c.y := by
        have := (root_spec c.y).1
        by_contra h
        exact hy ((root_two _).mp (by omega))
      obtain ⟨C,hC,hf⟩ := ordinary_cover c (by omega) hs
      refine ⟨(c.y,C),(bulk_on_ordinary hn c.y C hy hf).trans hC,?_⟩
      intro e
      have ey : c.y = y2 := congrArg Prod.fst e
      have hc : C.val = fours 2 := congrArg (fun p : F n × F m => p.2.val) e
      exact hf.noDouble (by rw [ey]; exact root_smallY hn 2 (by decide)) hc

noncomputable def bulkEncode {n m : ℕ} (hn : 24 ≤ n) (hm : 8 ≤ m)
    (x : F (n+m)) : F n × F m :=
  (bulk_cover hn hm x).choose

theorem bulkEncode_spec {n m : ℕ} (hn : 24 ≤ n) (hm : 8 ≤ m) (x : F (n+m)) :
    bulkDecode hn (bulkEncode hn hm x) = x.val ∧
    bulkEncode hn hm x ≠ bulkUnused hn hm :=
  (bulk_cover hn hm x).choose_spec

theorem bulk_strict {n m : ℕ} (hn : 24 ≤ n) (hm : 8 ≤ m) :
    P (n+m) < P m * P n := by
  have hs := bulkEncode_spec hn hm
  apply cross_card (bulkEncode hn hm) ?_ (bulkUnused hn hm) (fun x => (hs x).2)
  intro x y h
  exact Subtype.ext ((hs x).1.symm.trans ((congrArg (bulkDecode hn) h).trans (hs y).1))

end Roy362601
```

## Thin.lean

```lean
import Code

namespace Roy362601

def slot {n L : ℕ} (h : L ≤ n) : F n :=
  fourF ((n-L)/4) (by omega)

theorem slot_sum {n L : ℕ} (h : L ≤ n) :
    n - (slot h).val.sum = L + (n-L)%4 := by
  change n - (fours ((n-L)/4)).sum = _
  rw [sum_fours]
  omega

theorem y₀_sum (n : ℕ) : n - (y₀ n).val.sum = n%4 := by
  change n - (fours (n/4)).sum = _
  rw [sum_fours]
  omega

theorem slot_sep {n L K : ℕ} (hL : L ≤ n) (hK : K ≤ n) (h : L+4 ≤ K) :
    slot hL ≠ slot hK := by
  intro e
  have e' := congrArg (fun y : F n => n-y.val.sum) e
  rw [slot_sum,slot_sum] at e'
  omega

theorem slot_ne_y₀ {n L : ℕ} (hL : L ≤ n) (h : 4 ≤ L) :
    slot hL ≠ y₀ n := by
  intro e
  have e' := congrArg (fun y : F n => n-y.val.sum) e
  rw [slot_sum,y₀_sum] at e'
  omega

theorem slot_impossible {n m L r : ℕ} (hL : L ≤ n) {x : Multiset ℕ}
    (c : Crossing n m x) (h : m ≤ 7) (hr : r*r ≤ L)
    (hr' : L+10 < (r+1)*(r+1)) : c.y ≠ slot hL := by
  intro e
  have hsum := c.y.property.2
  have hs := slot_sum hL
  rw [← e] at hs
  have hc := c.cross
  have hb : r < c.b := by
    by_contra hn
    have hle := sq_mono (show c.b ≤ r by omega)
    omega
  have hle := sq_mono (show r+1 ≤ c.b by omega)
  have := c.budget
  omega

noncomputable def thinDecode {n m : ℕ} (hn : 52 ≤ n) (p : F n × F m) : Multiset ℕ := by
  classical
  let y := p.1
  exact if p.2.val = 0 then y.val
    else if y = y₀ n then y.val + one 4 + one 4
    else if y = slot (show 25 ≤ n by omega) then (y₀ n).val + one 4
    else if y = slot (show 36 ≤ n by omega) then (y₀ n).val + one 9
    else y.val + one (root y * root y)

def thinUnused {n m : ℕ} (hn : 52 ≤ n) (hm : 4 ≤ m) : F n × F m :=
  (slot (show 49 ≤ n by omega),fourF 1 hm)

theorem thin_cover {m n : ℕ} (hm : 4 ≤ m) (hm' : m ≤ 7) (hn : 52 ≤ n)
    (x : F (n+m)) :
    ∃ p, thinDecode hn p = x.val ∧ p ≠ thinUnused hn hm := by
  classical
  let z25 := slot (show 25 ≤ n by omega)
  let z36 := slot (show 36 ≤ n by omega)
  let z49 := slot (show 49 ≤ n by omega)
  let f := fourF (n := m) 1 (by omega)
  have hf : f.val ≠ 0 := by simp [f,fourF,one]
  have h25 := slot_ne_y₀ (show 25 ≤ n by omega) (by decide)
  have h36 := slot_ne_y₀ (show 36 ≤ n by omega) (by decide)
  have h49 := slot_ne_y₀ (show 49 ≤ n by omega) (by decide)
  have e2536 := slot_sep (show 25 ≤ n by omega) (show 36 ≤ n by omega) (by decide)
  have e2549 := slot_sep (show 25 ≤ n by omega) (show 49 ≤ n by omega) (by decide)
  have e3649 := slot_sep (show 36 ≤ n by omega) (show 49 ≤ n by omega) (by decide)
  change ∃ p, thinDecode hn p = x.val ∧ p ≠ (z49,f)
  by_cases hx : x.val.sum ≤ n
  · let y : F n := ⟨x.val,x.property.1,hx⟩
    refine ⟨(y,zeroF m),?_,?_⟩
    · simp [thinDecode,zeroF,y]
    · intro e
      exact hf (congrArg (fun p : F n × F m => p.2.val) e).symm
  · obtain ⟨c⟩ := exists_crossing x (by omega)
    have hc25 : c.y ≠ z25 := slot_impossible _ c hm' (r := 5) (by decide) (by decide)
    have hc36 : c.y ≠ z36 := slot_impossible _ c hm' (r := 6) (by decide) (by decide)
    have hc49 : c.y ≠ z49 := slot_impossible _ c hm' (r := 7) (by decide) (by decide)
    by_cases he : c.y = y₀ n
    · have hb := c.b_ge
      have hs := y₀_cross c he
      have hlt : c.b < 4 := by
        by_contra h
        have := sq_mono (show 4 ≤ c.b by omega)
        omega
      obtain e | e : c.b = 2 ∨ c.b = 3 := by omega
      · by_cases hu : c.U = 0
        · refine ⟨(z25,f),?_,pair_ne_left e2549 _ _⟩
          simpa [thinDecode,hf,z25,h25,he,e,hu,add_comm] using c.reconstruct.symm
        · have hU : c.U = one 4 := eq_one_four_of_small c.U_big (by rw [e] at hs; omega) hu
          refine ⟨(y₀ n,f),?_,pair_ne_left (Ne.symm h49) _ _⟩
          simpa [thinDecode,hf,he,e,hU,add_comm,add_left_comm,add_assoc] using c.reconstruct.symm
      · have hu : c.U = 0 := by
          by_contra hz
          have := sum_ge_of_nonzero hz c.U_ge
          rw [e] at this hs
          omega
        refine ⟨(z36,f),?_,pair_ne_left e3649 _ _⟩
        simpa [thinDecode,hf,z36,h36,Ne.symm e2536,he,e,hu,add_comm] using c.reconstruct.symm
    · have hroot := (root_spec c.y).1
      have hs : 3 ≤ root c.y := by
        by_contra hh
        exact he ((root_two c.y).mp (by omega))
      have hmin := root_min c.y ⟨c.b_ge,c.cross,c.y_le⟩
      have hsum := (root_spec c.y).2.1
      have hc := c.budget
      have es : c.b = root c.y := by
        by_contra hh
        have hsq := sq_mono (show root c.y+1 ≤ c.b by omega)
        have hgap : root c.y*root c.y+7 ≤ (root c.y+1)*(root c.y+1) := by nlinarith
        omega
      have hu : c.U = 0 := by
        by_contra hz
        have := sum_ge_of_nonzero hz c.U_ge
        have := sq_mono (show 3 ≤ c.b by omega)
        have := c.cross
        omega
      refine ⟨(c.y,f),?_,pair_ne_left hc49 _ _⟩
      simpa [thinDecode,hf,he,hc25,hc36,z25,z36,hu,es,add_comm] using c.reconstruct.symm

noncomputable def thinEncode {m n : ℕ} (hm : 4 ≤ m) (hm' : m ≤ 7) (hn : 52 ≤ n)
    (x : F (n+m)) : F n × F m :=
  (thin_cover hm hm' hn x).choose

theorem thinEncode_spec {m n : ℕ} (hm : 4 ≤ m) (hm' : m ≤ 7) (hn : 52 ≤ n)
    (x : F (n+m)) :
    thinDecode hn (thinEncode hm hm' hn x) = x.val ∧
    thinEncode hm hm' hn x ≠ thinUnused hn hm :=
  (thin_cover hm hm' hn x).choose_spec

theorem thin_strict {m n : ℕ} (hm : 4 ≤ m) (hm' : m ≤ 7) (hn : 52 ≤ n) :
    P (n+m) < P m * P n := by
  have hs := thinEncode_spec hm hm' hn
  apply cross_card (thinEncode hm hm' hn) ?_ (thinUnused hn hm) (fun x => (hs x).2)
  intro x y h
  exact Subtype.ext ((hs x).1.symm.trans ((congrArg (thinDecode hn) h).trans (hs y).1))

end Roy362601
```

## Recurrence.lean

```lean
import Base
import Mathlib.Tactic.IntervalCases

set_option linter.style.haveILetI false

namespace Roy362601

abbrev Allowed (l : List ℕ) (t : ℕ) := {x : Multiset ℕ // (∀ q ∈ x, q ∈ l) ∧ x.sum ≤ t}

@[instance_reducible] noncomputable def allowedFintype (l : List ℕ) (t : ℕ) (hl : ∀ q ∈ l, Big q) :
    Fintype (Allowed l t) := by
  let f : Allowed l t → F t := fun x =>
    ⟨x.val, fun q hq => hl q (x.property.1 q hq), x.property.2⟩
  letI := Finite.of_injective f (fun _ _ e =>
    Subtype.ext (congrArg (fun z : F t => z.val) e))
  exact Fintype.ofFinite _

noncomputable def A (l : List ℕ) (t : ℕ) (hl : ∀ q ∈ l, Big q) : ℕ :=
  letI := allowedFintype l t hl
  Fintype.card (Allowed l t)

theorem allowed_nil (t : ℕ) (hl : ∀ q ∈ ([] : List ℕ), Big q) : A [] t hl = 1 := by
  letI := allowedFintype [] t hl
  unfold A
  apply Fintype.card_eq_one_iff.mpr
  let z : Allowed [] t := ⟨0,by simp⟩
  refine ⟨z, fun x => Subtype.ext ?_⟩
  exact Multiset.eq_zero_of_forall_notMem fun q h => by simpa using x.property.1 q h

def allowed_no {a t : ℕ} {l : List ℕ} (h : a ∉ l) :
    {x : Allowed (a::l) t // a ∉ x.val} ≃ Allowed l t where
  toFun x := ⟨x.val.val, fun q hq =>
    (List.mem_cons.mp (x.val.property.1 q hq)).resolve_left (fun e => x.property (e ▸ hq)),
    x.val.property.2⟩
  invFun x := ⟨⟨x.val, fun q hq => List.mem_cons_of_mem _ (x.property.1 q hq),
                x.property.2⟩, fun ha => h (x.property.1 a ha)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def allowed_yes {a t : ℕ} {l : List ℕ} (h : a ≤ t) :
    {x : Allowed (a::l) t // a ∈ x.val} ≃ Allowed (a::l) (t-a) where
  toFun x := ⟨x.val.val.erase a,
    fun q hq => x.val.property.1 q (Multiset.erase_subset _ _ hq), by
      have e := congrArg Multiset.sum (Multiset.cons_erase x.property)
      simp only [Multiset.sum_cons] at e
      have := x.val.property.2
      omega⟩
  invFun x := ⟨⟨a ::ₘ x.val, fun q hq => by
      rcases Multiset.mem_cons.mp hq with rfl | hq
      · simp
      · exact x.property.1 q hq, by
      rw [Multiset.sum_cons]
      have := x.property.2
      omega⟩, by simp⟩
  left_inv x := Subtype.ext (Subtype.ext (Multiset.cons_erase x.property))
  right_inv x := Subtype.ext (by simp)

theorem allowed_step {a t : ℕ} {l : List ℕ} (h : a ∉ l)
    (hl : ∀ q ∈ a::l, Big q) :
    A (a::l) t hl = A l t (fun q hq => hl q (List.mem_cons_of_mem _ hq)) +
      if a ≤ t then A (a::l) (t-a) hl else 0 := by
  classical
  letI := allowedFintype (a::l) t hl
  letI := allowedFintype l t (fun q hq => hl q (List.mem_cons_of_mem _ hq))
  letI := allowedFintype (a::l) (t-a) hl
  let no := allowed_no (t := t) h
  have hn := Fintype.card_congr no
  have e := (Equiv.sumCompl (fun x : Allowed (a::l) t => a ∉ x.val)).symm
  have he := Fintype.card_congr e
  rw [Fintype.card_sum, hn] at he
  simp only [not_not] at he
  unfold A
  by_cases ht : a ≤ t
  · rw [ite_eq_left ht]
    rwa [Fintype.card_congr (allowed_yes (l := l) ht)] at he
  · haveI : IsEmpty {x : Allowed (a::l) t // a ∈ x.val} :=
      ⟨fun x => ht ((Multiset.le_sum_of_mem x.property).trans x.val.property.2)⟩
    rw [ite_eq_right ht]
    have hz : Fintype.card {x : Allowed (a::l) t // a ∈ x.val} = 0 := Fintype.card_eq_zero
    exact he.trans (congrArg (_ + ·) hz)

def coeff : List ℕ → ℕ → ℕ
  | [], _ => 1
  | a::l, t => if 0 < a ∧ a ≤ t then coeff l t + coeff (a::l) (t-a)
               else coeff l t
termination_by l t => (l.length,t)
decreasing_by all_goals (simp_wf; omega)

theorem coeff_spec (l : List ℕ) (t : ℕ) (hl : ∀ q ∈ l, Big q) (hd : l.Nodup) :
    A l t hl = coeff l t := by
  induction l generalizing t with
  | nil => rw [coeff]; exact allowed_nil t hl
  | cons a l ih =>
    obtain ⟨ha,hd'⟩ := List.nodup_cons.mp hd
    have hp : 0 < a := by
      have := big_four (hl a (by simp))
      omega
    induction t using Nat.strong_induction_on with
    | h t it =>
      rw [allowed_step ha, coeff, ih _ _ hd']
      by_cases ht : a ≤ t
      · rw [ite_eq_left ht, ite_eq_left ⟨hp,ht⟩, it (t-a) (by omega)]
      · rw [ite_eq_right ht, ite_eq_right (fun h => ht h.2), Nat.add_zero]

def parts58 : List ℕ := [4,9,16,25,36,49]

theorem parts58_big : ∀ q ∈ parts58, Big q := by
  intro q hq
  simp [parts58] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact ⟨2,by decide,rfl⟩ | exact ⟨3,by decide,rfl⟩ |
    exact ⟨4,by decide,rfl⟩ | exact ⟨5,by decide,rfl⟩ |
    exact ⟨6,by decide,rfl⟩ | exact ⟨7,by decide,rfl⟩

theorem parts58_complete {q : ℕ} (h : Big q) (hq : q ≤ 58) : q ∈ parts58 := by
  obtain ⟨r,hr,rfl⟩ := h
  have hr' : r < 8 := by
    by_contra hn
    have := sq_mono (show 8 ≤ r by omega)
    omega
  interval_cases r <;> decide

theorem P_coeff {t : ℕ} (ht : t ≤ 58) : P t = coeff parts58 t := by
  letI := allowedFintype parts58 t parts58_big
  let e : F t ≃ Allowed parts58 t :=
    ⟨fun x => ⟨x.val,fun q hq => parts58_complete (x.property.1 q hq)
      (((Multiset.le_sum_of_mem hq).trans x.property.2).trans ht),x.property.2⟩,
     fun x => ⟨x.val,fun q hq => parts58_big q (x.property.1 q hq),x.property.2⟩,
     fun _ => rfl,fun _ => rfl⟩
  rw [← card_F, Fintype.card_congr e]
  exact coeff_spec parts58 t parts58_big (by decide)

def coeffFuel : ℕ → List ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | _+1, [], _ => 1
  | k+1, a::l, t =>
    if 0 < a ∧ a ≤ t then coeffFuel k l t + coeffFuel k (a::l) (t-a)
    else coeffFuel k l t

theorem coeffFuel_spec (k : ℕ) (l : List ℕ) (t : ℕ) (h : l.length + t < k) :
    coeffFuel k l t = coeff l t := by
  induction k generalizing l t with
  | zero => omega
  | succ k ih =>
    cases l with
    | nil => rw [coeffFuel,coeff]
    | cons a l =>
      simp only [List.length_cons] at h
      rw [coeffFuel,coeff,ih l t (by omega)]
      split
      · rename_i ha
        have := ha.1
        have := ha.2
        rw [ih _ _ (by simp only [List.length_cons]; omega)]
      · rfl

def C (t : ℕ) := coeffFuel (t+7) parts58 t

theorem P_C {t : ℕ} (ht : t ≤ 58) : P t = C t := by
  rw [P_coeff ht,C,coeffFuel_spec _ _ _ (by simp [parts58]; omega)]

example : C 58 = 163 := by decide

end Roy362601
```

## FiniteSigns.lean

```lean
import Recurrence

namespace Roy362601

def equalValues : ℕ → List ℕ
  | 1 => [1,2,4,5,6,9,10,13,14,18,22]
  | 2 => [4,5,9,13]
  | 3 => [4]
  | 4 => [5,6,7]
  | 5 => [5,6,8,11,15]
  | 6 => [8,10,12,14]
  | 7 => [8,9,12,13,19]
  | _ => []

def EqRow (m n : ℕ) : Prop := n ∈ equalValues m

def FailRow (m n : ℕ) : Prop :=
  match m with
  | 1 => n ∉ [1,2,4,5,6,9,10,13,14,18,22]
  | 2 => n ∉ [1,4,5,9,13]
  | 3 => n ∉ [1,2,4]
  | 5 => n ∈ [7]
  | 6 => n ∈ [6,7,11,15]
  | 7 => n ∈ [7,10,11,14,15]
  | _ => False

instance (m n : ℕ) : Decidable (EqRow m n) := by
  unfold EqRow
  infer_instance

instance (m n : ℕ) : Decidable (FailRow m n) := by
  unfold FailRow
  split <;> infer_instance

def Signs (Q : ℕ → ℕ) (m n : ℕ) : Prop :=
  (Q m * Q n = Q (m+n) ↔ EqRow m n) ∧
  (Q m * Q n < Q (m+n) ↔ FailRow m n) ∧
  (Q (m+n) < Q m * Q n ↔ ¬ EqRow m n ∧ ¬ FailRow m n)

instance (Q : ℕ → ℕ) (m n : ℕ) : Decidable (Signs Q m n) := by
  unfold Signs
  infer_instance

def FiniteRegion (m n : ℕ) : Prop :=
  0 < m ∧ m ≤ n ∧ ((m ≤ 3 ∧ n < 23) ∨
    (4 ≤ m ∧ m ≤ 7 ∧ n < 52) ∨ (8 ≤ m ∧ n < 24))

instance (m n : ℕ) : Decidable (FiniteRegion m n) := by
  unfold FiniteRegion
  infer_instance

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem finite_certificate :
    ∀ m : Fin 24, ∀ n : Fin 52, FiniteRegion m.val n.val → Signs C m.val n.val := by
  decide

theorem finite_signs {m n : ℕ} (h : FiniteRegion m n) : Signs P m n := by
  rcases h with ⟨hp,hm,h⟩
  have ht : m+n ≤ 58 := by omega
  have hc := finite_certificate ⟨m,by omega⟩ ⟨n,by omega⟩ ⟨hp,hm,h⟩
  unfold Signs at hc ⊢
  rwa [P_C (show m ≤ 58 by omega), P_C (show n ≤ 58 by omega), P_C ht]

theorem row_none_ge8 {m n : ℕ} (h : 8 ≤ m) : ¬ EqRow m n ∧ ¬ FailRow m n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  simp [EqRow,equalValues,FailRow, Nat.add_comm 8]

theorem row_none_mid {m n : ℕ} (hm : 4 ≤ m) (hm' : m ≤ 7)
    (hn : 52 ≤ n) : ¬ EqRow m n ∧ ¬ FailRow m n := by
  interval_cases m <;> simp [EqRow,equalValues,FailRow] <;> omega

theorem row_small_tail {m n : ℕ} (hm : 0 < m) (hm' : m ≤ 3)
    (hn : 23 ≤ n) : ¬ EqRow m n ∧ FailRow m n := by
  interval_cases m <;> simp [EqRow,equalValues,FailRow] <;> omega

theorem signs_of_strict {m n : ℕ} (h : P (m+n) < P m * P n)
    (he : ¬ EqRow m n) (hf : ¬ FailRow m n) : Signs P m n := by
  unfold Signs
  simp [he,hf,Nat.ne_of_gt h,Nat.not_lt_of_ge (Nat.le_of_lt h),h]

theorem signs_of_failure {m n : ℕ} (h : P m * P n < P (m+n))
    (he : ¬ EqRow m n) (hf : FailRow m n) : Signs P m n := by
  unfold Signs
  simp [he,hf,Nat.ne_of_lt h,Nat.not_lt_of_ge (Nat.le_of_lt h),h]

end Roy362601
```

## Small.lean

```lean
import Code
import FiniteSigns

namespace Roy362601

def gaps : List ℕ := [1,2,3,5,6,7,10,11,14,15,19,23]
def Representable (t : ℕ) : Prop := ∃ x : F t, x.val.sum = t

theorem represent_4_9 (a b : ℕ) : Representable (4*a+9*b) := by
  let r := Multiset.replicate b 9
  let v := fours a + r
  have hv : v.sum = 4*a+9*b := by simp [v,r,Nat.mul_comm]
  refine ⟨⟨v,?_,hv.le⟩,hv⟩
  intro q hq
  rcases Multiset.mem_add.mp hq with h | h
  · exact big_fours _ _ h
  · rw [(Multiset.mem_replicate.mp h).2]
    exact ⟨3,by decide,rfl⟩

theorem represent_add_four {t : ℕ} (h : Representable t) : Representable (t+4) := by
  obtain ⟨x,hx⟩ := h
  let v := x.val + fours 1
  have hv : v.sum = t+4 := by simp only [v,Multiset.sum_add,sum_fours,hx,Nat.mul_one]
  refine ⟨⟨v,?_,hv.le⟩,hv⟩
  intro q hq
  rcases Multiset.mem_add.mp hq with h | h
  · exact x.property.1 _ h
  · exact big_fours _ _ h

theorem represent_ge24 (t : ℕ) (h : 24 ≤ t) : Representable t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t ≤ 27
    · interval_cases t
      · exact represent_4_9 6 0
      · exact represent_4_9 4 1
      · exact represent_4_9 2 2
      · exact represent_4_9 0 3
    · have e : t-4+4 = t := by omega
      exact e ▸ represent_add_four (ih (t-4) (by omega) (by omega))

theorem gap_certificate :
    ∀ i : Fin 23, C i.val < C (i.val+1) ↔ i.val+1 ∉ gaps := by decide

theorem succ_gap (t : ℕ) : P t < P (t+1) ↔ t+1 ∉ gaps := by
  by_cases ht : t < 23
  · rw [P_C (show t ≤ 58 by omega),P_C (show t+1 ≤ 58 by omega)]
    exact gap_certificate ⟨t,ht⟩
  · have hrep := represent_ge24 (t+1) (by omega)
    have hs := (P_succ_lt_iff t).mpr hrep
    have hg : t+1 ∉ gaps := by simp [gaps]; omega
    simp [hs,hg]

theorem represent_iff_not_gap {t : ℕ} (ht : 0 < t) : Representable t ↔ t ∉ gaps := by
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [hi,Nat.succ_eq_add_one]
  exact (P_succ_lt_iff i).symm.trans (succ_gap i)

theorem P_eq_window (n m : ℕ) :
    P n = P (n+m) ↔ ∀ t, n < t → t ≤ n+m → t ∈ gaps := by
  constructor
  · intro he t ht hu
    by_contra h
    have e : t-1+1=t := by omega
    have hlt := (succ_gap (t-1)).mpr (by rwa [e])
    rw [e] at hlt
    have h₁ := P_mono (show n ≤ t-1 by omega)
    have h₂ := P_mono hu
    omega
  · intro h
    induction m with
    | zero => simp
    | succ m ih =>
      have he := ih (fun t ht hu => h t ht (by omega))
      have hg := h (n+m+1) (by omega) (by omega)
      have hlt : ¬P (n+m) < P (n+m+1) := fun hlt => (succ_gap _).mp hlt hg
      have hle := P_mono (show n+m ≤ n+m+1 by omega)
      change P n = P (n+m+1)
      omega

theorem small_P_one {m : ℕ} (hm : m ≤ 3) : P m = 1 := by
  rw [P_C (show m ≤ 58 by omega)]
  interval_cases m <;> decide

theorem small_tail {m n : ℕ} (hm : 0 < m) (hm' : m ≤ 3) (hn : 23 ≤ n) :
    P m * P n < P (m+n) := by
  rw [small_P_one hm',one_mul]
  have hs := (P_succ_lt_iff n).mpr (represent_ge24 (n+1) (by omega))
  exact hs.trans_le (P_mono (by omega))

theorem small_window_table {m n : ℕ} (hm : 0 < m) (hm' : m ≤ 3) (h : m ≤ n) :
    (∀ t, n < t → t ≤ n+m → t ∈ gaps) ↔ EqRow m n := by
  rw [← P_eq_window]
  by_cases hn : n < 23
  · have hsign := (finite_signs ⟨hm,h,Or.inl ⟨hm',hn⟩⟩).1
    simpa [small_P_one hm',Nat.add_comm] using hsign
  · have hfail := small_tail hm hm' (by omega : 23 ≤ n)
    have hne := (row_small_tail hm hm' (by omega : 23 ≤ n)).1
    rw [small_P_one hm',one_mul,Nat.add_comm] at hfail
    simp [hne,Nat.ne_of_lt hfail]

end Roy362601
```

## Table.lean

```lean
import Bulk
import Thin
import Small

namespace Roy362601

theorem sign_table_ordered {m n : ℕ} (hp : 0 < m) (hmn : m ≤ n) :
    Signs P m n := by
  by_cases hm3 : m ≤ 3
  · by_cases hn : n < 23
    · exact finite_signs ⟨hp,hmn,Or.inl ⟨hm3,hn⟩⟩
    · obtain ⟨he,hf⟩ := row_small_tail hp hm3 (by omega : 23 ≤ n)
      exact signs_of_failure (small_tail hp hm3 (by omega)) he hf
  · by_cases hm7 : m ≤ 7
    · by_cases hn : n < 52
      · exact finite_signs ⟨hp,hmn,Or.inr (Or.inl ⟨by omega,hm7,hn⟩)⟩
      · obtain ⟨he,hf⟩ := row_none_mid (by omega : 4 ≤ m) hm7 (by omega : 52 ≤ n)
        have h := thin_strict (by omega : 4 ≤ m) hm7 (by omega : 52 ≤ n)
        rw [Nat.add_comm] at h
        exact signs_of_strict h he hf
    · by_cases hn : n < 24
      · exact finite_signs ⟨hp,hmn,Or.inr (Or.inr ⟨by omega,hn⟩)⟩
      · obtain ⟨he,hf⟩ := row_none_ge8 (m := m) (n := n) (by omega)
        have h := bulk_strict (by omega : 24 ≤ n) (by omega : 8 ≤ m)
        rw [Nat.add_comm] at h
        exact signs_of_strict h he hf

theorem ordered_eq {m n : ℕ} (hp : 0 < m) (hmn : m ≤ n) :
    P m * P n = P (m+n) ↔ EqRow m n := (sign_table_ordered hp hmn).1

theorem ordered_lt {m n : ℕ} (hp : 0 < m) (hmn : m ≤ n) :
    P m * P n < P (m+n) ↔ FailRow m n := (sign_table_ordered hp hmn).2.1

theorem ordered_gt {m n : ℕ} (hp : 0 < m) (hmn : m ≤ n) :
    P (m+n) < P m * P n ↔ ¬ EqRow m n ∧ ¬ FailRow m n := (sign_table_ordered hp hmn).2.2

theorem sign_table {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (P a * P b = P (a+b) ↔ EqRow (min a b) (max a b)) ∧
    (P a * P b < P (a+b) ↔ FailRow (min a b) (max a b)) ∧
    (P (a+b) < P a * P b ↔ ¬ EqRow (min a b) (max a b) ∧
                            ¬ FailRow (min a b) (max a b)) := by
  rcases le_total a b with h | h
  · simpa [min_eq_left h,max_eq_right h,Signs] using sign_table_ordered ha h
  · simpa [min_eq_right h,max_eq_left h,Signs,Nat.mul_comm,Nat.add_comm] using sign_table_ordered hb h

theorem square_partition_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    P a * P b = P (a+b) ↔ EqRow (min a b) (max a b) := (sign_table ha hb).1

theorem square_partition_lt {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    P a * P b < P (a+b) ↔ FailRow (min a b) (max a b) := (sign_table ha hb).2.1

theorem square_partition_gt {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    P (a+b) < P a * P b ↔ ¬ EqRow (min a b) (max a b) ∧
                            ¬ FailRow (min a b) (max a b) := (sign_table ha hb).2.2

end Roy362601
```

## Certificates.lean

```lean
import Table
import Increment

namespace Roy362601

theorem crossing_slack {n m : ℕ} {x : Multiset ℕ} (c : Crossing n m x) :
    let h := n-c.y.val.sum
    h < c.b*c.b ∧ c.U.sum + c.b*c.b-h ≤ m := by
  dsimp
  have h := c.y.property.2
  have h' := c.cross
  have h'' := c.budget
  omega

theorem thin_second_coordinate {m : ℕ} (hm : m ≤ 7) (x : F m) :
    x.val = 0 ∨ x.val = one 4 := by
  by_cases h : x.val = 0
  · exact Or.inl h
  · exact Or.inr (eq_one_four_of_small x.property.1 (by have := x.property.2; omega) h)

theorem bulk_encode_injective {n m : ℕ} (hn : 24 ≤ n) (hm : 8 ≤ m) :
    Function.Injective (bulkEncode hn hm) := by
  intro x y e
  apply Subtype.ext
  have h := congrArg (bulkDecode hn) e
  rwa [(bulkEncode_spec hn hm x).1,(bulkEncode_spec hn hm y).1] at h

theorem thin_encode_injective {n m : ℕ} (hm : 4 ≤ m) (hm' : m ≤ 7) (hn : 52 ≤ n) :
    Function.Injective (thinEncode hm hm' hn) := by
  intro x y e
  apply Subtype.ext
  have h := congrArg (thinDecode hn) e
  rwa [(thinEncode_spec hm hm' hn x).1,(thinEncode_spec hm hm' hn y).1] at h

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem coefficient_list :
    List.ofFn (fun i : Fin 59 => P i.val) =
    [1,1,1,1,2,2,2,2,3,4,4,4,5,6,6,6,8,9,10,10,
     12,13,14,14,16,19,20,21,23,26,27,28,31,34,37,38,43,46,49,50,
     55,60,63,66,71,78,81,84,90,98,104,107,116,124,132,135,144,154,163] := by
  have e : (fun i : Fin 59 => P i.val) = fun i : Fin 59 => C i.val :=
    funext fun i => P_C (by have := i.isLt; omega)
  rw [e]
  decide

theorem restricted_sign_table [DecidablePred Sq] {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    let R (t : ℕ) := (Nat.Partition.restricted t Sq).card
    (R a * R b = R (a+b) ↔ EqRow (min a b) (max a b)) ∧
    (R a * R b < R (a+b) ↔ FailRow (min a b) (max a b)) ∧
    (R (a+b) < R a * R b ↔ ¬ EqRow (min a b) (max a b) ∧
                            ¬ FailRow (min a b) (max a b)) := by
  dsimp only
  rw [← P_restricted a,← P_restricted b,← P_restricted (a+b)]
  exact sign_table ha hb

end Roy362601
```

## Audit.lean

```lean
import Certificates

open Roy362601

#print axioms Roy362601.Sq
#print axioms Roy362601.Big
#print axioms Roy362601.P
#print axioms Roy362601.F
#print axioms Roy362601.padding
#print axioms Roy362601.card_F
#print axioms Roy362601.P_restricted
#print axioms Roy362601.P_mono
#print axioms Roy362601.P_succ_lt_iff
#print axioms Roy362601.removeOne
#print axioms Roy362601.noOnes
#print axioms Roy362601.P_add_exact
#print axioms Roy362601.list_cut
#print axioms Roy362601.earlier_suffix
#print axioms Roy362601.exists_crossing
#print axioms Roy362601.Crossing.offset
#print axioms Roy362601.crossing_slack
#print axioms Roy362601.root_two
#print axioms Roy362601.ordinary_cover
#print axioms Roy362601.bulk_on_ordinary
#print axioms Roy362601.bulk_exceptional
#print axioms Roy362601.bulk_cover
#print axioms Roy362601.bulkEncode
#print axioms Roy362601.bulkEncode_spec
#print axioms Roy362601.bulk_encode_injective
#print axioms Roy362601.bulk_strict
#print axioms Roy362601.slot_sum
#print axioms Roy362601.slot_impossible
#print axioms Roy362601.thin_second_coordinate
#print axioms Roy362601.thin_cover
#print axioms Roy362601.thinEncode
#print axioms Roy362601.thinEncode_spec
#print axioms Roy362601.thin_encode_injective
#print axioms Roy362601.thin_strict
#print axioms Roy362601.allowed_step
#print axioms Roy362601.coeff_spec
#print axioms Roy362601.coeffFuel_spec
#print axioms Roy362601.P_C
#print axioms Roy362601.coefficient_list
#print axioms Roy362601.finite_certificate
#print axioms Roy362601.finite_signs
#print axioms Roy362601.represent_ge24
#print axioms Roy362601.represent_iff_not_gap
#print axioms Roy362601.P_eq_window
#print axioms Roy362601.small_window_table
#print axioms Roy362601.small_tail
#print axioms Roy362601.EqRow
#print axioms Roy362601.FailRow
#print axioms Roy362601.sign_table_ordered
#print axioms Roy362601.ordered_eq
#print axioms Roy362601.ordered_lt
#print axioms Roy362601.ordered_gt
#print axioms Roy362601.sign_table
#print axioms Roy362601.square_partition_eq
#print axioms Roy362601.square_partition_lt
#print axioms Roy362601.square_partition_gt
#print axioms Roy362601.restricted_sign_table

#check Roy362601.Sq
#check Roy362601.Big
#check Roy362601.P
#check Roy362601.F
#check Roy362601.padding
#check Roy362601.card_F
#check Roy362601.P_restricted
#check Roy362601.P_mono
#check Roy362601.P_succ_lt_iff
#check Roy362601.removeOne
#check Roy362601.noOnes
#check Roy362601.P_add_exact
#check Roy362601.list_cut
#check Roy362601.earlier_suffix
#check Roy362601.exists_crossing
#check Roy362601.Crossing.offset
#check Roy362601.crossing_slack
#check Roy362601.root_two
#check Roy362601.ordinary_cover
#check Roy362601.bulk_on_ordinary
#check Roy362601.bulk_exceptional
#check Roy362601.bulk_cover
#check Roy362601.bulkEncode
#check Roy362601.bulkEncode_spec
#check Roy362601.bulk_encode_injective
#check Roy362601.bulk_strict
#check Roy362601.slot_sum
#check Roy362601.slot_impossible
#check Roy362601.thin_second_coordinate
#check Roy362601.thin_cover
#check Roy362601.thinEncode
#check Roy362601.thinEncode_spec
#check Roy362601.thin_encode_injective
#check Roy362601.thin_strict
#check Roy362601.allowed_step
#check Roy362601.coeff_spec
#check Roy362601.coeffFuel_spec
#check Roy362601.P_C
#check Roy362601.coefficient_list
#check Roy362601.finite_certificate
#check Roy362601.finite_signs
#check Roy362601.represent_ge24
#check Roy362601.represent_iff_not_gap
#check Roy362601.P_eq_window
#check Roy362601.small_window_table
#check Roy362601.small_tail
#check Roy362601.EqRow
#check Roy362601.FailRow
#check Roy362601.sign_table_ordered
#check Roy362601.ordered_eq
#check Roy362601.ordered_lt
#check Roy362601.ordered_gt
#check Roy362601.sign_table
#check Roy362601.square_partition_eq
#check Roy362601.square_partition_lt
#check Roy362601.square_partition_gt
#check Roy362601.restricted_sign_table

```

