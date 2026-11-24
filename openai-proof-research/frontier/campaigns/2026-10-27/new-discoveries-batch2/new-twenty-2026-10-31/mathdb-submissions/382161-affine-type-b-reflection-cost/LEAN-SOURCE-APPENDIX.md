# Lean source appendix

### `AffineBStatement.lean`

```lean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card

namespace AffineB

open scoped BigOperators

abbrev PermZ := Equiv.Perm ℤ

def period (n : ℕ) : ℤ := 2 * (n : ℤ) + 2

def AffSigned (n : ℕ) (w : PermZ) : Prop :=
  (∀ i : ℤ, w (-i) = -w i) ∧
  (∀ i : ℤ, w (i + period n) = w i + period n)

def negCrossing (w : PermZ) : Set ℤ := {i | 0 < i ∧ w i < 0}

noncomputable def AffB (n : ℕ) (w : PermZ) : Prop :=
  AffSigned n w ∧ Even (negCrossing w).ncard

def swapCopy (n : ℕ) (x y a b : ℤ) : Prop :=
  ∃ k : ℤ, let s := k * period n
    (a = x+s ∧ b = y+s) ∨ (a = y+s ∧ b = x+s) ∨
    (a = -x+s ∧ b = -y+s) ∨ (a = -y+s ∧ b = -x+s)

def BRefl (n : ℕ) (t : PermZ) : Prop :=
  AffB n t ∧ ∃ x y : ℤ, x ≠ y ∧
    (∀ a b : ℤ, swapCopy n x y a b → t a = b) ∧
    (∀ a : ℤ, (¬ ∃ b : ℤ, swapCopy n x y a b) → t a = a)

def dis (n : ℕ) (w : PermZ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, Int.natAbs (w (i : ℤ) - i)

def Good (w : PermZ) (j : ℕ) : Prop :=
  ∀ i : ℤ, i.natAbs ≤ j ↔ (w i).natAbs ≤ j

def negPrefix (w : PermZ) (j : ℕ) : ℕ :=
  ((Finset.Icc 1 j).filter (fun i : ℕ => w (i : ℤ) < 0)).card

def VeryGood (w : PermZ) (j : ℕ) : Prop :=
  Good w j ∧ Even (negPrefix w j)

noncomputable def blC (n : ℕ) (w : PermZ) : ℕ := by
  classical
  exact 1 + ((Finset.Ico 1 n).filter (Good w)).card

noncomputable def blB (n : ℕ) (w : PermZ) : ℕ := by
  classical
  exact 1 + ((Finset.Ico 1 n).filter (VeryGood w)).card

def Costs2 (n : ℕ) (w : PermZ) : Set ℕ :=
  {c | ∃ ts : List PermZ, (∀ t ∈ ts, BRefl n t) ∧
      ts.prod = w ∧ (ts.map (dis n)).sum = c}

def Conjecture42 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ w : PermZ, AffB n w →
    IsLeast (Costs2 n w) (dis n w + 2 * (blC n w - blB n w))

theorem blB_le_blC (n : ℕ) (w : PermZ) : blB n w ≤ blC n w := by
  classical
  unfold blB blC
  apply Nat.add_le_add_left
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2.1⟩

def OddGood (w : PermZ) (j : ℕ) : Prop := Good w j ∧ ¬ Even (negPrefix w j)

noncomputable def oddGoods (n : ℕ) (w : PermZ) : Finset ℕ := by
  classical
  exact (Finset.Ico 1 n).filter (OddGood w)

theorem block_difference (n : ℕ) (w : PermZ) :
    blC n w - blB n w = (oddGoods n w).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.Ico 1 n).filter (Good w)) (fun j => Even (negPrefix w j))
  simp only [Finset.filter_filter] at h
  have hc : ((Finset.Ico 1 n).filter (Good w)).card =
      ((Finset.Ico 1 n).filter (VeryGood w)).card + (oddGoods n w).card := by
    unfold oddGoods VeryGood OddGood
    convert h.symm using 2 <;> congr 1 <;> ext j <;> simp only [Finset.mem_filter]
  change 1 + ((Finset.Ico 1 n).filter (Good w)).card -
      (1 + ((Finset.Ico 1 n).filter (VeryGood w)).card) = (oddGoods n w).card
  omega

end AffineB
```

### `AffineBBasics.lean`

```lean
import AffineBStatement

namespace AffineB

open scoped BigOperators

theorem period_pos (n : ℕ) : 0 < period n := by unfold period; omega

theorem AffSigned.zero {n : ℕ} {w : PermZ} (hw : AffSigned n w) : w 0 = 0 := by
  have h := hw.1 0
  rw [neg_zero] at h
  omega

theorem AffSigned.sub_period {n : ℕ} {w : PermZ} (hw : AffSigned n w) (x : ℤ) :
    w (x - period n) = w x - period n := by
  have h := hw.2 (x - period n)
  rw [sub_add_cancel] at h
  omega

theorem AffSigned.translate {n : ℕ} {w : PermZ} (hw : AffSigned n w) (x k : ℤ) :
    w (x + k * period n) = w x + k * period n := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [add_mul, one_mul, ← add_assoc, hw.2, ih, add_assoc]
  | pred k ih =>
    rw [sub_mul, one_mul, ← add_sub_assoc,
      hw.sub_period, ih, add_sub_assoc]

theorem AffSigned.mirror {n : ℕ} {w : PermZ} (hw : AffSigned n w) (x : ℤ) :
    w (period n - x) = period n - w x := by
  rw [sub_eq_add_neg, add_comm, hw.2, hw.1, add_comm, ← sub_eq_add_neg]

theorem AffSigned.midpoint {n : ℕ} {w : PermZ} (hw : AffSigned n w) :
    w ((n : ℤ) + 1) = (n : ℤ) + 1 := by
  have h := hw.mirror ((n : ℤ) + 1)
  unfold period at h
  rw [show 2 * (n : ℤ) + 2 - ((n : ℤ) + 1) = (n : ℤ) + 1 by omega] at h
  omega

theorem affSigned_one (n : ℕ) : AffSigned n (1 : PermZ) := by
  constructor <;> intro x <;> rfl

theorem AffSigned.mul {n : ℕ} {u t : PermZ} (hu : AffSigned n u) (ht : AffSigned n t) :
    AffSigned n (u * t) := by
  constructor
  · intro x
    change u (t (-x)) = -u (t x)
    rw [ht.1, hu.1]
  · intro x
    change u (t (x + period n)) = u (t x) + period n
    rw [ht.2, hu.2]

theorem AffSigned.inverse {n : ℕ} {w : PermZ} (hw : AffSigned n w) :
    AffSigned n w.symm := by
  constructor
  · intro x
    apply w.injective
    rw [w.apply_symm_apply, hw.1, w.apply_symm_apply]
  · intro x
    apply w.injective
    rw [w.apply_symm_apply, hw.2, w.apply_symm_apply]

theorem AffSigned.displacement_neg {n : ℕ} {w : PermZ} (hw : AffSigned n w) (x : ℤ) :
    w (-x) - (-x) = -(w x - x) := by rw [hw.1]; omega

theorem AffSigned.bound {n : ℕ} {w : PermZ} (hw : AffSigned n w) :
    ∃ D : ℕ, ∀ x : ℤ, (w x - x).natAbs ≤ D := by
  let s := Finset.Ico (0 : ℤ) (period n)
  refine ⟨s.sup (fun x => (w x - x).natAbs), fun x => ?_⟩
  have hx : x % period n ∈ s :=
    Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (period_pos n).ne', Int.emod_lt_of_pos _ (period_pos n)⟩
  have h := Finset.le_sup (f := fun x => (w x - x).natAbs) hx
  have he : x % period n + (x / period n) * period n = x := by simpa only [mul_comm] using Int.emod_add_mul_ediv x (period n)
  have htranslate := hw.translate (x % period n) (x / period n)
  rw [he] at htranslate
  convert h using 2
  omega

theorem AffSigned.negCrossing_finite {n : ℕ} {w : PermZ} (hw : AffSigned n w) :
    (negCrossing w).Finite := by
  obtain ⟨D, hD⟩ := hw.bound
  apply (Finset.Icc (1 : ℤ) (D : ℤ)).finite_toSet.subset
  intro x hx
  change 0 < x ∧ w x < 0 at hx
  have h := hD x
  simpa only [Finset.mem_coe, Finset.mem_Icc] using
    (show 1 ≤ x ∧ x ≤ (D : ℤ) by omega)

theorem Good.of_mapsTo {w : PermZ} {j : ℕ}
    (h : ∀ i : ℤ, i.natAbs ≤ j → (w i).natAbs ≤ j) : Good w j := by
  let s : Finset ℤ := Finset.Icc (-(j : ℤ)) j
  have hs (i : ℤ) : i ∈ s ↔ i.natAbs ≤ j := by
    change _ ∈ Finset.Icc _ _ ↔ _
    rw [Finset.mem_Icc]
    omega
  have he : s.map w.toEmbedding = s := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
      exact (hs _).mpr (h a ((hs a).mp ha))
    · simp
  intro i
  refine ⟨h i, fun hi => ?_⟩
  have hm : w i ∈ s.map w.toEmbedding := by rw [he]; exact (hs _).mpr hi
  obtain ⟨a, ha, ha'⟩ := Finset.mem_map.mp hm
  exact (hs _).mp (w.injective ha' ▸ ha)

theorem AffSigned.good_iff_window {n : ℕ} {w : PermZ} (hw : AffSigned n w) (j : ℕ) :
    Good w j ↔ ∀ i ∈ Finset.Icc 1 j, (w (i : ℤ)).natAbs ≤ j := by
  constructor
  · intro h i hi
    exact (h i).mp (by simpa using (Finset.mem_Icc.mp hi).2)
  · intro h
    apply Good.of_mapsTo
    intro x hx
    have hpos (y : ℤ) (hy : 0 < y) (hyj : y.natAbs ≤ j) : (w y).natAbs ≤ j := by
      have hi := h y.toNat (Finset.mem_Icc.mpr (by omega))
      rwa [Int.toNat_of_nonneg hy.le] at hi
    rcases lt_trichotomy x 0 with hn | rfl | hp
    · have hi := hpos (-x) (by omega) (by simpa using hx)
      simpa only [hw.1, Int.natAbs_neg] using hi
    · simp [hw.zero]
    · exact hpos x hp hx

theorem BRefl.involutive {n : ℕ} {t : PermZ} (ht : BRefl n t) :
    Function.Involutive t := by
  obtain ⟨_, x, y, _, hswap, hfix⟩ := ht
  intro a
  by_cases h : ∃ b, swapCopy n x y a b
  · obtain ⟨b, hb⟩ := h
    have hba : swapCopy n x y b a := by
      obtain ⟨k, h | h | h | h⟩ := hb
      exacts [⟨k, Or.inr (Or.inl ⟨h.2, h.1⟩)⟩, ⟨k, Or.inl ⟨h.2, h.1⟩⟩,
        ⟨k, Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))⟩, ⟨k, Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))⟩]
    rw [hswap _ _ hb, hswap _ _ hba]
  · rw [hfix a h, hfix a h]

end AffineB
```

### `AffineBCuts.lean`

```lean
import AffineBBasics
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace AffineB

open scoped BigOperators

def Right (w : PermZ) (j : ℤ) : Set ℤ := {p | p ≤ j ∧ j < w p}
def Left (w : PermZ) (j : ℤ) : Set ℤ := {p | w p ≤ j ∧ j < p}

noncomputable def rightCount (w : PermZ) (j : ℤ) : ℕ := (Right w j).ncard
noncomputable def leftCount (w : PermZ) (j : ℤ) : ℕ := (Left w j).ncard

theorem right_bound {w : PermZ} {D : ℕ} (hD : ∀ p : ℤ, (w p - p).natAbs ≤ D)
    {j p : ℤ} (hp : p ∈ Right w j) : j - (D : ℤ) ≤ p ∧ p ≤ j := by
  change p ≤ j ∧ j < w p at hp
  have := hD p
  omega

theorem left_bound {w : PermZ} {D : ℕ} (hD : ∀ p : ℤ, (w p - p).natAbs ≤ D)
    {j p : ℤ} (hp : p ∈ Left w j) : j < p ∧ p ≤ j + (D : ℤ) := by
  change w p ≤ j ∧ j < p at hp
  have := hD p
  omega

theorem AffSigned.right_finite {n : ℕ} {w : PermZ} (hw : AffSigned n w) (j : ℤ) :
    (Right w j).Finite := by
  obtain ⟨D, hD⟩ := hw.bound
  exact (Finset.Icc (j - (D : ℤ)) j).finite_toSet.subset
    (fun _ hp => Finset.mem_Icc.mpr (right_bound hD hp))

theorem AffSigned.left_finite {n : ℕ} {w : PermZ} (hw : AffSigned n w) (j : ℤ) :
    (Left w j).Finite := by
  obtain ⟨D, hD⟩ := hw.bound
  exact (Finset.Ioc j (j + (D : ℤ))).finite_toSet.subset
    (fun _ hp => Finset.mem_Ioc.mpr (left_bound hD hp))

theorem AffSigned.right_translate {n : ℕ} {w : PermZ} (hw : AffSigned n w) (j k : ℤ) :
    rightCount w (j + k * period n) = rightCount w j := by
  unfold rightCount
  symm
  apply Set.ncard_congr (fun p _ => p + k * period n)
  · intro p hp
    change p ≤ j ∧ j < w p at hp
    change _ ≤ _ ∧ _ < w (_ + _)
    rw [hw.translate]
    omega
  · intro a b _ _ he
    omega
  · intro p hp
    refine ⟨p - k * period n, ?_, by omega⟩
    change p ≤ _ ∧ _ < w p at hp
    change _ ≤ j ∧ j < w (_ - _)
    have h := hw.translate (p - k * period n) k
    rw [sub_add_cancel] at h
    omega

theorem AffSigned.right_reflect {n : ℕ} {w : PermZ} (hw : AffSigned n w) (j : ℤ) :
    rightCount w (-j-1) = leftCount w j := by
  unfold rightCount leftCount
  apply Set.ncard_congr (fun p _ => -p)
  · intro p hp
    change p ≤ -j-1 ∧ -j-1 < w p at hp
    change w (-p) ≤ j ∧ j < -p
    rw [hw.1]
    omega
  · intro a b _ _ he
    omega
  · intro p hp
    refine ⟨-p, ?_, by omega⟩
    change w p ≤ j ∧ j < p at hp
    change -p ≤ -j-1 ∧ -j-1 < w (-p)
    rw [hw.1]
    omega

private def indicator (j p : ℤ) : ℤ := if p ≤ j then 1 else 0

private theorem flux_eq_sum (w : PermZ) (j : ℤ) (s : Finset ℤ)
    (hr : Right w j ⊆ ↑s) (hl : Left w j ⊆ ↑s) :
    (rightCount w j : ℤ) - (leftCount w j : ℤ) =
      ∑ p ∈ s, (indicator j p - indicator j (w p)) := by
  have hR : Right w j = ↑(s.filter (fun p => p ≤ j ∧ j < w p)) := by
    ext p
    change (p ≤ j ∧ j < w p) ↔ _
    simp only [Finset.mem_coe, Finset.mem_filter]
    exact ⟨fun h => ⟨hr h, h⟩, And.right⟩
  have hL : Left w j = ↑(s.filter (fun p => w p ≤ j ∧ j < p)) := by
    ext p
    change (w p ≤ j ∧ j < p) ↔ _
    simp only [Finset.mem_coe, Finset.mem_filter]
    exact ⟨fun h => ⟨hl h, h⟩, And.right⟩
  rw [rightCount, leftCount, hR, hL, Set.ncard_coe_finset, Set.ncard_coe_finset]
  rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  unfold indicator
  by_cases h₁ : p ≤ j <;> by_cases h₂ : w p ≤ j <;>
    simp [h₁, h₂, not_lt.mpr, lt_of_not_ge]

private theorem flux_succ {n : ℕ} {w : PermZ} (hw : AffSigned n w) (j : ℤ) :
    (rightCount w (j+1) : ℤ) - (leftCount w (j+1) : ℤ) =
      (rightCount w j : ℤ) - (leftCount w j : ℤ) := by
  classical
  obtain ⟨D, hD⟩ := hw.bound
  let s := Finset.Icc (j - (D : ℤ)) (j + 1 + (D : ℤ))
  have hr (k : ℤ) (hk : j ≤ k ∧ k ≤ j + 1) : Right w k ⊆ ↑s := by
    intro p hp
    have := right_bound hD hp
    exact Finset.mem_Icc.mpr (by omega)
  have hl (k : ℤ) (hk : j ≤ k ∧ k ≤ j + 1) : Left w k ⊆ ↑s := by
    intro p hp
    have := left_bound hD hp
    exact Finset.mem_Icc.mpr (by omega)
  rw [flux_eq_sum w (j+1) s (hr _ (by omega)) (hl _ (by omega)),
    flux_eq_sum w j s (hr _ (by omega)) (hl _ (by omega))]
  have hdelta (p : ℤ) : indicator (j + 1) p - indicator j p =
      if p = j + 1 then 1 else 0 := by
    unfold indicator
    split <;> split <;> split <;> omega
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  have hpoint (p : ℤ) :
      (indicator (j + 1) p - indicator (j + 1) (w p)) -
        (indicator j p - indicator j (w p)) =
      (if p = j + 1 then 1 else 0) - (if p = w.symm (j + 1) then 1 else 0) := by
    rw [show ∀ a b c d : ℤ, (a - b) - (c - d) = (a - c) - (b - d) by intros; omega,
      hdelta, hdelta]
    have he : w p = j + 1 ↔ p = w.symm (j + 1) := w.eq_symm_apply.symm
    simp only [he]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hj : j + 1 ∈ s := Finset.mem_Icc.mpr (by omega)
  have hi : w.symm (j + 1) ∈ s := by
    have h := hD (w.symm (j + 1))
    rw [w.apply_symm_apply] at h
    exact Finset.mem_Icc.mpr (by omega)
  simp [hj, hi]

theorem AffSigned.cut_balance {n : ℕ} {w : PermZ} (hw : AffSigned n w) (j : ℤ) :
    rightCount w j = leftCount w j := by
  have h0 : rightCount w 0 = leftCount w 0 := by
    unfold rightCount leftCount
    apply Set.ncard_congr (fun p _ => -p)
    · intro p hp
      change p ≤ 0 ∧ 0 < w p at hp
      have he : p ≠ 0 := by
        intro he
        rw [he, hw.zero] at hp
        exact (lt_irrefl _ hp.2)
      change w (-p) ≤ 0 ∧ 0 < -p
      rw [hw.1]
      omega
    · intro a b _ _ he
      omega
    · intro p hp
      refine ⟨-p, ?_, by omega⟩
      change w p ≤ 0 ∧ 0 < p at hp
      have he : w p ≠ 0 := fun he => (ne_of_gt hp.2) (w.injective (he.trans hw.zero.symm))
      change -p ≤ 0 ∧ 0 < w (-p)
      rw [hw.1]
      omega
  induction j using Int.induction_on with
  | zero => exact h0
  | succ k ih =>
    have := flux_succ hw k
    omega
  | pred k ih =>
    have := flux_succ hw (-(k : ℤ)-1)
    rw [sub_add_cancel] at this
    omega

end AffineB
```

### `AffineBCutSum.lean`

```lean
import AffineBCuts
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals

namespace AffineB

open scoped BigOperators

private def cutsAt (w : PermZ) (p : ℤ) : Finset ℤ :=
  Finset.Ico (min p (w p)) (max p (w p))

private theorem mem_cutsAt (w : PermZ) (p j : ℤ) :
    j ∈ cutsAt w p ↔ p ∈ Right w j ∪ Left w j := by
  change j ∈ Finset.Ico _ _ ↔ (p ≤ j ∧ j < w p) ∨ (w p ≤ j ∧ j < p)
  rw [Finset.mem_Ico]
  omega

private theorem cutsAt_card (w : PermZ) (p : ℤ) :
    (cutsAt w p).card = (w p - p).natAbs := by
  unfold cutsAt
  rw [Int.card_Ico]
  omega

private theorem cross_translate {n : ℕ} {w : PermZ} (hw : AffSigned n w) (p j k : ℤ) :
    j + k * period n ∈ cutsAt w (p + k * period n) ↔ j ∈ cutsAt w p := by
  rw [mem_cutsAt, mem_cutsAt]
  change ((_ ≤ _ ∧ _ < w (_ + _)) ∨ (w (_ + _) ≤ _ ∧ _ < _)) ↔ _
  rw [hw.translate]
  change _ ↔ (p ≤ j ∧ j < w p) ∨ (w p ≤ j ∧ j < p)
  omega

private theorem cross_card {n : ℕ} {w : PermZ} (hw : AffSigned n w) (j : ℤ) :
    (Right w j ∪ Left w j).ncard = 2 * rightCount w j := by
  rw [Set.ncard_union_eq (hs := hw.right_finite j) (ht := hw.left_finite j)]
  · change rightCount w j + leftCount w j = _
    rw [← hw.cut_balance j]
    omega
  · rw [Set.disjoint_left]
    intro p hr hl
    exact (not_lt_of_ge hr.1) hl.2

private theorem full_cut_sum {n : ℕ} {w : PermZ} (hw : AffSigned n w) :
    ∑ p ∈ Finset.Ico 0 (period n), (w p - p).natAbs =
      2 * ∑ j ∈ Finset.Ico 0 (period n), rightCount w j := by
  classical
  let N := period n
  let s := Finset.Ico 0 N
  let pointsAt (j : ℤ) := ((hw.right_finite j).union (hw.left_finite j)).toFinset
  have hp (j p : ℤ) : p ∈ pointsAt j ↔ j ∈ cutsAt w p := by
    rw [Set.Finite.mem_toFinset, mem_cutsAt]
  have hd (j : ℤ) : (pointsAt j).card = 2 * rightCount w j := by
    rw [← Set.ncard_eq_toFinset_card _ ((hw.right_finite j).union (hw.left_finite j)), cross_card hw]
  have hdecomp (x : ℤ) : x % N + (x / N) * N = x := by
    simpa only [mul_comm] using Int.emod_add_mul_ediv x N
  have hpos : 0 < N := period_pos n
  have hm (x : ℤ) : x % N ∈ s :=
    Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩
  have hz (x : ℤ) (hx : x ∈ s) : x / N = 0 :=
    Int.ediv_eq_zero_of_lt (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2
  have hcut (p j : ℤ) :
      j % N ∈ cutsAt w (p - (j / N) * N) ↔ j ∈ cutsAt w p := by
    have h := cross_translate hw p j (-(j / N))
    rw [neg_mul, ← sub_eq_add_neg, ← sub_eq_add_neg] at h
    change j - (j / N) * N ∈ cutsAt w (p - (j / N) * N) ↔ _ at h
    convert h using 2
    have := hdecomp j
    omega
  have hpoint (j p : ℤ) :
      j - (p / N) * N ∈ cutsAt w (p % N) ↔ j ∈ cutsAt w p := by
    have h := cross_translate hw p j (-(p / N))
    rw [neg_mul, ← sub_eq_add_neg, ← sub_eq_add_neg] at h
    change j - (p / N) * N ∈ cutsAt w (p - (p / N) * N) ↔ _ at h
    convert h using 3
    have := hdecomp p
    omega
  have hdiv (x y : ℤ) (hx : x ∈ s) : (x - (y / N) * N) / N = -(y / N) := by
    rw [sub_eq_add_neg, ← neg_mul, Int.add_mul_ediv_right _ _ hpos.ne', hz x hx, zero_add]
  have hc : (s.sigma (fun p => cutsAt w p)).card = (s.sigma pointsAt).card := by
    refine Finset.card_nbij' (fun ⟨p, j⟩ => ⟨j % N, p - (j / N) * N⟩)
      (fun ⟨j, p⟩ => ⟨p % N, j - (p / N) * N⟩) ?_ ?_ ?_ ?_
    · rintro ⟨p,j⟩ h
      simp only [Finset.mem_coe, Finset.mem_sigma] at h ⊢
      exact ⟨hm _, (hp ..).mpr ((hcut ..).mpr h.2)⟩
    · rintro ⟨j,p⟩ h
      simp only [Finset.mem_coe, Finset.mem_sigma] at h ⊢
      exact ⟨hm _, (hpoint ..).mpr ((hp ..).mp h.2)⟩
    · rintro ⟨p,j⟩ h
      simp only [Finset.mem_coe, Finset.mem_sigma] at h
      apply congrArg₂ (fun a b => (⟨a,b⟩ : Σ _ : ℤ, ℤ))
      · rw [sub_eq_add_neg, ← neg_mul, Int.add_mul_emod_self_right,
          Int.emod_eq_of_lt (Finset.mem_Ico.mp h.1).1 (Finset.mem_Ico.mp h.1).2]
      · rw [hdiv _ _ h.1, neg_mul, sub_neg_eq_add, hdecomp]
    · rintro ⟨j,p⟩ h
      simp only [Finset.mem_coe, Finset.mem_sigma] at h
      apply congrArg₂ (fun a b => (⟨a,b⟩ : Σ _ : ℤ, ℤ))
      · rw [sub_eq_add_neg, ← neg_mul, Int.add_mul_emod_self_right,
          Int.emod_eq_of_lt (Finset.mem_Ico.mp h.1).1 (Finset.mem_Ico.mp h.1).2]
      · rw [hdiv _ _ h.1, neg_mul, sub_neg_eq_add, hdecomp]
  simp_rw [Finset.card_sigma, cutsAt_card, hd, ← Finset.mul_sum] at hc
  exact hc

private theorem int_sum_split (f : ℤ → ℕ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ x ∈ Finset.Ico a c, f x) =
      (∑ x ∈ Finset.Ico a b, f x) + ∑ x ∈ Finset.Ico b c, f x := by
  rw [← Finset.Ico_union_Ico_eq_Ico hab hbc, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive ..)]

private theorem reflect_sum_dis (n : ℕ) (w : PermZ) (hw : AffSigned n w) :
    ∑ p ∈ Finset.Ico 0 (period n), (w p - p).natAbs = 2 * dis n w := by
  let m := (n : ℤ) + 1
  have hN : period n = 2 * m := by unfold period m; omega
  have hm : 0 ≤ m := by dsimp [m]; omega
  have hmid : w m = m := hw.midpoint
  rw [int_sum_split (fun p => (w p - p).natAbs) hm (by omega : m ≤ period n)]
  have ha : ∑ p ∈ Finset.Ico 0 m, (w p - p).natAbs =
      ∑ p ∈ Finset.Ico 1 m, (w p - p).natAbs := by
    rw [int_sum_split (fun p => (w p - p).natAbs) (by omega : (0 : ℤ) ≤ 1) (by dsimp [m]; omega : 1 ≤ m)]
    simp [show Finset.Ico (0 : ℤ) 1 = {0} by ext p; simp; omega, hw.zero]
  have hb : ∑ p ∈ Finset.Ico m (period n), (w p - p).natAbs =
      ∑ p ∈ Finset.Ico (m+1) (period n), (w p - p).natAbs := by
    have hsing : Finset.Ico m (m + 1) = {m} := by ext p; simp; omega
    rw [int_sum_split (fun p => (w p - p).natAbs) (by omega : m ≤ m+1)
      (by dsimp [m, period]; omega : m+1 ≤ period n)]
    simp [hsing, hmid]
  rw [ha, hb]
  have hreflect : ∑ p ∈ Finset.Ico (m+1) (period n), (w p - p).natAbs =
      ∑ p ∈ Finset.Ico 1 m, (w p - p).natAbs := by
    refine Finset.sum_nbij' (fun p => period n - p) (fun p => period n - p) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_Ico] at hp ⊢
      omega
    · intro p hp
      rw [Finset.mem_Ico] at hp ⊢
      omega
    · intro p _
      omega
    · intro p _
      omega
    · intro p _
      rw [hw.mirror]
      rw [show period n - w p - (period n - p) = -(w p - p) by omega, Int.natAbs_neg]
  have hwindow : (∑ p ∈ Finset.Ico 1 m, (w p - p).natAbs) = dis n w := by
    unfold dis
    refine Finset.sum_nbij' Int.toNat Int.ofNat ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_Ico] at hp
      exact Finset.mem_Icc.mpr (by dsimp [m] at hp; omega)
    · intro p hp
      rw [Finset.mem_Icc] at hp
      exact Finset.mem_Ico.mpr (by dsimp [m]; omega)
    · intro p hp
      rw [Finset.mem_Ico] at hp
      exact Int.toNat_of_nonneg (by omega)
    · intro p _
      simp
    · intro p hp
      rw [Finset.mem_Ico] at hp
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ p)]
  rw [hreflect, hwindow, two_mul]

theorem AffSigned.dis_eq_cut_sum {n : ℕ} {w : PermZ} (hw : AffSigned n w) :
    dis n w = 2 * ∑ j ∈ Finset.Ico 0 ((n : ℤ)+1), rightCount w j := by
  let m := (n : ℤ) + 1
  have hN : period n = 2 * m := by unfold period m; omega
  have hm : 0 ≤ m := by dsimp [m]; omega
  have htotal := full_cut_sum hw
  rw [reflect_sum_dis n w hw] at htotal
  rw [int_sum_split (rightCount w) hm (by omega : m ≤ period n)] at htotal
  have hreflect : ∑ j ∈ Finset.Ico m (period n), rightCount w j =
      ∑ j ∈ Finset.Ico 0 m, rightCount w j := by
    refine Finset.sum_nbij' (fun j => period n - j - 1) (fun j => period n - j - 1)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Ico] at hj ⊢
      omega
    · intro j hj
      rw [Finset.mem_Ico] at hj ⊢
      omega
    · intro j _
      omega
    · intro j _
      omega
    · intro j _
      rw [show period n - j - 1 = (-j-1) + 1 * period n by omega,
        hw.right_translate, hw.right_reflect, ← hw.cut_balance]
  rw [hreflect] at htotal
  change dis n w = 2 * ∑ j ∈ Finset.Ico 0 m, rightCount w j
  omega

end AffineB
```

### `AffineBParity.lean`

```lean
import AffineBBasics

namespace AffineB

def positivePrefix (j : ℕ) : Set ℤ := {p | 0 < p ∧ p ≤ (j : ℤ)}

def negativeIn (w : PermZ) (s : Set ℤ) : Set ℤ := {p ∈ s | w p < 0}

theorem AffSigned.nonzero {n : ℕ} {w : PermZ} (hw : AffSigned n w) {p : ℤ}
    (hp : p ≠ 0) : w p ≠ 0 := fun h => hp (w.injective (h.trans hw.zero.symm))

private theorem magnitude_signed {n : ℕ} {w : PermZ} (hw : AffSigned n w) (p : ℤ) :
    w (Int.natAbs p : ℤ) = if 0 ≤ p then w p else -w p := by
  split
  · congr 1
    omega
  · rw [show (p.natAbs : ℤ) = -p by omega, hw.1]

private theorem magnitude_symm {n : ℕ} {t : PermZ} (ht : AffSigned n t) (p : ℤ) :
    (t.symm ((t p).natAbs : ℤ)).natAbs = p.natAbs := by
  rw [magnitude_signed ht.inverse]
  split <;> simp

theorem negPrefix_eq_ncard (w : PermZ) (j : ℕ) :
    negPrefix w j = (negativeIn w (positivePrefix j)).ncard := by
  unfold negPrefix
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun (p : ℕ) _ => (p : ℤ))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hp
    change (0 < (p : ℤ) ∧ (p : ℤ) ≤ (j : ℤ)) ∧ w (p : ℤ) < 0
    exact ⟨⟨by omega, by omega⟩, hp.2⟩
  · intro a b _ _ he
    omega
  · intro p hp
    change (0 < p ∧ p ≤ (j : ℤ)) ∧ w p < 0 at hp
    have he : (p.toNat : ℤ) = p := by omega
    refine ⟨p.toNat, ?_, he⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, he]
    exact ⟨⟨by omega, by omega⟩, hp.2⟩

private theorem negativeIn_finite {n : ℕ} {w : PermZ} (hw : AffSigned n w)
    {s : Set ℤ} (hs : ∀ p ∈ s, 0 < p) : (negativeIn w s).Finite :=
  hw.negCrossing_finite.subset (fun p hp => ⟨hs p hp.1, hp.2⟩)

private theorem parity_mul_on {n : ℕ} {u t : PermZ}
    (hu : AffSigned n u) (ht : AffSigned n t) {s : Set ℤ}
    (hs : ∀ p ∈ s, 0 < p)
    (hmap : ∀ p : ℤ, 0 < p → (p ∈ s ↔ ((t p).natAbs : ℤ) ∈ s)) :
    (negativeIn (u * t) s).ncard % 2 =
      ((negativeIn u s).ncard + (negativeIn t s).ncard) % 2 := by
  let mag : ℤ → ℤ := fun p => (t p).natAbs
  let A := negativeIn t s
  let B := s ∩ mag ⁻¹' (negativeIn u s)
  have hB : Set.BijOn mag B (negativeIn u s) := by
    refine ⟨fun p hp => hp.2, ?_, ?_⟩
    · intro p hp q hq hpq
      have h := congrArg (fun x => (t.symm x).natAbs) hpq
      change (t.symm ((t p).natAbs : ℤ)).natAbs =
        (t.symm ((t q).natAbs : ℤ)).natAbs at h
      rw [magnitude_symm ht, magnitude_symm ht] at h
      have hp' := hs p hp.1
      have hq' := hs q hq.1
      omega
    · intro z hz
      have hz' := hs z hz.1
      let p : ℤ := (t.symm z).natAbs
      have he : mag p = z := by
        change ((t ((t.symm z).natAbs : ℤ)).natAbs : ℤ) = z
        have hh := magnitude_symm ht.inverse z
        change (t ((t.symm z).natAbs : ℤ)).natAbs = z.natAbs at hh
        rw [hh]
        omega
      have hp : 0 < p := by
        have h := ht.inverse.nonzero (show z ≠ 0 by omega)
        dsimp [p]
        omega
      have hp' := (hmap p hp).mpr (show mag p ∈ s by rw [he]; exact hz.1)
      exact ⟨p, ⟨hp', show mag p ∈ negativeIn u s by rw [he]; exact hz⟩, he⟩
  have hAfin : A.Finite := negativeIn_finite ht hs
  have hBfin : B.Finite := (negativeIn_finite hu hs).of_injOn hB.1 hB.2.1
  have hneg : negativeIn (u * t) s = (A \ B) ∪ (B \ A) := by
    ext p
    change (p ∈ s ∧ u (t p) < 0) ↔ (p ∈ s ∧ t p < 0) ∧ ¬(p ∈ s ∧
        (mag p ∈ s ∧ u (mag p) < 0)) ∨
      (p ∈ s ∧ (mag p ∈ s ∧ u (mag p) < 0)) ∧ ¬(p ∈ s ∧ t p < 0)
    by_cases hp : p ∈ s
    · have hmag : mag p ∈ s := (hmap p (hs p hp)).mp hp
      simp only [hp, hmag, true_and, mag, magnitude_signed hu]
      have hn := hu.nonzero (ht.nonzero (ne_of_gt (hs p hp)))
      split <;> omega
    · simp [hp]
  have hdis : Disjoint (A \ B) (B \ A) := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact hp.2 hq.1
  have hleft := Set.ncard_sdiff (s := A ∩ B) (t := A) Set.inter_subset_left (hAfin.subset Set.inter_subset_left)
  have hright := Set.ncard_sdiff (s := A ∩ B) (t := B) Set.inter_subset_right (hBfin.subset Set.inter_subset_right)
  have heleft : A \ (A ∩ B) = A \ B := by ext p; simp
  have heright : B \ (A ∩ B) = B \ A := by ext p; simp [and_comm]
  rw [heleft] at hleft
  rw [heright] at hright
  have hi₁ := Set.ncard_le_ncard (s := A ∩ B) Set.inter_subset_left hAfin
  have hi₂ := Set.ncard_le_ncard (s := A ∩ B) Set.inter_subset_right hBfin
  rw [hneg, Set.ncard_union_eq hdis (hAfin.subset Set.sdiff_subset)
    (hBfin.subset Set.sdiff_subset), hleft, hright, ← hB.ncard_eq]
  change ((A.ncard - (A ∩ B).ncard) + (B.ncard - (A ∩ B).ncard)) % 2 =
    (B.ncard + A.ncard) % 2
  omega

theorem AffB.mul {n : ℕ} {u t : PermZ} (hu : AffB n u) (ht : AffB n t) : AffB n (u * t) := by
  refine ⟨hu.1.mul ht.1, ?_⟩
  have h := parity_mul_on hu.1 ht.1 (s := Set.Ioi 0) (fun _ hp => hp)
    (fun p hp => by
      have hn := ht.1.nonzero (ne_of_gt hp)
      change 0 < p ↔ 0 < ((t p).natAbs : ℤ)
      omega)
  change (negCrossing (u * t)).ncard % 2 =
    ((negCrossing u).ncard + (negCrossing t).ncard) % 2 at h
  have hu' := Nat.even_iff.mp hu.2
  have ht' := Nat.even_iff.mp ht.2
  exact Nat.even_iff.mpr (by omega)

theorem prefix_parity_mul {n : ℕ} {u t : PermZ} {j : ℕ}
    (hu : AffSigned n u) (ht : AffSigned n t) (hg : Good t j) :
    negPrefix (u * t) j % 2 = (negPrefix u j + negPrefix t j) % 2 := by
  simp only [negPrefix_eq_ncard]
  apply parity_mul_on hu ht (fun _ hp => hp.1)
  intro p hp
  have hn := ht.nonzero (ne_of_gt hp)
  have h := hg p
  change (0 < p ∧ p ≤ (j : ℤ)) ↔
    (0 < ((t p).natAbs : ℤ) ∧ ((t p).natAbs : ℤ) ≤ (j : ℤ))
  omega

theorem affB_one (n : ℕ) : AffB n (1 : PermZ) := by
  refine ⟨affSigned_one n, ?_⟩
  have h : negCrossing (1 : PermZ) = ∅ := by
    ext p
    change (0 < p ∧ p < 0) ↔ p ∈ (∅ : Set ℤ)
    rw [Set.mem_empty_iff_false]
    exact ⟨fun h => (not_lt_of_ge h.1.le) h.2, False.elim⟩
  rw [h, Set.ncard_empty]
  exact ⟨0, rfl⟩

end AffineB
```

### `AffineBLower.lean`

```lean
import AffineBCutSum
import AffineBParity
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace AffineB

open scoped BigOperators

theorem swapCopy.rebase {n : ℕ} {x y p q a b : ℤ}
    (hpq : swapCopy n x y p q) (hab : swapCopy n x y a b) :
    swapCopy n p q a b := by
  obtain ⟨k, hk | hk | hk | hk⟩ := hpq
  all_goals obtain ⟨rfl, rfl⟩ := hk
  all_goals obtain ⟨l, hl | hl | hl | hl⟩ := hab
  all_goals obtain ⟨rfl, rfl⟩ := hl
  all_goals
    first
    | refine ⟨l-k, ?_⟩
      simp only [sub_mul]
      omega
    | refine ⟨l+k, ?_⟩
      simp only [add_mul]
      omega

private theorem refl_even_prefix {n j : ℕ} {t : PermZ}
    (ht : BRefl n t) (hg : Good t j) (hj : j ≤ n) : Even (negPrefix t j) := by
  classical
  by_cases hmove : ∃ p : ℤ, p.natAbs ≤ j ∧ t p ≠ p
  · obtain ⟨p, hp, hpne⟩ := hmove
    have hq := (hg p).mp hp
    obtain ⟨htB, x, y, _, hswap, hfix⟩ := ht
    obtain ⟨q, hqcopy⟩ : ∃ q, swapCopy n x y p q := by
      by_contra hc
      exact hpne (hfix p hc)
    have hpq := hswap p q hqcopy
    rw [hpq] at hq
    have hnegs : negativeIn t (positivePrefix j) = negCrossing t := by
      ext a
      change ((0 < a ∧ a ≤ (j : ℤ)) ∧ t a < 0) ↔ (0 < a ∧ t a < 0)
      refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
      by_contra! ha
      obtain ⟨b, hb⟩ : ∃ b, swapCopy n x y a b := by
        by_contra hc
        have := hfix a hc
        omega
      have htb := hswap a b hb
      obtain ⟨k, hk | hk | hk | hk⟩ := hqcopy.rebase hb
      all_goals
        have hkpos : 0 < k := by
          by_contra! h
          have hh := mul_nonpos_of_nonpos_of_nonneg h (period_pos n).le
          omega
        have hlarge : period n ≤ k * period n := by
          simpa using mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ k by omega) (period_pos n).le
        have hperiod : (j : ℤ) < period n := by unfold period; omega
        omega
    rw [negPrefix_eq_ncard, hnegs]
    exact htB.2
  · have he : negativeIn t (positivePrefix j) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      change (0 < p ∧ p ≤ (j : ℤ)) ∧ t p < 0 at hp
      have he : t p = p := by
        by_contra hc
        exact hmove ⟨p, by omega, hc⟩
      omega
    rw [negPrefix_eq_ncard, he, Set.ncard_empty]
    exact ⟨0, rfl⟩

private def crossMap (t : PermZ) (j p : ℤ) : ℤ ⊕ ℤ :=
  if j < t p then Sum.inl p else Sum.inr (t p)

private theorem cut_subadd_aux {n : ℕ} {u t : PermZ} (hu : AffSigned n u)
    (ht : AffSigned n t) (j : ℤ) :
    rightCount (u * t) j ≤ rightCount t j + rightCount u j ∧
      (∀ p ∈ Right t j, p ∉ Right (u * t) j →
        rightCount (u * t) j < rightCount t j + rightCount u j) := by
  let s := (ht.right_finite j).toFinset
  let r := (hu.right_finite j).toFinset
  let v := ((hu.mul ht).right_finite j).toFinset
  let im := v.image (crossMap t j)
  have hmaps : ∀ p ∈ v, crossMap t j p ∈ s.disjSum r := by
    intro p hp
    have h := ((hu.mul ht).right_finite j).mem_toFinset.mp hp
    change p ≤ j ∧ j < u (t p) at h
    unfold crossMap
    split
    · rename_i htp
      rw [Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]
      exact ⟨h.1, htp⟩
    · rename_i htp
      rw [Finset.inr_mem_disjSum, Set.Finite.mem_toFinset]
      exact ⟨not_lt.mp htp, h.2⟩
  have hinj : Set.InjOn (crossMap t j) ↑v := by
    intro a _ b _ he
    unfold crossMap at he
    split at he <;> split at he
    · exact Sum.inl.inj he
    · cases he
    · cases he
    · exact t.injective (Sum.inr.inj he)
  have hsubset : im ⊆ s.disjSum r := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact hmaps p hp
  have him : im.card = rightCount (u * t) j := by
    dsimp [im]
    rw [Finset.card_image_of_injOn hinj]
    exact (Set.ncard_eq_toFinset_card _ ((hu.mul ht).right_finite j)).symm
  have hrs : (s.disjSum r).card = rightCount t j + rightCount u j := by
    rw [Finset.card_disjSum]
    exact congrArg₂ (· + ·) (Set.ncard_eq_toFinset_card _ (ht.right_finite j)).symm
      (Set.ncard_eq_toFinset_card _ (hu.right_finite j)).symm
  rw [← him, ← hrs]
  refine ⟨Finset.card_le_card hsubset, fun p hp hpv => ?_⟩
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, fun he => ?_⟩
  have himp : Sum.inl p ∈ im := by
    rw [he, Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]
    exact hp
  obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp himp
  unfold crossMap at hqp
  split at hqp
  · have hq' := ((hu.mul ht).right_finite j).mem_toFinset.mp hq
    exact hpv (Sum.inl.inj hqp ▸ hq')
  · cases hqp

theorem cut_subadd {n : ℕ} {u t : PermZ} (hu : AffSigned n u)
    (ht : AffSigned n t) (j : ℤ) :
    rightCount (u * t) j ≤ rightCount u j + rightCount t j := by
  simpa only [add_comm] using (cut_subadd_aux hu ht j).1

theorem good_mul_iff {u t : PermZ} {j : ℕ} (ht : Good t j) :
    Good (u * t) j ↔ Good u j := by
  constructor
  · intro h p
    have hp := ht (t.symm p)
    have hv := h (t.symm p)
    change (t.symm p).natAbs ≤ j ↔ (u (t (t.symm p))).natAbs ≤ j at hv
    rw [t.apply_symm_apply] at hp hv
    exact hp.symm.trans hv
  · intro h p
    exact (ht p).trans (h (t p))

private theorem oddGood_charge {n j : ℕ} {u t : PermZ} (hu : AffSigned n u)
    (ht : BRefl n t) (hj : j ≤ n) (hv : OddGood (u * t) j) (hprev : ¬ OddGood u j) :
    rightCount (u * t) (j : ℤ) < rightCount u (j : ℤ) + rightCount t (j : ℤ) := by
  have hn : ¬ Good t j := by
    intro hg
    have hp := prefix_parity_mul hu ht.1.1 hg
    have he := Nat.even_iff.mp (refl_even_prefix ht hg hj)
    have hodd := hv.2
    simp only [Nat.even_iff] at hodd
    exact hprev ⟨(good_mul_iff hg).mp hv.1, Nat.even_iff.not.mpr (by omega)⟩
  obtain ⟨p, hp, htp⟩ : ∃ p : ℤ, p.natAbs ≤ j ∧ j < (t p).natAbs := by
    by_contra! h
    exact hn (Good.of_mapsTo h)
  have hdepart : ∃ q : ℤ, q.natAbs ≤ j ∧ (j : ℤ) < t q := by
    by_cases hp' : 0 ≤ t p
    · exact ⟨p, hp, by omega⟩
    · refine ⟨-p, by simpa using hp, ?_⟩
      rw [ht.1.1.1]
      omega
  obtain ⟨q, hq, htq⟩ := hdepart
  have hr : q ∈ Right t (j : ℤ) := ⟨by omega, htq⟩
  have hnv : q ∉ Right (u * t) (j : ℤ) := by
    have hh := (hv.1 q).mp hq
    exact fun h => (show ¬ (j : ℤ) < (u * t) q by omega) h.2
  simpa only [add_comm] using (cut_subadd_aux hu ht.1.1 (j : ℤ)).2 q hr hnv

noncomputable def potential (n : ℕ) (w : PermZ) : ℕ :=
  dis n w + 2 * (oddGoods n w).card

theorem potential_eq (n : ℕ) (w : PermZ) :
    potential n w = dis n w + 2 * (blC n w - blB n w) := by
  rw [potential, block_difference]

theorem potential_mul_le {n : ℕ} {u t : PermZ} (hu : AffSigned n u) (ht : BRefl n t) :
    potential n (u * t) ≤ potential n u + dis n t := by
  classical
  let s := Finset.Ico (0 : ℤ) ((n : ℤ) + 1)
  let a := oddGoods n (u * t)
  let b := oddGoods n u
  let slack (j : ℤ) := rightCount u j + rightCount t j - rightCount (u * t) j
  have hpay : (a \ b).card ≤ ∑ j ∈ s, slack j := by
    let e : ℕ ↪ ℤ := ⟨Int.ofNat, fun _ _ h => Int.ofNat.inj h⟩
    let d := (a \ b).map e
    have hsub : d ⊆ s := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
      have hi := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hk).1).1
      rw [Finset.mem_Ico] at hi
      exact Finset.mem_Ico.mpr ⟨by change 0 ≤ (k : ℤ); omega, by change (k : ℤ) < _; omega⟩
    have hone : ∀ j ∈ d, 1 ≤ slack j := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
      obtain ⟨hv, hn⟩ := Finset.mem_sdiff.mp hk
      obtain ⟨hi, hv⟩ := Finset.mem_filter.mp hv
      have hn' : ¬ OddGood u k := fun hk => hn (Finset.mem_filter.mpr ⟨hi, hk⟩)
      have h := oddGood_charge hu ht (Nat.le_of_lt (Finset.mem_Ico.mp hi).2) hv hn'
      change 1 ≤ rightCount u (k : ℤ) + rightCount t (k : ℤ) - rightCount (u * t) (k : ℤ)
      omega
    calc
      (a \ b).card = ∑ _j ∈ d, (1 : ℕ) := by simp [d]
      _ ≤ ∑ j ∈ d, slack j := Finset.sum_le_sum hone
      _ ≤ ∑ j ∈ s, slack j := Finset.sum_le_sum_of_subset hsub
  have hc : a.card ≤ (a \ b).card + b.card := by
    have h := Finset.card_sdiff_add_card_inter a b
    have hi : (a ∩ b).card ≤ b.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have hs (j : ℤ) : slack j + rightCount (u * t) j = rightCount u j + rightCount t j :=
    Nat.sub_add_cancel (cut_subadd hu ht.1.1 j)
  have hsum : (∑ j ∈ s, slack j) + (∑ j ∈ s, rightCount (u * t) j) =
      (∑ j ∈ s, rightCount u j) + (∑ j ∈ s, rightCount t j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hs j)
  have hdis : 2 * (∑ j ∈ s, slack j) + dis n (u * t) = dis n u + dis n t := by
    rw [(hu.mul ht.1.1).dis_eq_cut_sum, hu.dis_eq_cut_sum, ht.1.1.dis_eq_cut_sum]
    change 2 * (∑ j ∈ s, slack j) + 2 * (∑ j ∈ s, rightCount (u * t) j) =
      2 * (∑ j ∈ s, rightCount u j) + 2 * (∑ j ∈ s, rightCount t j)
    omega
  change dis n (u * t) + 2 * a.card ≤ dis n u + 2 * b.card + dis n t
  omega

theorem potential_one (n : ℕ) : potential n (1 : PermZ) = 0 := by
  classical
  have hneg (j : ℕ) : negPrefix (1 : PermZ) j = 0 := by
    unfold negPrefix
    have he : ((Finset.Icc 1 j).filter (fun i : ℕ => (1 : PermZ) (i : ℤ) < 0)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hn := (Finset.mem_filter.mp hi).2
      change (i : ℤ) < 0 at hn
      omega
    rw [he, Finset.card_empty]
  have hodd : oddGoods n (1 : PermZ) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have h := (Finset.mem_filter.mp hj).2.2
    rw [hneg] at h
    exact h ⟨0, rfl⟩
  simp [potential, dis, hodd]

private theorem list_lower {n : ℕ} (u : PermZ) (hu : AffSigned n u) (ts : List PermZ)
    (hts : ∀ t ∈ ts, BRefl n t) :
    potential n (u * ts.prod) ≤ potential n u + (ts.map (dis n)).sum := by
  induction ts generalizing u with
  | nil => simp
  | cons t ts ih =>
    have ht := hts t List.mem_cons_self
    have hrest (r : PermZ) (hr : r ∈ ts) := hts r (List.mem_cons_of_mem t hr)
    have h := ih (u * t) (hu.mul ht.1.1) hrest
    have hstep := potential_mul_le hu ht
    simp only [List.prod_cons, List.map_cons, List.sum_cons, ← mul_assoc]
    omega

theorem lewis_tenner_4_2_lower (n : ℕ) (w : PermZ) {c : ℕ} (hc : c ∈ Costs2 n w) :
    dis n w + 2 * (blC n w - blB n w) ≤ c := by
  obtain ⟨ts, hs, rfl, rfl⟩ := hc
  have h := list_lower (1 : PermZ) (affSigned_one n) ts hs
  rwa [one_mul, potential_one, zero_add, potential_eq] at h

#print axioms lewis_tenner_4_2_lower

end AffineB
```

### `AffineBWindow.lean`

```lean
import AffineBParity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace AffineB

open scoped BigOperators

theorem period_decomp (n : ℕ) (x : ℤ) :
    x % period n + (x / period n) * period n = x := by
  simpa only [mul_comm] using Int.emod_add_mul_ediv x (period n)

theorem window_cases (n : ℕ) (p : ℤ) :
    (∃ k : ℤ, p = k * period n) ∨
    (∃ k : ℤ, p = ((n : ℤ) + 1) + k * period n) ∨
    (∃ (i : ℕ) (k : ℤ), 1 ≤ i ∧ i ≤ n ∧ p = (i : ℤ) + k * period n) ∨
    (∃ (i : ℕ) (k : ℤ), 1 ≤ i ∧ i ≤ n ∧ p = -(i : ℤ) + k * period n) := by
  let r := p % period n
  let k := p / period n
  have hpos := period_pos n
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hpos.ne'
  have hrN : r < period n := Int.emod_lt_of_pos _ hpos
  have he : r + k * period n = p := period_decomp n p
  have hN : period n = 2 * (n : ℤ) + 2 := rfl
  by_cases hr : r = 0
  · exact Or.inl ⟨k, by omega⟩
  by_cases hr' : r = (n : ℤ) + 1
  · exact Or.inr (Or.inl ⟨k, by omega⟩)
  by_cases h : r ≤ (n : ℤ)
  · exact Or.inr (Or.inr (Or.inl ⟨r.toNat, k, by omega, by omega, by omega⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨(period n - r).toNat, k + 1,
      by omega, by omega, ?_⟩))
    rw [add_mul, one_mul]
    omega

theorem AffSigned.window_ext {n : ℕ} {u w : PermZ}
    (hu : AffSigned n u) (hw : AffSigned n w)
    (h : ∀ i ∈ Finset.Icc 1 n, u (i : ℤ) = w (i : ℤ)) : u = w := by
  ext p
  change u p = w p
  rcases window_cases n p with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨i,k,hi,hin,rfl⟩ | ⟨i,k,hi,hin,rfl⟩
  · simpa only [zero_add, hu.zero, hw.zero] using
      (hu.translate 0 k).trans ((by rw [hu.zero, hw.zero] :
        u 0 + k * period n = w 0 + k * period n).trans (hw.translate 0 k).symm)
  · rw [hu.translate, hw.translate, hu.midpoint, hw.midpoint]
  · rw [hu.translate, hw.translate, h i (Finset.mem_Icc.mpr ⟨hi, hin⟩)]
  · rw [hu.translate, hw.translate, hu.1, hw.1, h i (Finset.mem_Icc.mpr ⟨hi, hin⟩)]

theorem AffSigned.dis_zero_iff {n : ℕ} {w : PermZ} (hw : AffSigned n w) :
    dis n w = 0 ↔ w = 1 := by
  constructor
  · intro h
    apply hw.window_ext (affSigned_one n)
    intro i hi
    have h' : (w (i : ℤ) - (i : ℤ)).natAbs ≤ dis n w :=
      Finset.single_le_sum (f := fun k : ℕ => (w (k : ℤ) - (k : ℤ)).natAbs)
        (fun _ _ => Nat.zero_le _) hi
    change w (i : ℤ) = (i : ℤ)
    omega
  · rintro rfl
    simp [dis]

private theorem window_mod_nonzero {n : ℕ} {w : PermZ} (hw : AffSigned n w)
    {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) : w (i : ℤ) % period n ≠ 0 := by
  intro h
  let k := w (i : ℤ) / period n
  have he := period_decomp n (w (i : ℤ))
  rw [h, zero_add] at he
  have hk : w (k * period n) = k * period n := by
    simpa only [zero_add, hw.zero] using hw.translate 0 k
  have hi' : (i : ℤ) = k * period n := w.injective (he.symm.trans hk.symm)
  have hr : ((i : ℤ) % period n) = (i : ℤ) :=
    Int.emod_eq_of_lt (by omega) (by unfold period; omega)
  rw [hi'] at hr
  have hzero : (k * period n) % period n = 0 := by simp
  rw [hzero, ← hi'] at hr
  omega

def floorMass (n : ℕ) (w : PermZ) (i : ℕ) : ℕ :=
  (w (i : ℤ) / period n).natAbs

theorem floorMass_small {n : ℕ} {w : PermZ} {i : ℕ}
    (h : -(n : ℤ) ≤ w (i : ℤ) ∧ w (i : ℤ) ≤ n) :
    floorMass n w i = if w (i : ℤ) < 0 then 1 else 0 := by
  unfold floorMass
  split
  · rename_i hn
    have h' : 0 ≤ w (i : ℤ) + period n ∧ w (i : ℤ) + period n < period n := by
      unfold period
      omega
    have hq := Int.ediv_eq_zero_of_lt h'.1 h'.2
    rw [show w (i : ℤ) + period n = w (i : ℤ) + 1 * period n by simp,
      Int.add_mul_ediv_right _ _ (period_pos n).ne'] at hq
    rw [show w (i : ℤ) / period n = -1 by omega]
    decide
  · rename_i hn
    rw [Int.ediv_eq_zero_of_lt (by omega) (by unfold period; omega)]
    decide

private theorem shift_nonneg_iff {N x k : ℤ} (hx : 0 ≤ x ∧ x < N) :
    0 ≤ x + k * N ↔ 0 ≤ k := by
  constructor
  · intro h
    by_contra! hk
    have hh := mul_le_mul_of_nonneg_right (show k ≤ -1 by omega) (show 0 ≤ N by omega)
    rw [neg_one_mul] at hh
    omega
  · intro h
    exact add_nonneg hx.1 (mul_nonneg h (by omega))

private def liftIndex (n : ℕ) (p : ℤ) : ℕ :=
  let r := p % period n
  (if r ≤ (n : ℤ) then r else period n - r).toNat

private def liftCode (n : ℕ) (p : ℤ) : ℤ :=
  if p % period n ≤ (n : ℤ) then -(p / period n) - 1 else p / period n

private theorem liftIndexCode_pos {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (k : ℤ) :
    liftIndex n ((i : ℤ) + k * period n) = i ∧
    liftCode n ((i : ℤ) + k * period n) = -k - 1 := by
  have hr : 0 ≤ (i : ℤ) ∧ (i : ℤ) < period n := by unfold period; omega
  simp [liftIndex, liftCode, Int.add_mul_emod_self_right,
    Int.add_mul_ediv_right _ _ (period_pos n).ne', Int.ediv_eq_zero_of_lt hr.1 hr.2,
    Int.emod_eq_of_lt hr.1 hr.2, hin]

private theorem liftIndexCode_neg {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (k : ℤ) :
    liftIndex n (-(i : ℤ) + k * period n) = i ∧
    liftCode n (-(i : ℤ) + k * period n) = k - 1 := by
  have hr : 0 ≤ period n - (i : ℤ) ∧ period n - (i : ℤ) < period n := by
    unfold period
    omega
  have he : -(i : ℤ) + k * period n = (period n - (i : ℤ)) + (k - 1) * period n := by
    rw [sub_mul, one_mul]
    omega
  have hlt : ¬ period n - (i : ℤ) ≤ (n : ℤ) := by unfold period; omega
  rw [he]
  simp [liftIndex, liftCode, Int.add_mul_emod_self_right,
    Int.add_mul_ediv_right _ _ (period_pos n).ne', Int.ediv_eq_zero_of_lt hr.1 hr.2,
    Int.emod_eq_of_lt hr.1 hr.2, hlt]

private theorem posShift_spec {n i : ℕ} {w : PermZ} (hw : AffSigned n w)
    (hi : 1 ≤ i) (hin : i ≤ n) (k : ℤ) :
    (i : ℤ) + k * period n ∈ negCrossing w ↔ 0 ≤ k ∧ k + w (i : ℤ) / period n < 0 := by
  let N := period n
  let a := w (i : ℤ)
  have hr : 0 < a % N ∧ a % N < N := by
    have h := window_mod_nonzero hw hi hin
    exact ⟨lt_of_le_of_ne (Int.emod_nonneg _ (period_pos n).ne') (Ne.symm h),
      Int.emod_lt_of_pos _ (period_pos n)⟩
  have hq : a % N + (a / N) * N = a := period_decomp n a
  change (0 < (i : ℤ) + k * N ∧ w ((i : ℤ) + k * N) < 0) ↔ _
  rw [hw.translate]
  change (0 < (i : ℤ) + k * N ∧ a + k * N < 0) ↔ 0 ≤ k ∧ k + a / N < 0
  have h0 : 0 ≤ (i : ℤ) - 1 ∧ (i : ℤ) - 1 < N := by dsimp [N, period]; omega
  have h1 := shift_nonneg_iff (k := k) h0
  have h2 := shift_nonneg_iff (k := k + a / N) (show 0 ≤ a % N ∧ a % N < N from ⟨hr.1.le, hr.2⟩)
  rw [add_mul] at h2
  omega

private theorem negShift_spec {n i : ℕ} {w : PermZ} (hw : AffSigned n w)
    (hi : 1 ≤ i) (hin : i ≤ n) (k : ℤ) :
    -(i : ℤ) + k * period n ∈ negCrossing w ↔ 1 ≤ k ∧ k ≤ w (i : ℤ) / period n := by
  let N := period n
  let a := w (i : ℤ)
  have hr : 0 < a % N ∧ a % N < N := by
    have h := window_mod_nonzero hw hi hin
    exact ⟨lt_of_le_of_ne (Int.emod_nonneg _ (period_pos n).ne') (Ne.symm h),
      Int.emod_lt_of_pos _ (period_pos n)⟩
  have hq : a % N + (a / N) * N = a := period_decomp n a
  change (0 < -(i : ℤ) + k * N ∧ w (-(i : ℤ) + k * N) < 0) ↔ _
  rw [hw.translate, hw.1]
  change (0 < -(i : ℤ) + k * N ∧ -a + k * N < 0) ↔ 1 ≤ k ∧ k ≤ a / N
  have h0 : 0 ≤ N - (i : ℤ) - 1 ∧ N - (i : ℤ) - 1 < N := by dsimp [N, period]; omega
  have h1 := shift_nonneg_iff (k := k - 1) h0
  rw [sub_mul, one_mul] at h1
  have h2 := shift_nonneg_iff (k := a / N - k)
    (show 0 ≤ a % N - 1 ∧ a % N - 1 < N from ⟨by omega, by omega⟩)
  rw [sub_mul] at h2
  omega

theorem AffSigned.negCrossing_sum_floor {n : ℕ} {w : PermZ} (hw : AffSigned n w) :
    (negCrossing w).ncard = ∑ i ∈ Finset.Icc 1 n, floorMass n w i := by
  let Q (i : ℕ) := w (i : ℤ) / period n
  let s := (Finset.Icc 1 n).sigma (fun i => Finset.Ico (min 0 (Q i)) (max 0 (Q i)))
  have hmem (i : ℕ) (k : ℤ) : (⟨i,k⟩ : Σ _ : ℕ, ℤ) ∈ (s : Set _) ↔
      (1 ≤ i ∧ i ≤ n) ∧ min 0 (Q i) ≤ k ∧ k < max 0 (Q i) := by
    simp [s]
  let f (p : ℤ) : Σ _ : ℕ, ℤ := ⟨liftIndex n p, liftCode n p⟩
  let g (v : Σ _ : ℕ, ℤ) : ℤ :=
    if v.2 < 0 then (v.1 : ℤ) + (-v.2 - 1) * period n
    else -(v.1 : ℤ) + (v.2 + 1) * period n
  have hleft (p : ℤ) (hp : p ∈ negCrossing w) : f p ∈ (s : Set _) ∧ g (f p) = p := by
    rcases window_cases n p with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨i,k,hi,hin,rfl⟩ | ⟨i,k,hi,hin,rfl⟩
    · have hk : w (k * period n) = k * period n := by
        simpa only [zero_add, hw.zero] using hw.translate 0 k
      have h := hp.1
      have h' := hp.2
      rw [hk] at h'
      exact False.elim ((lt_asymm h) h')
    · have h := hp.1
      have h' : w _ < 0 := hp.2
      rw [hw.translate, hw.midpoint] at h'
      exact False.elim ((lt_asymm h) h')
    · obtain ⟨hI, hC⟩ := liftIndexCode_pos hi hin k
      have hk := (posShift_spec hw hi hin k).mp hp
      have hq : k + Q i < 0 := hk.2
      dsimp [f]
      rw [hI, hC, hmem]
      refine ⟨⟨⟨hi, hin⟩, by omega, by omega⟩, ?_⟩
      simp only [g, ite_eq_left (show -k-1 < 0 by omega)]
      rw [show -(-k-1)-1 = k by omega]
    · obtain ⟨hI, hC⟩ := liftIndexCode_neg hi hin k
      have hk := (negShift_spec hw hi hin k).mp hp
      have hq : k ≤ Q i := hk.2
      dsimp [f]
      rw [hI, hC, hmem]
      refine ⟨⟨⟨hi, hin⟩, by omega, by omega⟩, ?_⟩
      simp only [g, ite_eq_right (show ¬ k-1 < 0 by omega)]
      rw [sub_add_cancel]
  have hright (v : Σ _ : ℕ, ℤ) (hv : v ∈ (s : Set _)) :
      g v ∈ negCrossing w ∧ f (g v) = v := by
    obtain ⟨i,k⟩ := v
    obtain ⟨⟨hi,hin⟩, hklo, hkhi⟩ := (hmem i k).mp hv
    by_cases hk : k < 0
    · simp only [g, ite_eq_left hk]
      refine ⟨(posShift_spec hw hi hin _).mpr ⟨by omega, ?_⟩, ?_⟩
      · change -k - 1 + Q i < 0
        omega
      · obtain ⟨hI, hC⟩ := liftIndexCode_pos hi hin (n := n) (-k-1)
        simp only [f, hI, hC]
        congr 2
        omega
    · simp only [g, ite_eq_right hk]
      refine ⟨(negShift_spec hw hi hin _).mpr ⟨by omega, ?_⟩, ?_⟩
      · change k + 1 ≤ Q i
        omega
      · obtain ⟨hI, hC⟩ := liftIndexCode_neg hi hin (n := n) (k+1)
        simp only [f, hI, hC, add_sub_cancel_right]
  have hc := Set.ncard_congr (s := negCrossing w) (t := (s : Set _)) (fun p _ => f p)
    (fun p hp => (hleft p hp).1)
    (fun a b ha hb he => by rw [← (hleft a ha).2, he, (hleft b hb).2])
    (fun v hv => ⟨g v, (hright v hv).1, (hright v hv).2⟩)
  rw [Set.ncard_coe_finset, Finset.card_sigma] at hc
  rw [hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.card_Ico]
  change (max 0 (Q i) - min 0 (Q i)).toNat = (Q i).natAbs
  omega

end AffineB
```

### `AffineBReflections.lean`

```lean
import AffineBWindow
import AffineBLower

namespace AffineB

open scoped BigOperators

theorem swapCopy.symm' {n : ℕ} {x y a b : ℤ} (h : swapCopy n x y a b) :
    swapCopy n x y b a := by
  obtain ⟨k, h | h | h | h⟩ := h
  exacts [⟨k, Or.inr (Or.inl h.symm)⟩, ⟨k, Or.inl h.symm⟩,
    ⟨k, Or.inr (Or.inr (Or.inr h.symm))⟩, ⟨k, Or.inr (Or.inr (Or.inl h.symm))⟩]

private theorem swapCopy.neg {n : ℕ} {x y a b : ℤ} (h : swapCopy n x y a b) :
    swapCopy n x y (-a) (-b) := by
  obtain ⟨k, h | h | h | h⟩ := h
  all_goals
    refine ⟨-k, ?_⟩
    simp only [neg_mul]
    omega

private theorem swapCopy.add_period {n : ℕ} {x y a b : ℤ} (h : swapCopy n x y a b) :
    swapCopy n x y (a + period n) (b + period n) := by
  obtain ⟨k, h | h | h | h⟩ := h
  all_goals
    refine ⟨k+1, ?_⟩
    simp only [add_mul, one_mul]
    omega

private theorem swapCopy.sub_period {n : ℕ} {x y a b : ℤ} (h : swapCopy n x y a b) :
    swapCopy n x y (a - period n) (b - period n) := by
  obtain ⟨k, h | h | h | h⟩ := h
  all_goals
    refine ⟨k-1, ?_⟩
    simp only [sub_mul, one_mul]
    omega

structure SwapSpec (n : ℕ) (t : PermZ) (x y : ℤ) : Prop where
  signed : AffSigned n t
  swap : ∀ a b : ℤ, swapCopy n x y a b → t a = b
  fixed : ∀ a : ℤ, (¬ ∃ b : ℤ, swapCopy n x y a b) → t a = a

private theorem makeSwap (n : ℕ) (x y : ℤ)
    (hfun : ∀ a b c, swapCopy n x y a b → swapCopy n x y a c → b = c) :
    ∃ t : PermZ, SwapSpec n t x y := by
  classical
  let f (a : ℤ) : ℤ := if h : ∃ b, swapCopy n x y a b then h.choose else a
  have hf (a b : ℤ) (h : swapCopy n x y a b) : f a = b := by
    have he : ∃ b, swapCopy n x y a b := ⟨b,h⟩
    rw [show f a = he.choose by dsimp only [f]; rw [dite_eq_left he]]
    exact hfun a _ b he.choose_spec h
  have hfix (a : ℤ) (h : ¬ ∃ b, swapCopy n x y a b) : f a = a := by simp [f, h]
  have hinv : Function.Involutive f := by
    intro a
    by_cases h : ∃ b, swapCopy n x y a b
    · obtain ⟨b, hb⟩ := h
      rw [hf _ _ hb, hf _ _ hb.symm']
    · rw [hfix _ h, hfix _ h]
  refine ⟨⟨f, f, hinv, hinv⟩, ⟨?_, ?_⟩, hf, hfix⟩
  · intro a
    change f (-a) = -f a
    by_cases h : ∃ b, swapCopy n x y a b
    · obtain ⟨b,hb⟩ := h
      rw [hf _ _ hb, hf _ _ hb.neg]
    · have hn : ¬ ∃ b, swapCopy n x y (-a) b := by
        rintro ⟨b,hb⟩
        exact h ⟨-b, by simpa only [neg_neg] using hb.neg⟩
      rw [hfix _ h, hfix _ hn]
  · intro a
    change f (a + period n) = f a + period n
    by_cases h : ∃ b, swapCopy n x y a b
    · obtain ⟨b,hb⟩ := h
      rw [hf _ _ hb, hf _ _ hb.add_period]
    · have hn : ¬ ∃ b, swapCopy n x y (a + period n) b := by
        rintro ⟨b,hb⟩
        exact h ⟨b - period n, by simpa only [add_sub_cancel_right] using hb.sub_period⟩
      rw [hfix _ h, hfix _ hn]

private theorem period_separated (n : ℕ) (k : ℤ) :
    k ≠ 0 → 2 * (n : ℤ) < ((k * period n).natAbs : ℤ) := by
  intro h
  rw [Int.natAbs_mul]
  have hk : 1 ≤ k.natAbs := by omega
  have hp : ((period n).natAbs : ℤ) = period n := by have := period_pos n; omega
  have hh := Nat.mul_le_mul_right (period n).natAbs hk
  rw [one_mul] at hh
  have hN : period n = 2 * (n : ℤ) + 2 := rfl
  omega

private theorem representative_unique {n : ℕ} {u v k l : ℤ}
    (hu : u.natAbs ≤ n) (hv : v.natAbs ≤ n)
    (h : u + k * period n = v + l * period n) : u = v ∧ k = l := by
  have hz : (k-l) * period n = v-u := by rw [sub_mul]; omega
  have he : k-l = 0 := by
    by_contra hn
    have hl := period_separated n (k-l) hn
    rw [hz] at hl
    omega
  rw [he, zero_mul] at hz
  exact ⟨by omega, by omega⟩

private theorem smallSwap_functional {n : ℕ} {x y : ℤ} (hx : x.natAbs ≤ n)
    (hy : y.natAbs ≤ n) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x.natAbs ≠ y.natAbs) :
    ∀ a b c, swapCopy n x y a b → swapCopy n x y a c → b = c := by
  intro a b c hab hac
  obtain ⟨k, hk | hk | hk | hk⟩ := hab
  all_goals obtain ⟨l, hl | hl | hl | hl⟩ := hac
  all_goals
    have he := hk.1.symm.trans hl.1
    have h₁ := representative_unique (n := n) (by first | simpa using hx | simpa using hy)
      (by first | simpa using hx | simpa using hy) he
    have h₂ := h₁.2
    have h₃ := h₁.1
    have h₄ := hk.2
    have h₅ := hl.2
    omega

private theorem smallSwap_fixed {n : ℕ} {t : PermZ} {x y : ℤ} (ht : SwapSpec n t x y)
    (hx : x.natAbs ≤ n) (hy : y.natAbs ≤ n) {i : ℕ} (hi : i ≤ n)
    (hxi : i ≠ x.natAbs) (hyi : i ≠ y.natAbs) : t (i : ℤ) = (i : ℤ) := by
  apply ht.fixed
  rintro ⟨b,k,h | h | h | h⟩
  all_goals

    have he' := h.1
    rw [← add_zero (i : ℤ), ← zero_mul (period n)] at he'
    have hrep := representative_unique (n := n) (by simpa using hi)
      (by first | simpa using hx | simpa using hy) he'
    omega

private theorem swap_direct {n : ℕ} {x y : ℤ} : swapCopy n x y x y :=
  ⟨0, Or.inl ⟨by simp, by simp⟩⟩

private theorem floorMass_windowSwap {n a b : ℕ} {t : PermZ}
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ n)
    (h : ((t (a : ℤ) = (b : ℤ) ∧ t (b : ℤ) = (a : ℤ)) ∨
          (t (a : ℤ) = -(b : ℤ) ∧ t (b : ℤ) = -(a : ℤ))))
    (hfix : ∀ i : ℕ, i ≤ n → i ≠ a → i ≠ b → t (i : ℤ) = (i : ℤ)) :
    Even (∑ i ∈ Finset.Icc 1 n, floorMass n t i) := by
  classical
  let s := Finset.Icc 1 n
  have ha' : a ∈ s := Finset.mem_Icc.mpr ⟨ha, by omega⟩
  have hb' : b ∈ s.erase a := Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, hb⟩⟩
  rw [← Finset.sum_erase_add _ _ ha', ← Finset.sum_erase_add _ _ hb']
  have he : ∑ i ∈ (s.erase a).erase b, floorMass n t i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨hib, hi'⟩ := Finset.mem_erase.mp hi
    obtain ⟨hia, hi'⟩ := Finset.mem_erase.mp hi'
    have hin := (Finset.mem_Icc.mp hi').2
    rw [floorMass_small (by rw [hfix i hin hia hib]; omega),
      hfix i hin hia hib, ite_eq_right (by omega)]
  rw [he, zero_add]
  rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [floorMass_small (i := b) (by rw [h₂]; omega), floorMass_small (i := a) (by rw [h₁]; omega), h₁,h₂,
      ite_eq_right (by omega), ite_eq_right (by omega)]
    exact ⟨0, rfl⟩
  · rw [floorMass_small (i := b) (by rw [h₂]; omega), floorMass_small (i := a) (by rw [h₁]; omega), h₁,h₂,
      ite_eq_left (by omega), ite_eq_left (by omega)]
    exact ⟨1, rfl⟩

theorem windowSwap_exists (n a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ n)
    (neg : Bool) :
    ∃ t : PermZ, BRefl n t ∧
      t (a : ℤ) = (if neg then -(b : ℤ) else (b : ℤ)) ∧
      t (b : ℤ) = (if neg then -(a : ℤ) else (a : ℤ)) ∧
      (∀ i : ℕ, i ≤ n → i ≠ a → i ≠ b → t (i : ℤ) = (i : ℤ)) := by
  let y : ℤ := if neg then -(b : ℤ) else (b : ℤ)
  have hy : y.natAbs = b := by cases neg <;> simp [y]
  have hya : y.natAbs ≠ ((a : ℤ)).natAbs := by simp [hy]; omega
  obtain ⟨t, ht⟩ := makeSwap n (a : ℤ) y
    (smallSwap_functional (by simp; omega) (by omega) (by omega)
      (by intro h; rw [h] at hy; simp at hy; omega) hya.symm)
  have ht₁ : t (a : ℤ) = y := ht.swap _ _ swap_direct
  have ht₂ : t y = (a : ℤ) := ht.swap _ _ swap_direct.symm'
  have ht₂' : t (b : ℤ) = if neg then -(a : ℤ) else (a : ℤ) := by
    cases neg
    · exact ht₂
    · change t (-(b : ℤ)) = (a : ℤ) at ht₂
      rw [ht.signed.1] at ht₂
      change t (b : ℤ) = -(a : ℤ)
      omega
  have hfix : ∀ i : ℕ, i ≤ n → i ≠ a → i ≠ b → t (i : ℤ) = (i : ℤ) := by
    intro i hi hi₁ hi₂
    exact smallSwap_fixed ht (by simp; omega) (by omega) hi (by simpa using hi₁)
      (hy ▸ hi₂)
  have htB : AffB n t := by
    refine ⟨ht.signed, ?_⟩
    rw [ht.signed.negCrossing_sum_floor]
    apply floorMass_windowSwap ha hab hb _ hfix
    cases neg
    · exact Or.inl ⟨ht₁, ht₂'⟩
    · exact Or.inr ⟨ht₁, ht₂'⟩
  refine ⟨t, ⟨htB, (a : ℤ), y, ?_, ht.swap, ht.fixed⟩, ht₁, ht₂', hfix⟩
  intro h
  rw [← h] at hy
  simp at hy
  omega


private theorem mirror_copy {n : ℕ} {x a b : ℤ} :
    swapCopy n x (period n - x) a b ↔
      ∃ k : ℤ, (a = x + k * period n ∧ b = -x + (k+1) * period n) ∨
        (a = -x + k * period n ∧ b = x + (k-1) * period n) := by
  constructor
  · rintro ⟨k, h | h | h | h⟩
    · refine ⟨k, Or.inl ⟨h.1, ?_⟩⟩
      rw [add_mul, one_mul]
      omega
    · refine ⟨k+1, Or.inr ⟨?_, ?_⟩⟩
      · rw [add_mul, one_mul]
        omega
      · rw [add_sub_cancel_right]
        exact h.2
    · refine ⟨k, Or.inr ⟨h.1, ?_⟩⟩
      rw [sub_mul, one_mul]
      omega
    · refine ⟨k-1, Or.inl ⟨?_, ?_⟩⟩
      · rw [sub_mul, one_mul]
        omega
      · rw [sub_add_cancel]
        exact h.2
  · rintro ⟨k, h | h⟩
    · refine ⟨k, Or.inl ⟨h.1, ?_⟩⟩
      have hh := h.2
      rw [add_mul, one_mul] at hh
      omega
    · refine ⟨k, Or.inr (Or.inr (Or.inl ⟨h.1, ?_⟩))⟩
      have hh := h.2
      rw [sub_mul, one_mul] at hh
      omega

private theorem mirror_functional {n : ℕ} {x : ℤ} (hx : x.natAbs ≤ n) (hx0 : x ≠ 0) :
    ∀ a b c, swapCopy n x (period n - x) a b →
      swapCopy n x (period n - x) a c → b = c := by
  intro a b c hab hac
  obtain ⟨k, hk | hk⟩ := mirror_copy.mp hab
  all_goals obtain ⟨l, hl | hl⟩ := mirror_copy.mp hac
  all_goals
    have he := hk.1.symm.trans hl.1
    have h := representative_unique (n := n) (by simpa using hx) (by simpa using hx) he
    rcases h with ⟨he, rfl⟩
    first | exact hk.2.trans hl.2.symm | omega

theorem mirrorSwap_exists (n a : ℕ) (ha : 1 ≤ a) (han : a ≤ n) (neg : Bool) :
    ∃ t : PermZ, BRefl n t ∧
      t (a : ℤ) = (if neg then -period n - (a : ℤ) else period n - (a : ℤ)) ∧
      (∀ i : ℕ, i ≤ n → i ≠ a → t (i : ℤ) = (i : ℤ)) := by
  let x : ℤ := if neg then -(a : ℤ) else (a : ℤ)
  have hx : x.natAbs = a := by cases neg <;> simp [x]
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; simp at hx; omega
  have hN : period n = 2 * (n : ℤ) + 2 := rfl
  obtain ⟨t, ht⟩ := makeSwap n x (period n - x) (mirror_functional (by omega) hx0)
  have htx := ht.swap _ _ swap_direct
  have hta : t (a : ℤ) = if neg then -period n - (a : ℤ) else period n - (a : ℤ) := by
    cases neg
    · exact htx
    · change t (-(a : ℤ)) = period n - (-(a : ℤ)) at htx
      rw [ht.signed.1] at htx
      change t (a : ℤ) = -period n - (a : ℤ)
      omega
  have hfix : ∀ i : ℕ, i ≤ n → i ≠ a → t (i : ℤ) = (i : ℤ) := by
    intro i hi hia
    apply ht.fixed
    rintro ⟨b,hb⟩
    obtain ⟨k, h | h⟩ := mirror_copy.mp hb
    all_goals
      have he := h.1
      rw [← add_zero (i : ℤ), ← zero_mul (period n)] at he
      have hrep := representative_unique (n := n) (by simpa using hi)
        (by simpa only [Int.natAbs_neg, hx] using han) he
      have hh := congrArg Int.natAbs hrep.1
      simp [hx] at hh
      exact hia hh
  have hmass : Even (floorMass n t a) := by
    unfold floorMass
    rw [hta]
    cases neg
    · change Even ((period n - (a : ℤ)) / period n).natAbs
      rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      exact ⟨0, rfl⟩
    · change Even ((-period n - (a : ℤ)) / period n).natAbs
      have hq : (period n - (a : ℤ)) / period n = 0 :=
        Int.ediv_eq_zero_of_lt (by omega) (by omega)
      rw [show -period n - (a : ℤ) = (period n - (a : ℤ)) + (-2) * period n by omega,
        Int.add_mul_ediv_right _ _ (period_pos n).ne', hq]
      exact ⟨1, rfl⟩
  have htB : AffB n t := by
    refine ⟨ht.signed, ?_⟩
    rw [ht.signed.negCrossing_sum_floor]
    classical
    rw [← Finset.sum_erase_add _ _ (Finset.mem_Icc.mpr ⟨ha, han⟩)]
    have he : ∑ i ∈ (Finset.Icc 1 n).erase a, floorMass n t i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      obtain ⟨hia, hi⟩ := Finset.mem_erase.mp hi
      have hin := (Finset.mem_Icc.mp hi).2
      rw [floorMass_small (by rw [hfix i hin hia]; omega),
        hfix i hin hia, ite_eq_right (by omega)]
    rw [he, zero_add]
    exact hmass
  exact ⟨t, ⟨htB, x, period n - x, by have := hx; omega, ht.swap, ht.fixed⟩, hta, hfix⟩

end AffineB
```

### `AffineBSteps.lean`

```lean
import AffineBReflections

namespace AffineB

open scoped BigOperators

def Step (n : ℕ) (w t : PermZ) : Prop :=
  BRefl n t ∧ 0 < dis n t ∧ potential n (w * t) + dis n t = potential n w

theorem dis_one_support {n a : ℕ} {u v : PermZ}
    (ha : 1 ≤ a) (han : a ≤ n)
    (h : ∀ i : ℕ, 1 ≤ i → i ≤ n → i ≠ a → u (i : ℤ) = v (i : ℤ)) :
    dis n u + (v (a : ℤ) - (a : ℤ)).natAbs =
      dis n v + (u (a : ℤ) - (a : ℤ)).natAbs := by
  classical
  let s := Finset.Icc 1 n
  let f (i : ℕ) := (u (i : ℤ) - (i : ℤ)).natAbs
  let g (i : ℕ) := (v (i : ℤ) - (i : ℤ)).natAbs
  have ha' : a ∈ s := Finset.mem_Icc.mpr ⟨ha, han⟩
  have he : (∑ i ∈ s.erase a, f i) = ∑ i ∈ s.erase a, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hia, hi⟩ := Finset.mem_erase.mp hi
    obtain ⟨hil, hin⟩ := Finset.mem_Icc.mp hi
    simp only [f, g, h i hil hin hia]
  have hf := Finset.sum_erase_add s f ha'
  have hg := Finset.sum_erase_add s g ha'
  change (∑ i ∈ s, f i) + g a = (∑ i ∈ s, g i) + f a
  omega

theorem dis_two_support {n a b : ℕ} {u v : PermZ}
    (ha : 1 ≤ a) (hab : a < b) (hbn : b ≤ n)
    (h : ∀ i : ℕ, 1 ≤ i → i ≤ n → i ≠ a → i ≠ b → u (i : ℤ) = v (i : ℤ)) :
    dis n u + (v (a : ℤ) - (a : ℤ)).natAbs + (v (b : ℤ) - (b : ℤ)).natAbs =
      dis n v + (u (a : ℤ) - (a : ℤ)).natAbs + (u (b : ℤ) - (b : ℤ)).natAbs := by
  classical
  let s := Finset.Icc 1 n
  let f (i : ℕ) := (u (i : ℤ) - (i : ℤ)).natAbs
  let g (i : ℕ) := (v (i : ℤ) - (i : ℤ)).natAbs
  have ha' : a ∈ s := Finset.mem_Icc.mpr ⟨ha, by omega⟩
  have hb' : b ∈ s.erase a :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, hbn⟩⟩
  have he : (∑ i ∈ (s.erase a).erase b, f i) = ∑ i ∈ (s.erase a).erase b, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hib, hi⟩ := Finset.mem_erase.mp hi
    obtain ⟨hia, hi⟩ := Finset.mem_erase.mp hi
    obtain ⟨hil, hin⟩ := Finset.mem_Icc.mp hi
    simp only [f, g, h i hil hin hia hib]
  have hf := Finset.sum_erase_add s f ha'
  have hg := Finset.sum_erase_add s g ha'
  have hf' := Finset.sum_erase_add (s.erase a) f hb'
  have hg' := Finset.sum_erase_add (s.erase a) g hb'
  change (∑ i ∈ s, f i) + g a + g b = (∑ i ∈ s, g i) + f a + f b
  omega

theorem dis_identity (n : ℕ) : dis n (1 : PermZ) = 0 := by simp [dis]

theorem windowSwap_cost {n a b : ℕ} {t : PermZ} (ha : 1 ≤ a) (hab : a < b)
    (hbn : b ≤ n) {neg : Bool}
    (hta : t (a : ℤ) = if neg then -(b : ℤ) else (b : ℤ))
    (htb : t (b : ℤ) = if neg then -(a : ℤ) else (a : ℤ))
    (hfix : ∀ i : ℕ, i ≤ n → i ≠ a → i ≠ b → t (i : ℤ) = (i : ℤ)) :
    dis n t = 2 * (if neg then a+b else b-a) := by
  have h := dis_two_support (u := t) (v := 1) ha hab hbn (fun i _ hi => hfix i hi)
  change dis n t + ((a : ℤ) - (a : ℤ)).natAbs + ((b : ℤ) - (b : ℤ)).natAbs =
    dis n 1 + (t (a : ℤ) - (a : ℤ)).natAbs + (t (b : ℤ) - (b : ℤ)).natAbs at h
  rw [dis_identity, hta, htb] at h
  cases neg <;> simp at h ⊢ <;> omega

theorem windowSwap_efficient {n a b : ℕ} {w t : PermZ} (hw : AffSigned n w)
    (ha : 1 ≤ a) (hab : a < b) (hbn : b ≤ n) {neg : Bool}
    (hta : t (a : ℤ) = if neg then -(b : ℤ) else (b : ℤ))
    (htb : t (b : ℤ) = if neg then -(a : ℤ) else (a : ℤ))
    (hfix : ∀ i : ℕ, i ≤ n → i ≠ a → i ≠ b → t (i : ℤ) = (i : ℤ))
    (hcross : if neg then (b : ℤ) ≤ -w (a : ℤ) ∧ w (b : ℤ) ≤ -(a : ℤ)
      else (b : ℤ) ≤ w (a : ℤ) ∧ w (b : ℤ) ≤ (a : ℤ)) :
    dis n (w * t) + dis n t = dis n w := by
  have h := dis_two_support (u := w * t) (v := w) ha hab hbn (by
    intro i _ hin hia hib
    change w (t (i : ℤ)) = w (i : ℤ)
    rw [hfix i hin hia hib])
  change dis n (w*t) + (w (a : ℤ) - (a : ℤ)).natAbs + (w (b : ℤ) - (b : ℤ)).natAbs =
    dis n w + (w (t (a : ℤ)) - (a : ℤ)).natAbs + (w (t (b : ℤ)) - (b : ℤ)).natAbs at h
  rw [hta, htb] at h
  rw [windowSwap_cost ha hab hbn hta htb hfix]
  cases neg
  · change (b : ℤ) ≤ w (a : ℤ) ∧ w (b : ℤ) ≤ (a : ℤ) at hcross
    change dis n (w*t) + (w (a : ℤ) - (a : ℤ)).natAbs + (w (b : ℤ) - (b : ℤ)).natAbs =
      dis n w + (w (b : ℤ) - (a : ℤ)).natAbs + (w (a : ℤ) - (b : ℤ)).natAbs at h
    change dis n (w*t) + 2*(b-a) = dis n w
    omega
  · change (b : ℤ) ≤ -w (a : ℤ) ∧ w (b : ℤ) ≤ -(a : ℤ) at hcross
    change dis n (w*t) + (w (a : ℤ) - (a : ℤ)).natAbs + (w (b : ℤ) - (b : ℤ)).natAbs =
      dis n w + (w (-(b : ℤ)) - (a : ℤ)).natAbs + (w (-(a : ℤ)) - (b : ℤ)).natAbs at h
    rw [hw.1, hw.1] at h
    change dis n (w*t) + 2*(a+b) = dis n w
    omega

theorem mirrorSwap_cost {n a : ℕ} {t : PermZ} (ha : 1 ≤ a) (han : a ≤ n) {neg : Bool}
    (hta : t (a : ℤ) = if neg then -period n - (a : ℤ) else period n - (a : ℤ))
    (hfix : ∀ i : ℕ, i ≤ n → i ≠ a → t (i : ℤ) = (i : ℤ)) :
    dis n t = if neg then 2 * (n+1+a) else 2 * (n+1-a) := by
  have h := dis_one_support (u := t) (v := 1) ha han (fun i _ hi => hfix i hi)
  change dis n t + ((a : ℤ) - (a : ℤ)).natAbs =
    dis n 1 + (t (a : ℤ) - (a : ℤ)).natAbs at h
  rw [dis_identity, hta] at h
  cases neg <;> simp [period] at h ⊢ <;> omega

theorem mirrorSwap_efficient {n a : ℕ} {w t : PermZ} (hw : AffSigned n w)
    (ha : 1 ≤ a) (han : a ≤ n) {neg : Bool}
    (hta : t (a : ℤ) = if neg then -period n - (a : ℤ) else period n - (a : ℤ))
    (hfix : ∀ i : ℕ, i ≤ n → i ≠ a → t (i : ℤ) = (i : ℤ))
    (hcross : if neg then w (a : ℤ) ≤ -period n - (a : ℤ)
      else period n - (a : ℤ) ≤ w (a : ℤ)) :
    dis n (w * t) + dis n t = dis n w := by
  have h := dis_one_support (u := w * t) (v := w) ha han (by
    intro i _ hin hia
    change w (t (i : ℤ)) = w (i : ℤ)
    rw [hfix i hin hia])
  change dis n (w*t) + (w (a : ℤ) - (a : ℤ)).natAbs =
    dis n w + (w (t (a : ℤ)) - (a : ℤ)).natAbs at h
  rw [hta] at h
  rw [mirrorSwap_cost ha han hta hfix]
  have hN : period n = 2 * (n : ℤ) + 2 := rfl
  cases neg
  · change period n - (a : ℤ) ≤ w (a : ℤ) at hcross
    change dis n (w*t) + (w (a : ℤ) - (a : ℤ)).natAbs =
      dis n w + (w (period n - (a : ℤ)) - (a : ℤ)).natAbs at h
    rw [hw.mirror] at h
    change dis n (w*t) + 2*(n+1-a) = dis n w
    omega
  · change w (a : ℤ) ≤ -period n - (a : ℤ) at hcross
    change dis n (w*t) + (w (a : ℤ) - (a : ℤ)).natAbs =
      dis n w + (w (-period n - (a : ℤ)) - (a : ℤ)).natAbs at h
    rw [show -period n - (a : ℤ) = -(a : ℤ) - period n by omega, hw.sub_period, hw.1] at h
    change dis n (w*t) + 2*(n+1+a) = dis n w
    omega

theorem prefix_agree {n j : ℕ} {u w : PermZ} (hu : AffSigned n u) (hw : AffSigned n w)
    (h : ∀ i : ℕ, 1 ≤ i → i ≤ j → u (i : ℤ) = w (i : ℤ)) :
    Good u j ↔ Good w j := by
  rw [hu.good_iff_window, hw.good_iff_window]
  simp only [Finset.mem_Icc]
  exact ⟨fun H i hi => h i hi.1 hi.2 ▸ H i hi, fun H i hi => (h i hi.1 hi.2).symm ▸ H i hi⟩

theorem prefix_neg_agree {j : ℕ} {u w : PermZ}
    (h : ∀ i : ℕ, 1 ≤ i → i ≤ j → (u (i : ℤ) < 0 ↔ w (i : ℤ) < 0)) :
    negPrefix u j = negPrefix w j := by
  unfold negPrefix
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact and_congr_right fun hi => h i hi.1 hi.2

theorem prefix_neg_split (w : PermZ) {a b : ℕ} (hab : a ≤ b) :
    negPrefix w b = negPrefix w a +
      ∑ i ∈ Finset.Ioc a b, (if w (i : ℤ) < 0 then 1 else 0) := by
  classical
  have h : Finset.Icc 1 b = Finset.Icc 1 a ∪ Finset.Ioc a b := by ext i; simp; omega
  have hd : Disjoint (Finset.Icc 1 a) (Finset.Ioc a b) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_Ioc] at hj
    omega
  unfold negPrefix
  rw [h, Finset.filter_union, Finset.card_union_of_disjoint
    (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
  simp

theorem prefix_neg_extend {w : PermZ} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ i : ℕ, a < i → i ≤ b → 0 ≤ w (i : ℤ)) :
    negPrefix w b = negPrefix w a := by
  rw [prefix_neg_split w hab]
  have he : ∑ i ∈ Finset.Ioc a b, (if w (i : ℤ) < 0 then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨hia, hib⟩ := Finset.mem_Ioc.mp hi
    exact ite_eq_right (not_lt.mpr (h i hia hib))
  rw [he, add_zero]

theorem prefix_neg_succ (w : PermZ) (a : ℕ) :
    negPrefix w (a+1) = negPrefix w a + (if w ((a+1 : ℕ) : ℤ) < 0 then 1 else 0) := by
  rw [prefix_neg_split w (Nat.le_succ a)]
  have h : Finset.Ioc a (a+1) = {a+1} := by ext i; simp
  rw [h, Finset.sum_singleton]

theorem good_extend {n a b : ℕ} {w : PermZ} (hw : AffSigned n w)
    (ha : Good w a) (hab : a ≤ b)
    (h : ∀ i : ℕ, a < i → i ≤ b → (w (i : ℤ)).natAbs ≤ b) : Good w b := by
  rw [hw.good_iff_window]
  intro i hi
  obtain ⟨hil, hib⟩ := Finset.mem_Icc.mp hi
  by_cases hia : i ≤ a
  · exact le_trans ((ha (i : ℤ)).mp (by simpa using hia)) hab
  · exact h i (by omega) hib

theorem good_shrink_fixed {n a b : ℕ} {w : PermZ} (hw : AffSigned n w)
    (hb : Good w b) (hab : a ≤ b)
    (h : ∀ i : ℕ, a < i → i ≤ b → w (i : ℤ) = (i : ℤ)) : Good w a := by
  rw [hw.good_iff_window]
  intro i hi
  obtain ⟨hil, hia⟩ := Finset.mem_Icc.mp hi
  have hval := (hb (i : ℤ)).mp (by simp; omega)
  by_contra! hv
  let k := (w (i : ℤ)).natAbs
  have hfix := h k hv hval
  have he : w (i : ℤ) = (k : ℤ) ∨ w (i : ℤ) = -(k : ℤ) := by dsimp [k]; omega
  rcases he with he | he
  · have hz := w.injective (he.trans hfix.symm)
    change (i : ℤ) = (k : ℤ) at hz
    change a < k at hv
    omega
  · have hn : w (-(k : ℤ)) = -(k : ℤ) := by rw [hw.1, hfix]
    have hz := w.injective (he.trans hn.symm)
    change (i : ℤ) = -(k : ℤ) at hz
    omega

theorem negCrossing_eq_negPrefix {n : ℕ} {w : PermZ}
    (hw : AffSigned n w) (hg : Good w n) :
    (negCrossing w).ncard = negPrefix w n := by
  rw [hw.negCrossing_sum_floor, negPrefix]
  have hcount := Finset.sum_boole (R := ℕ) (fun i : ℕ => w (i : ℤ) < 0) (Finset.Icc 1 n)
  change (∑ i ∈ Finset.Icc 1 n, (if w (i : ℤ) < 0 then 1 else 0)) =
    ((Finset.Icc 1 n).filter (fun i : ℕ => w (i : ℤ) < 0)).card at hcount
  rw [← hcount]
  apply Finset.sum_congr rfl
  intro i hi
  have hv := (hg (i : ℤ)).mp (by simpa using (Finset.mem_Icc.mp hi).2)
  exact floorMass_small (by omega)

theorem oddGood_below {n q j : ℕ} {w : PermZ} (hw : AffB n w)
    (hfix : ∀ i : ℕ, q < i → i ≤ n → w (i : ℤ) = (i : ℤ))
    (hj : j ≤ n) (hjq : q ≤ j) (hg : Good w j) : Even (negPrefix w j) := by
  have hf : Good w n := good_extend hw.1 hg hj (by
    intro i hi hin
    rw [hfix i (by omega) hin]
    simpa using hin)
  have he := prefix_neg_extend hj (w := w) (by
    intro i hi hin
    rw [hfix i (by omega) hin]
    omega)
  have hh := hw.2
  rwa [negCrossing_eq_negPrefix hw.1 hf, he] at hh

theorem windowSwap_good_above {n a b j : ℕ} {t : PermZ}
    (ht : AffSigned n t) (_ha : 1 ≤ a) (hab : a < b) (hbj : b ≤ j) (hjn : j ≤ n)
    {neg : Bool}
    (hta : t (a : ℤ) = if neg then -(b : ℤ) else (b : ℤ))
    (htb : t (b : ℤ) = if neg then -(a : ℤ) else (a : ℤ))
    (hfix : ∀ i : ℕ, i ≤ n → i ≠ a → i ≠ b → t (i : ℤ) = (i : ℤ)) :
    Good t j := by
  rw [ht.good_iff_window]
  intro i hi
  have hij := (Finset.mem_Icc.mp hi).2
  by_cases hia : i = a
  · subst i
    rw [hta]
    cases neg <;> simpa using hbj
  by_cases hib : i = b
  · subst i
    rw [htb]
    cases neg <;> simpa using (show a ≤ j by omega)
  rw [hfix i (by omega) hia hib]
  simpa using hij

theorem repaired_step {n g q : ℕ} {w t : PermZ} (hw : AffB n w) (ht : BRefl n t)
    (hwfix : ∀ i : ℕ, q < i → i ≤ n → w (i : ℤ) = (i : ℤ))
    (tlow : ∀ i : ℕ, 1 ≤ i → i ≤ g → t (i : ℤ) = (i : ℤ))
    (thigh : ∀ i : ℕ, q < i → i ≤ n → t (i : ℤ) = (i : ℤ))
    (hnone : ∀ j : ℕ, g < j → j < q → ¬ Good w j)
    (hrepair : ∀ j : ℕ, g < j → j < q → Good (w * t) j → Even (negPrefix (w * t) j))
    (hdis : dis n (w * t) + dis n t = dis n w) (hpos : 0 < dis n t) :
    Step n w t := by
  classical
  have hB := hw.mul ht.1
  have he : oddGoods n (w * t) = oddGoods n w := by
    ext j
    simp only [oddGoods, Finset.mem_filter, Finset.mem_Ico, OddGood]
    apply and_congr_right
    intro hj
    by_cases hgj : j ≤ g
    · have h (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) : (w * t) (i : ℤ) = w (i : ℤ) := by
        change w (t (i : ℤ)) = _
        rw [tlow i hi (hij.trans hgj)]
      rw [prefix_agree hB.1 hw.1 h, prefix_neg_agree (u := w*t) (w := w) (fun i hi hij => by rw [h i hi hij])]
    · by_cases hjq : j < q
      · exact ⟨fun h => False.elim (h.2 (hrepair j (by omega) hjq h.1)),
          fun h => False.elim (hnone j (by omega) hjq h.1)⟩
      · have hfix' (i : ℕ) (hi : q < i) (hin : i ≤ n) : (w*t) (i : ℤ) = (i : ℤ) := by
          change w (t (i : ℤ)) = _
          rw [thigh i hi hin, hwfix i hi hin]
        exact ⟨fun h => False.elim (h.2 (oddGood_below hB hfix' (by omega) (by omega) h.1)),
          fun h => False.elim (h.2 (oddGood_below hw hwfix (by omega) (by omega) h.1))⟩
  refine ⟨ht, hpos, ?_⟩
  unfold potential
  rw [he]
  omega


theorem crossing_single_after {n a b : ℕ} {w : PermZ} (hw : AffSigned n w)
    (ha : Good w a) (hab : a < b) (hbn : b ≤ n)
    (h : ∀ i : ℕ, a < i → i ≤ n → i ≠ b → 0 ≤ w (i : ℤ) ∧ w (i : ℤ) ≤ n) :
    (negCrossing w).ncard = negPrefix w a + floorMass n w b := by
  classical
  rw [hw.negCrossing_sum_floor]
  have hs : Finset.Icc 1 n = Finset.Icc 1 a ∪ Finset.Ioc a n := by ext i; simp; omega
  have hd : Disjoint (Finset.Icc 1 a) (Finset.Ioc a n) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (Finset.mem_Icc.mp hi).2) (Finset.mem_Ioc.mp hj).1
  rw [hs, Finset.sum_union hd]
  have he : ∑ i ∈ Finset.Ioc a n, floorMass n w i = floorMass n w b := by
    apply Finset.sum_eq_single b
    · intro i hi hib
      obtain ⟨hia,hin⟩ := Finset.mem_Ioc.mp hi
      have hv := h i hia hin hib
      rw [floorMass_small (by omega), ite_eq_right (by omega)]
    · intro hh
      exact False.elim (hh (Finset.mem_Ioc.mpr ⟨hab,hbn⟩))
  rw [he]
  congr 1
  unfold negPrefix
  have hcount : (∑ i ∈ Finset.Icc 1 a, (if w (i : ℤ) < 0 then 1 else 0)) =
      ((Finset.Icc 1 a).filter (fun i : ℕ => w (i : ℤ) < 0)).card :=
    Finset.sum_boole (R := ℕ) (fun i : ℕ => w (i : ℤ) < 0) (Finset.Icc 1 a)
  rw [← hcount]
  apply Finset.sum_congr rfl
  intro i hi
  have hv := (ha (i : ℤ)).mp (by simpa using (Finset.mem_Icc.mp hi).2)
  exact floorMass_small (by omega)

end AffineB
```

### `AffineBActive.lean`

```lean
import AffineBSteps
import Mathlib.Data.Nat.Find

namespace AffineB

structure Active (n : ℕ) (w : PermZ) (g q : ℕ) : Prop where
  mem : AffB n w
  lt : g < q
  last_le : q ≤ n
  last_moved : w (q : ℤ) ≠ (q : ℤ)
  tail_fixed : ∀ i : ℕ, q < i → i ≤ n → w (i : ℤ) = (i : ℤ)
  lower_good : Good w g
  no_mid_good : ∀ j : ℕ, g < j → j < q → ¬ Good w j
  next_positive : ¬ Even (negPrefix w g) → 0 < w ((g+1 : ℕ) : ℤ)

theorem good_zero {n : ℕ} {w : PermZ} (hw : AffSigned n w) : Good w 0 := by
  rw [hw.good_iff_window]
  intro i hi
  have := Finset.mem_Icc.mp hi
  omega

theorem negPrefix_zero (w : PermZ) : negPrefix w 0 = 0 := by
  unfold negPrefix
  rw [Finset.Icc_eq_empty (by decide : ¬ (1 : ℕ) ≤ 0), Finset.filter_empty, Finset.card_empty]

theorem Active.first_moved {n g q : ℕ} {w : PermZ} (h : Active n w g q) :
    w ((g+1 : ℕ) : ℤ) ≠ ((g+1 : ℕ) : ℤ) := by
  intro he
  have hq := h.lt
  by_cases hm : g+1 = q
  · exact h.last_moved (hm ▸ he)
  · apply h.no_mid_good (g+1) (by omega) (by omega)
    apply good_extend h.mem.1 h.lower_good (by omega)
    intro i hi hi'
    have h' : i = g+1 := by omega
    subst i
    change (w ((g+1 : ℕ) : ℤ)).natAbs ≤ g+1
    rw [he]
    omega

theorem last_moved_exists {n : ℕ} {w : PermZ} (hw : AffSigned n w) (hne : w ≠ 1) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ n ∧ w (q : ℤ) ≠ (q : ℤ) ∧
      (∀ i : ℕ, q < i → i ≤ n → w (i : ℤ) = (i : ℤ)) := by
  classical
  have hm : ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ w (i : ℤ) ≠ (i : ℤ) := by
    by_contra! h
    apply hne (hw.window_ext (affSigned_one n) ?_)
    intro i hi
    obtain ⟨hil, hin⟩ := Finset.mem_Icc.mp hi
    exact h i hil hin
  obtain ⟨i, hi, hin, hiw⟩ := hm
  let Q (i : ℕ) := 1 ≤ i ∧ w (i : ℤ) ≠ (i : ℤ)
  let q := Nat.findGreatest Q n
  have hq : Q q := Nat.findGreatest_spec hin ⟨hi, hiw⟩
  refine ⟨q, hq.1, Nat.findGreatest_le _, hq.2, fun j hj hjn => ?_⟩
  by_contra he
  have hb : j ≤ q := Nat.le_findGreatest hjn (show Q j from ⟨by omega, he⟩)
  omega

theorem active_of_no_r1 {n q : ℕ} {w : PermZ} (hw : AffB n w)
    (hql : 1 ≤ q) (hq : q ≤ n) (hm : w (q : ℤ) ≠ (q : ℤ))
    (hfix : ∀ i : ℕ, q < i → i ≤ n → w (i : ℤ) = (i : ℤ))
    (hR : ¬ ∃ j : ℕ, 1 ≤ j ∧ j < n ∧ OddGood w j ∧
      (∀ k : ℕ, j < k → k < n → ¬ OddGood w k) ∧ w ((j+1 : ℕ) : ℤ) < 0) :
    ∃ g, Active n w g q := by
  classical
  let g := Nat.findGreatest (Good w) (q-1)
  have hg : Good w g := Nat.findGreatest_spec (Nat.zero_le _) (good_zero hw.1)
  have hgl : g ≤ q-1 := Nat.findGreatest_le _
  have hnone : ∀ j : ℕ, g < j → j < q → ¬ Good w j := by
    intro j hgj hjq hj
    have h := Nat.le_findGreatest (by omega : j ≤ q-1) hj
    change j ≤ g at h
    omega
  refine ⟨g, hw, by omega, hq, hm, hfix, hg, hnone, ?_⟩
  intro hodd
  have hg1 : 1 ≤ g := by
    by_contra! h
    have h' : g = 0 := by omega
    rw [h', negPrefix_zero] at hodd
    exact hodd ⟨0,rfl⟩
  have hno : ∀ k : ℕ, g < k → k < n → ¬ OddGood w k := by
    intro k hk hkn ho
    by_cases hkq : k < q
    · exact hnone k hk hkq ho.1
    · exact ho.2 (oddGood_below hw hfix (by omega) (by omega) ho.1)
  have hn := hw.1.nonzero (show ((g+1 : ℕ) : ℤ) ≠ 0 by omega)
  by_contra! h
  exact hR ⟨g, hg1, by omega, ⟨hg, hodd⟩, hno, by omega⟩

theorem step_r1 {n a : ℕ} {w : PermZ} (hw : AffB n w)
    (ha : 1 ≤ a) (han : a < n) (hao : OddGood w a)
    (_hlast : ∀ k : ℕ, a < k → k < n → ¬ OddGood w k)
    (hneg : w ((a+1 : ℕ) : ℤ) < 0) : ∃ t, Step n w t := by
  classical
  let b := a+1
  have hab : a < b := by omega
  have hbn : b ≤ n := by omega
  obtain ⟨t, ht, hta, htb, hfix⟩ := windowSwap_exists n a b ha hab hbn false
  change t (a : ℤ) = (b : ℤ) at hta
  change t (b : ℤ) = (a : ℤ) at htb
  have hdis : dis n t = 2 := by
    have htCost := windowSwap_cost (neg := false) ha hab hbn hta htb hfix
    change dis n t = 2 * (b-a) at htCost
    omega
  have hwa := (hao.1 (a : ℤ)).mp (by simp)
  have hwb : a < (w (b : ℤ)).natAbs := by
    by_contra! h
    have hh := (hao.1 (b : ℤ)).mpr h
    change b ≤ a at hh
    omega
  have hvdis : dis n (w*t) = dis n w := by
    have hh := dis_two_support (u := w*t) (v := w) ha hab hbn (by
      intro i _ hin hia hib
      change w (t (i : ℤ)) = _
      rw [hfix i hin hia hib])
    change dis n (w*t) + (w (a : ℤ) - (a : ℤ)).natAbs + (w (b : ℤ) - (b : ℤ)).natAbs =
      dis n w + (w (t (a : ℤ)) - (a : ℤ)).natAbs + (w (t (b : ℤ)) - (b : ℤ)).natAbs at hh
    rw [hta,htb] at hh
    have h' : w (b : ℤ) < 0 := hneg
    omega
  have hset : oddGoods n (w*t) = (oddGoods n w).erase a := by
    ext j
    simp only [oddGoods, Finset.mem_erase, Finset.mem_filter, Finset.mem_Ico, OddGood]
    by_cases hja : j = a
    · subst j
      have he : ¬ Good (w*t) a := by
        intro hg
        have hh := (hg (a : ℤ)).mp (by simp)
        change (w (t (a : ℤ))).natAbs ≤ a at hh
        rw [hta] at hh
        omega
      simp [he]
    · rw [show (j ≠ a) = True from eq_true hja, true_and]
      apply and_congr_right
      intro hj
      by_cases hlt : j < a
      · have h (i : ℕ) (_hi : 1 ≤ i) (hij : i ≤ j) :
            (w*t) (i : ℤ) = w (i : ℤ) := by
          change w (t (i : ℤ)) = _
          rw [hfix i (by omega) (by omega) (by omega)]
        rw [prefix_agree (hw.1.mul ht.1.1) hw.1 h,
          prefix_neg_agree (u := w*t) (w := w) (fun i hi hij => by rw [h i hi hij])]
      · have hgt : a < j := by omega
        have hg := windowSwap_good_above (neg := false) ht.1.1 ha hab
          (by omega : b ≤ j) (by omega : j ≤ n) hta htb hfix
        have hpar := prefix_parity_mul hw.1 ht.1.1 hg
        have htneg : negPrefix t j = 0 := by
          rw [prefix_neg_extend (a := 0) (w := t) (Nat.zero_le j) (by
            intro i hil hij
            by_cases hia : i = a
            · subst i; rw [hta]; omega
            by_cases hib : i = b
            · subst i; rw [htb]; omega
            rw [hfix i (by omega) hia hib]
            omega)]
          exact negPrefix_zero t
        have he : Even (negPrefix (w*t) j) ↔ Even (negPrefix w j) := by
          rw [htneg, add_zero] at hpar
          simp only [Nat.even_iff, hpar]
        rw [good_mul_iff hg, he]
  have haa : a ∈ oddGoods n w := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ha,han⟩, hao⟩
  have hc := Finset.card_erase_add_one haa
  refine ⟨t, ht, by omega, ?_⟩
  unfold potential
  rw [hset, hvdis, hdis]
  omega

theorem Active.step_rightmost {n g q : ℕ} {w : PermZ} (h : Active n w g q)
    (hex : (q : ℤ) < w (q : ℤ)) : ∃ t, Step n w t := by
  have hq : 1 ≤ q := by have := h.lt; omega
  have hN : period n = 2 * (n : ℤ) + 2 := rfl
  have hcross : period n - (q : ℤ) ≤ w (q : ℤ) := by
    by_contra! hc
    let z := w (q : ℤ)
    have hz1 : (q : ℤ) < z := hex
    have hz2 : z < period n - (q : ℤ) := hc
    have hfix : w z = z := by
      rcases lt_trichotomy z ((n : ℤ)+1) with hl | hm | hr
      · have he : (z.toNat : ℤ) = z := by omega
        simpa only [he] using h.tail_fixed z.toNat (by omega) (by omega)
      · rw [hm, h.mem.1.midpoint]
      · let i := (period n - z).toNat
        have he : (i : ℤ) = period n-z := by dsimp [i]; omega
        have hfix := h.tail_fixed i (by omega) (by omega)
        have he' : z = period n - (i : ℤ) := by omega
        rw [he', h.mem.1.mirror, hfix]
    have he : z = (q : ℤ) := w.injective (hfix.trans (show z = w (q : ℤ) from rfl))
    omega
  obtain ⟨t, ht, hta, hfix⟩ := mirrorSwap_exists n q hq h.last_le false
  have hc := mirrorSwap_cost (neg := false) hq h.last_le hta hfix
  change dis n t = 2 * (n+1-q) at hc
  refine ⟨t, repaired_step h.mem ht h.tail_fixed ?_ ?_ h.no_mid_good ?_
    (mirrorSwap_efficient (neg := false) h.mem.1 hq h.last_le hta hfix hcross) (by have := h.last_le; omega)⟩
  · intro i _ hi
    exact hfix i (by have := h.lt; have := h.last_le; omega) (by have := h.lt; omega)
  · intro i hi hin
    exact hfix i hin (by omega)
  · intro j hgj hjq hj
    apply False.elim (h.no_mid_good j hgj hjq ?_)
    apply (prefix_agree (h.mem.1.mul ht.1.1) h.mem.1 ?_).mp hj
    intro i _ hij
    change w (t (i : ℤ)) = _
    rw [hfix i (by have := h.last_le; omega) (by omega)]

end AffineB
```

### `AffineBPartners.lean`

```lean
import AffineBActive

namespace AffineB

structure PositiveSwap (n a b : ℕ) (t : PermZ) : Prop where
  refl : BRefl n t
  left : t (a : ℤ) = (b : ℤ)
  right : t (b : ℤ) = (a : ℤ)
  fixed : ∀ i : ℕ, i ≤ n → i ≠ a → i ≠ b → t (i : ℤ) = (i : ℤ)

private theorem PositiveSwap.exists (n a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hbn : b ≤ n) :
    ∃ t, PositiveSwap n a b t := by
  obtain ⟨t,ht,h₁,h₂,h₃⟩ := windowSwap_exists n a b ha hab hbn false
  exact ⟨t, ht, h₁,h₂,h₃⟩

private theorem PositiveSwap.repair_range {n g q a b j : ℕ} {w t : PermZ}
    (h : Active n w g q) (ht : PositiveSwap n a b t)
    (hga : g < a) (hab : a < b) (hbq : b ≤ q)
    (hgj : g < j) (hjq : j < q) (hv : Good (w*t) j) : a ≤ j ∧ j < b := by
  have hq := h.last_le
  have hl : a ≤ j := by
    by_contra! hja
    apply h.no_mid_good j hgj hjq
    apply (prefix_agree (h.mem.1.mul ht.refl.1.1) h.mem.1 ?_).mp hv
    intro i _ hij
    change w (t (i : ℤ)) = _
    rw [ht.fixed i (by omega) (by omega) (by omega)]
  refine ⟨hl, ?_⟩
  by_contra! hbj
  have hh := windowSwap_good_above (neg := false) ht.refl.1.1
    (by omega : 1 ≤ a) hab hbj (by omega) ht.left ht.right ht.fixed
  exact h.no_mid_good j hgj hjq ((good_mul_iff hh).mp hv)

private theorem PositiveSwap.repair {n g q a b : ℕ} {w t : PermZ}
    (h : Active n w g q) (ht : PositiveSwap n a b t)
    (hga : g < a) (hab : a < b) (hbq : b ≤ q)
    (hcross : (b : ℤ) ≤ w (a : ℤ) ∧ w (b : ℤ) ≤ (a : ℤ))
    (hpar : ∀ j : ℕ, g < j → j < q → Good (w*t) j → Even (negPrefix (w*t) j)) :
    Step n w t := by
  have hq := h.last_le
  have ha : 1 ≤ a := by omega
  have hb : b ≤ n := by omega
  have hc := windowSwap_cost (neg := false) ha hab hb ht.left ht.right ht.fixed
  change dis n t = 2 * (b-a) at hc
  refine repaired_step h.mem ht.refl h.tail_fixed ?_ ?_ h.no_mid_good hpar
    (windowSwap_efficient (neg := false) h.mem.1 ha hab hb ht.left ht.right ht.fixed hcross)
    (by omega)
  · intro i _ hi
    exact ht.fixed i (by omega) (by omega) (by omega)
  · intro i hi hin
    exact ht.fixed i hin (by omega) (by omega)

private theorem last_transition {n g q : ℕ} {w : PermZ} (h : Active n w g q)
    (hqA : w (q : ℤ) < (q : ℤ))
    (hE : ∃ i : ℕ, g < i ∧ i ≤ q ∧ (i : ℤ) < w (i : ℤ)) :
    ∃ a b : ℕ, g < a ∧ a < b ∧ b ≤ q ∧
      ((b : ℤ) ≤ w (a : ℤ) ∧ w (b : ℤ) ≤ (a : ℤ)) ∧
      (∀ i : ℕ, a < i → i < b → w (i : ℤ) = (i : ℤ)) ∧
      (∀ i : ℕ, b < i → i ≤ n → w (i : ℤ) ≤ (i : ℤ)) := by
  classical
  obtain ⟨i, hgi, hiq, hiE⟩ := hE
  let P (i : ℕ) := g < i ∧ (i : ℤ) < w (i : ℤ)
  let a := Nat.findGreatest P q
  have ha : P a := Nat.findGreatest_spec hiq ⟨hgi,hiE⟩
  obtain ⟨hga,haE⟩ := ha
  have haq : a ≤ q := Nat.findGreatest_le _
  have haq' : a < q := by
    by_contra! hh
    have he : a = q := by omega
    rw [he] at haE
    omega
  have hexc (i : ℕ) (hai : a < i) (hiq : i ≤ q) : w (i : ℤ) ≤ (i : ℤ) := by
    by_contra! hi
    have hh : i ≤ a := Nat.le_findGreatest hiq (show P i from ⟨by omega,hi⟩)
    omega
  let Q (i : ℕ) := a < i ∧ i ≤ q ∧ w (i : ℤ) ≠ (i : ℤ)
  have hex : ∃ i, Q i := ⟨q,haq',le_rfl,h.last_moved⟩
  let b := Nat.find hex
  have hb : Q b := Nat.find_spec hex
  obtain ⟨hab,hbq,hbm⟩ := hb
  have hfix (i : ℕ) (hai : a < i) (hib : i < b) : w (i : ℤ) = (i : ℤ) := by
    by_contra hn
    have hh : b ≤ i := Nat.find_min' hex (show Q i from ⟨hai, by omega, hn⟩)
    omega
  have hbA := hexc b hab hbq
  have hcross : (b : ℤ) ≤ w (a : ℤ) ∧ w (b : ℤ) ≤ (a : ℤ) := by
    constructor
    · by_contra! hh
      let k := (w (a : ℤ)).toNat
      have hk : (k : ℤ) = w (a : ℤ) := by dsimp [k]; omega
      have hf := hfix k (by omega) (by omega)
      have hz := w.injective (hf.trans hk)
      change (k : ℤ) = (a : ℤ) at hz
      omega
    · by_contra! hh
      let k := (w (b : ℤ)).toNat
      have hk : (k : ℤ) = w (b : ℤ) := by dsimp [k]; omega
      have hf := hfix k (by omega) (by omega)
      have hz := w.injective (hf.trans hk)
      change (k : ℤ) = (b : ℤ) at hz
      omega
  exact ⟨a,b,hga,hab,hbq,hcross,hfix,fun i hi hin =>
    if hiq : i ≤ q then hexc i (by omega) hiq else le_of_eq (h.tail_fixed i (by omega) hin)⟩

private theorem partner_prefix_parity {a b j : ℕ} {w v v₁ : PermZ}
    (ha : 1 ≤ a) (hab : a < b) (hbj : b ≤ j)
    (hfirst : v₁ (a : ℤ) = w (b : ℤ))
    (hbase : ∀ i : ℕ, 1 ≤ i → i < a → v (i : ℤ) = w (i : ℤ) ∧ v₁ (i : ℤ) = w (i : ℤ))
    (han : v (a : ℤ) < 0)
    (hvb : v (b : ℤ) = w (b : ℤ))
    (hpos : ∀ i : ℕ, a < i → i ≤ j → i ≠ b → 0 ≤ v (i : ℤ)) :
    negPrefix v j = negPrefix v₁ a + 1 := by
  have hb : 1 ≤ b := by omega
  have ha' : a-1+1 = a := by omega
  have hb' : b-1+1 = b := by omega
  have hsame : negPrefix v (a-1) = negPrefix v₁ (a-1) := by
    apply prefix_neg_agree
    intro i hi hil
    obtain ⟨h₁,h₂⟩ := hbase i hi (by omega)
    rw [h₁,h₂]
  have h_a := prefix_neg_succ v (a-1)
  rw [ha', ite_eq_left han] at h_a
  have h_b := prefix_neg_succ v (b-1)
  rw [hb', hvb] at h_b
  have h_c := prefix_neg_succ v₁ (a-1)
  rw [ha', hfirst] at h_c
  have hmid := prefix_neg_extend (w := v) (show a ≤ b-1 by omega) (by
    intro i hi hil
    exact hpos i hi (by omega) (by omega))
  have htail := prefix_neg_extend (w := v) hbj (by
    intro i hi hij
    exact hpos i (by omega) hij (by omega))
  omega

theorem Active.step_partner {n g q : ℕ} {w : PermZ} (h : Active n w g q)
    (hqA : w (q : ℤ) < (q : ℤ))
    (hE : ∃ i : ℕ, g < i ∧ i ≤ q ∧ (i : ℤ) < w (i : ℤ)) :
    ∃ t, Step n w t := by
  classical
  obtain ⟨a,b,hga,hab,hbq,hcross,hfixed,hanti⟩ := last_transition h hqA hE
  have hq := h.last_le
  have ha : 1 ≤ a := by omega
  have hbn : b ≤ n := by omega
  obtain ⟨t₁, ht₁⟩ := PositiveSwap.exists n a b ha hab hbn
  let v₁ := w*t₁
  have hv₁ : AffB n v₁ := h.mem.mul ht₁.refl.1
  have hva : v₁ (a : ℤ) = w (b : ℤ) := congrArg w ht₁.left
  have hvb : v₁ (b : ℤ) = w (a : ℤ) := congrArg w ht₁.right
  have hvfix (i : ℕ) (hin : i ≤ n) (hia : i ≠ a) (hib : i ≠ b) :
      v₁ (i : ℤ) = w (i : ℤ) := congrArg w (ht₁.fixed i hin hia hib)
  by_cases hopen : OddGood v₁ a
  swap
  · refine ⟨t₁, ht₁.repair h hga hab hbq hcross ?_⟩
    intro j hgj hjq hv
    obtain ⟨haj,hjb⟩ := ht₁.repair_range h hga hab hbq hgj hjq hv
    have hf (i : ℕ) (hi : a < i) (hij : i ≤ j) : v₁ (i : ℤ) = (i : ℤ) := by
      rw [hvfix i (by omega) (by omega) (by omega), hfixed i hi (by omega)]
    have hgood := good_shrink_fixed hv₁.1 hv haj hf
    have hpar := prefix_neg_extend haj (by intro i hi hij; rw [hf i hi hij]; omega)
    rw [hpar]
    by_contra hodd
    exact hopen ⟨hgood, hodd⟩
  have hwb : (w (b : ℤ)).natAbs ≤ a := by
    have hh := (hopen.1 (a : ℤ)).mp (by simp)
    rwa [hva] at hh
  let Partner (i : ℕ) := b < i ∧ i ≤ n ∧ (i : ℤ) ≤ w (a : ℤ) ∧ w (i : ℤ) ≤ (a : ℤ)
  by_cases hex : ∃ i, Partner i
  · let c := Nat.find hex
    have hc : Partner c := Nat.find_spec hex
    obtain ⟨hbc,hcn,hc₁,hc₂⟩ := hc
    have hcq : c ≤ q := by
      by_contra! hh
      have := h.tail_fixed c hh hcn
      omega
    have hac : a < c := by omega
    obtain ⟨t,ht⟩ := PositiveSwap.exists n a c ha hac hcn
    have hneg : w (c : ℤ) < 0 := by
      have hn : a < (v₁ (c : ℤ)).natAbs := by
        by_contra! hc
        have hh := (hopen.1 (c : ℤ)).mpr hc
        change c ≤ a at hh
        omega
      rw [hvfix c hcn (by omega) (by omega)] at hn
      omega
    refine ⟨t, ht.repair h hga hac hcq ⟨hc₁,hc₂⟩ ?_⟩
    intro j hgj hjq hv
    obtain ⟨haj,hjc⟩ := ht.repair_range h hga hac hcq hgj hjq hv
    have hfix (i : ℕ) (hin : i ≤ n) (hia : i ≠ a) (hic : i ≠ c) :
        (w*t) (i : ℤ) = w (i : ℤ) := congrArg w (ht.fixed i hin hia hic)
    have hvb' := hfix b hbn (by omega) (by omega)
    have hbj : b ≤ j := by
      have hh := (hv (b : ℤ)).mpr (by rw [hvb']; omega)
      exact hh
    have hpar := partner_prefix_parity ha hab hbj hva
      (fun i _ hi => ⟨hfix i (by omega) (by omega) (by omega),
        hvfix i (by omega) (by omega) (by omega)⟩)
      (show (w*t) (a : ℤ) < 0 by
        change w (t (a : ℤ)) < 0
        rwa [ht.left]) hvb' (by
          intro i hia hij hib
          rw [hfix i (by omega) (by omega) (by omega)]
          by_cases hlt : i < b
          · rw [hfixed i hia hlt]; omega
          · by_contra! hn
            have hi : Partner i := ⟨by omega,by omega,by omega,by omega⟩
            have hh : c ≤ i := Nat.find_min' hex hi
            omega)
    rw [hpar, Nat.even_iff]
    have hn := hopen.2
    rw [Nat.even_iff] at hn
    omega
  have hout (i : ℕ) (hbi : b < i) (hin : i ≤ n) (hiw : (i : ℤ) ≤ w (a : ℤ)) :
      (a : ℤ) < w (i : ℤ) ∧ w (i : ℤ) ≤ (i : ℤ) := by
    refine ⟨?_, hanti i hbi hin⟩
    by_contra! hh
    exact hex ⟨i,hbi,hin,hiw,hh⟩
  have hwaN : (n : ℤ) < w (a : ℤ) := by
    by_contra! hn
    let c := (w (a : ℤ)).toNat
    have hc : (c : ℤ) = w (a : ℤ) := by have := hcross.1; dsimp [c]; omega
    have hbc : b ≤ c := by have := hcross.1; omega
    have hcn : c ≤ n := by omega
    have hcq : c ≤ q := by
      by_contra! hqc
      have hf := h.tail_fixed c hqc hcn
      have he := w.injective (hc.symm.trans hf.symm)
      change (a : ℤ) = (c : ℤ) at he
      omega
    have hpos (i : ℕ) (hai : a < i) (hic : i ≤ c) :
        0 ≤ v₁ (i : ℤ) ∧ v₁ (i : ℤ) ≤ (c : ℤ) := by
      by_cases hib : i = b
      · subst i; rw [hvb, ← hc]; omega
      · rw [hvfix i (by omega) (by omega) hib]
        by_cases hil : i < b
        · rw [hfixed i hai hil]; omega
        · have := hout i (by omega) (by omega) (by omega)
          omega
    have hg : Good v₁ c := good_extend hv₁.1 hopen.1 (by omega) (by
      intro i hi hil
      have := hpos i hi hil
      omega)
    have hwg : Good w c := (good_mul_iff
      (windowSwap_good_above (neg := false) ht₁.refl.1.1 ha hab hbc hcn
        ht₁.left ht₁.right ht₁.fixed)).mp hg
    have he : c = q := by
      by_contra hne
      exact h.no_mid_good c (by omega) (by omega) hwg
    have hf (i : ℕ) (hi : q < i) (hin : i ≤ n) : v₁ (i : ℤ) = (i : ℤ) := by
      rw [hvfix i hin (by omega) (by omega), h.tail_fixed i hi hin]
    have hp := oddGood_below hv₁ hf hcn (by omega) hg
    have hr := prefix_neg_extend (w := v₁) (show a ≤ c by omega)
      (fun i hi hic => (hpos i hi hic).1)
    exact hopen.2 (hr ▸ hp)
  have hpos' (i : ℕ) (hia : a < i) (hin : i ≤ n) (hib : i ≠ b) :
      0 ≤ w (i : ℤ) ∧ w (i : ℤ) ≤ (n : ℤ) := by
    by_cases hlt : i < b
    · rw [hfixed i hia hlt]; omega
    · have := hout i (by omega) hin (by omega)
      omega
  have hcount := crossing_single_after hv₁.1 hopen.1 hab hbn (by
    intro i hi hin hib
    rw [hvfix i hin (by omega) hib]
    exact hpos' i hi hin hib)
  have hN : period n = 2 * (n : ℤ) + 2 := rfl
  have hwa : period n < w (a : ℤ) := by
    by_contra! hn
    have hlt : w (a : ℤ) < period n := by
      have he := h.mem.1.translate 0 1
      rw [zero_add, one_mul, h.mem.1.zero, zero_add] at he
      by_contra! hge
      have hh : w (a : ℤ) = period n := by omega
      have hz := w.injective (hh.trans he.symm)
      change (a : ℤ) = period n at hz
      omega
    have hzero : floorMass n v₁ b = 0 := by
      unfold floorMass
      rw [hvb, Int.ediv_eq_zero_of_lt (by omega) hlt]
      decide
    have he := hv₁.2
    rw [hcount, hzero, add_zero] at he
    exact hopen.2 he
  obtain ⟨t, ht, hta, hfix⟩ := mirrorSwap_exists n a ha (by omega) false
  have hfix' (i : ℕ) (hin : i ≤ n) (hia : i ≠ a) :
      (w*t) (i : ℤ) = w (i : ℤ) := congrArg w (hfix i hin hia)
  have hvb' := hfix' b hbn (by omega)
  have hvneg : (w*t) (a : ℤ) < 0 := by
    change w (t (a : ℤ)) < 0
    change t (a : ℤ) = period n - (a : ℤ) at hta
    rw [hta, h.mem.1.mirror]
    omega
  have hcost := mirrorSwap_cost (neg := false) ha (by omega : a ≤ n) hta hfix
  change dis n t = 2*(n+1-a) at hcost
  have hmirrorCross : period n - (a : ℤ) ≤ w (a : ℤ) :=
    le_trans (Int.sub_le_self _ (by omega)) hwa.le
  refine ⟨t, repaired_step h.mem ht h.tail_fixed ?_ ?_ h.no_mid_good ?_
    (mirrorSwap_efficient (neg := false) h.mem.1 ha (by omega) hta hfix hmirrorCross) (by omega)⟩
  · intro i _ hi
    exact hfix i (by omega) (by omega)
  · intro i hi hin
    exact hfix i hin (by omega)
  · intro j hgj hjq hv
    have haj : a ≤ j := by
      by_contra! hj
      apply h.no_mid_good j hgj hjq
      exact (prefix_agree (h.mem.1.mul ht.1.1) h.mem.1 (fun i _ hi =>
        hfix' i (by omega) (by omega))).mp hv
    have hbj : b ≤ j := by
      exact (hv (b : ℤ)).mpr (by rw [hvb']; omega)
    have hpar := partner_prefix_parity ha hab hbj hva
      (fun i _ hi => ⟨hfix' i (by omega) (by omega), hvfix i (by omega) (by omega) (by omega)⟩)
      hvneg hvb' (by
        intro i hi hij hib
        rw [hfix' i (by omega) (by omega)]
        exact (hpos' i hi (by omega) hib).1)
    rw [hpar, Nat.even_iff]
    have hn := hopen.2
    rw [Nat.even_iff] at hn
    omega

end AffineB
```

### `AffineBOuter.lean`

```lean
import AffineBActive

namespace AffineB

private theorem first_outer_data {n g q : ℕ} {w : PermZ} (h : Active n w g q)
    (hA : ∀ i : ℕ, g < i → i ≤ q → w (i : ℤ) ≤ (i : ℤ)) :
    w ((g+1 : ℕ) : ℤ) < -((g+1 : ℕ) : ℤ) ∧ Even (negPrefix w g) := by
  let s := g+1
  have hs : s ≤ q := by have := h.lt; omega
  have hsn : s ≤ n := hs.trans h.last_le
  have hanti : w (s : ℤ) < (s : ℤ) :=
    lt_of_le_of_ne (hA s (by omega) hs) h.first_moved
  have hmag : g < (w (s : ℤ)).natAbs := by
    by_contra! hm
    have hh := (h.lower_good (s : ℤ)).mpr hm
    change s ≤ g at hh
    omega
  have hneg : w (s : ℤ) < 0 := by omega
  have hpar : Even (negPrefix w g) := by
    by_contra hn
    have := h.next_positive hn
    change 0 < w (s : ℤ) at this
    omega
  refine ⟨?_,hpar⟩
  have hn : w (s : ℤ) ≠ -(s : ℤ) := by
    intro he
    have hg : Good w s := good_extend h.mem.1 h.lower_good (by omega) (by
      intro i hi hi'
      have he' : i = s := by omega
      subst i
      rw [he]
      simp)
    by_cases hlt : s < q
    · exact h.no_mid_good s (by omega) hlt hg
    · have heven := oddGood_below h.mem h.tail_fixed hsn (by omega) hg
      have hp := prefix_neg_succ w g
      change negPrefix w s = negPrefix w g + (if w (s : ℤ) < 0 then 1 else 0) at hp
      rw [ite_eq_left hneg] at hp
      rw [hp, Nat.even_iff] at heven
      rw [Nat.even_iff] at hpar
      omega
  change w (s : ℤ) < -(s : ℤ)
  omega

theorem Active.step_outer {n g q : ℕ} {w : PermZ} (h : Active n w g q)
    (hA : ∀ i : ℕ, g < i → i ≤ q → w (i : ℤ) ≤ (i : ℤ)) :
    ∃ t, Step n w t := by
  classical
  let s := g+1
  let d := -w (s : ℤ)
  have hd_def : w (s : ℤ) = -d := by dsimp [d]; omega
  have hs_def : (s : ℤ) = (g : ℤ)+1 := by simp [s]
  have hq := h.last_le
  have hgs := h.lt
  have hsn : s ≤ n := by omega
  have hs1 : 1 ≤ s := by omega
  obtain ⟨hneg, hpar⟩ := first_outer_data h hA
  change w (s : ℤ) < -(s : ℤ) at hneg
  have hds : (s : ℤ) < d := by dsimp [d]; omega
  have hAnti (i : ℕ) (hi : g < i) (hin : i ≤ n) : w (i : ℤ) ≤ (i : ℤ) := by
    by_cases hiq : i ≤ q
    · exact hA i hi hiq
    · rw [h.tail_fixed i (by omega) hin]
  have hout (i : ℕ) (hi : g < i) : g < (w (i : ℤ)).natAbs := by
    by_contra! hh
    have he := (h.lower_good (i : ℤ)).mpr hh
    exact hi.not_ge he
  have hfinite_neg (hd : d ≤ (n : ℤ)) :
      ∃ i : ℕ, s < i ∧ (i : ℤ) ≤ d ∧ w (i : ℤ) < 0 := by
    by_contra! hh
    let c := d.toNat
    have hc : (c : ℤ) = d := by dsimp [c]; omega
    have hcn : c ≤ n := by omega
    have hgc : g ≤ c := by omega
    have hg : Good w c := good_extend h.mem.1 h.lower_good hgc (by
      intro i hgi hic
      by_cases he : i = s
      · subst i
        dsimp [d] at hc
        omega
      · have hs_i : s < i := by omega
        have hpos := hh i hs_i (by omega)
        have hle := hAnti i hgi (hic.trans hcn)
        omega)
    by_cases hcq : c < q
    · exact h.no_mid_good c (by omega) hcq hg
    · have hev := oddGood_below h.mem h.tail_fixed hcn (by omega) hg
      have hcpos := prefix_neg_extend (w := w) (show s ≤ c by omega)
        (fun i hi hic => hh i hi (by omega))
      have hp := prefix_neg_succ w g
      change negPrefix w s = negPrefix w g + (if w (s : ℤ) < 0 then 1 else 0) at hp
      rw [ite_eq_left (by omega)] at hp
      rw [hcpos, hp, Nat.even_iff] at hev
      rw [Nat.even_iff] at hpar
      omega
  let Partner (i : ℕ) := s < i ∧ i ≤ n ∧ w (i : ℤ) < 0
  by_cases hex : ∃ i, Partner i
  · let r := Nat.find hex
    obtain ⟨hsr,hrn,hrneg⟩ : Partner r := Nat.find_spec hex
    have hrq : r ≤ q := by
      by_contra! hh
      have := h.tail_fixed r hh hrn
      omega
    have hrd : (r : ℤ) ≤ d := by
      by_cases hd : d ≤ (n : ℤ)
      · obtain ⟨i, hsi, hid, hin⟩ := hfinite_neg hd
        have hr : r ≤ i := Nat.find_min' hex (show Partner i from ⟨hsi,by omega,hin⟩)
        omega
      · omega
    have hrb : w (r : ℤ) ≤ -(s : ℤ) := by
      have := hout r (by omega)
      omega
    obtain ⟨t,ht,hta,htb,hfix⟩ := windowSwap_exists n s r hs1 hsr hrn true
    have hcost := windowSwap_cost (neg := true) hs1 hsr hrn hta htb hfix
    change dis n t = 2*(s+r) at hcost
    refine ⟨t, repaired_step h.mem ht h.tail_fixed ?_ ?_ h.no_mid_good ?_
      (windowSwap_efficient (neg := true) h.mem.1 hs1 hsr hrn hta htb hfix ⟨hrd,hrb⟩)
      (by omega)⟩
    · intro i _ hi
      exact hfix i (by omega) (by omega) (by omega)
    · intro i hi hin
      exact hfix i hin (by omega) (by omega)
    · intro j hgj hjq hv
      have hjr : j < r := by
        by_contra! hle
        have hg := windowSwap_good_above (neg := true) ht.1.1 hs1 hsr hle
          (by omega) hta htb hfix
        exact h.no_mid_good j hgj hjq ((good_mul_iff hg).mp hv)
      have hp (i : ℕ) (hgi : g < i) (hij : i ≤ j) : 0 ≤ (w*t) (i : ℤ) := by
        change 0 ≤ w (t (i : ℤ))
        by_cases his : i = s
        · subst i
          change t (s : ℤ) = -(r : ℤ) at hta
          rw [hta, h.mem.1.1]
          omega
        · rw [hfix i (by omega) his (by omega)]
          by_contra! hi
          have hri : r ≤ i := Nat.find_min' hex (show Partner i from ⟨by omega,by omega,hi⟩)
          omega
      rw [prefix_neg_extend (w := w*t) (by omega : g ≤ j) hp,
        prefix_neg_agree (w := w) (by
          intro i _ hi
          change w (t (i : ℤ)) < 0 ↔ w (i : ℤ) < 0
          rw [hfix i (by omega) (by omega) (by omega)])]
      exact hpar
  have hpos (i : ℕ) (hsi : s < i) (hin : i ≤ n) : 0 ≤ w (i : ℤ) := by
    by_contra! hh
    exact hex ⟨i,hsi,hin,hh⟩
  have hd : (n : ℤ) < d := by
    by_contra! hn
    obtain ⟨i,hi,hid,hneg⟩ := hfinite_neg hn
    exact hex ⟨i,hi,by omega,hneg⟩
  have hN : period n = 2 * (n : ℤ) + 2 := rfl
  have hbig : period n < d := by
    by_contra! hh
    have hχ := crossing_single_after h.mem.1 h.lower_good (show g < s by omega) hsn (by
      intro i hi hin hne
      exact ⟨hpos i (by omega) hin, (hAnti i hi hin).trans (by omega)⟩)
    have hfloor : floorMass n w s = 1 := by
      unfold floorMass
      rw [hd_def]
      have hbase : (period n - d) / period n = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
      rw [show -d = (period n - d) + (-1) * period n by omega,
        Int.add_mul_ediv_right _ _ (period_pos n).ne', hbase]
      decide
    have he := h.mem.2
    rw [hχ,hfloor,Nat.even_iff] at he
    rw [Nat.even_iff] at hpar
    omega
  have hm : period n + (s : ℤ) ≤ d := by
    by_contra! hd'
    have he := h.mem.1.translate (s : ℤ) 1
    rw [one_mul] at he
    have hin : (w ((s : ℤ) + period n)).natAbs ≤ g := by
      rw [he]
      rw [hd_def]
      omega
    have he' := (h.lower_good ((s : ℤ) + period n)).mpr hin
    omega
  obtain ⟨t, ht, hta, hfix⟩ := mirrorSwap_exists n s hs1 hsn true
  have hc := mirrorSwap_cost (neg := true) hs1 hsn hta hfix
  change dis n t = 2 * (n+1+s) at hc
  have hcross : w (s : ℤ) ≤ -period n - (s : ℤ) := by dsimp [d] at hm; omega
  refine ⟨t, repaired_step h.mem ht h.tail_fixed ?_ ?_ h.no_mid_good ?_
    (mirrorSwap_efficient (neg := true) h.mem.1 hs1 hsn hta hfix hcross) (by omega)⟩
  · intro i _ hi
    exact hfix i (by omega) (by omega)
  · intro i hi hin
    exact hfix i hin (by omega)
  · intro j hgj hjq _hv
    have hp (i : ℕ) (hgi : g < i) (hij : i ≤ j) : 0 ≤ (w*t) (i : ℤ) := by
      change 0 ≤ w (t (i : ℤ))
      by_cases his : i = s
      · subst i
        change t (s : ℤ) = -period n - (s : ℤ) at hta
        rw [hta, show -period n - (s : ℤ) = -(s : ℤ) - period n by omega,
          h.mem.1.sub_period, h.mem.1.1]
        dsimp [d] at hbig
        omega
      · rw [hfix i (by omega) his]
        exact hpos i (by omega) (by omega)
    rw [prefix_neg_extend (w := w*t) (by omega : g ≤ j) hp,
      prefix_neg_agree (w := w) (by
        intro i _ hi
        change w (t (i : ℤ)) < 0 ↔ w (i : ℤ) < 0
        rw [hfix i (by omega) (by omega)])]
    exact hpar

end AffineB
```

### `AffineBCost.lean`

```lean
import AffineBPartners
import AffineBOuter

namespace AffineB

theorem step_exists {n : ℕ} {w : PermZ} (hw : AffB n w) (hne : w ≠ 1) :
    ∃ t, Step n w t := by
  classical
  by_cases hR : ∃ j : ℕ, 1 ≤ j ∧ j < n ∧ OddGood w j ∧
      (∀ k : ℕ, j < k → k < n → ¬ OddGood w k) ∧ w ((j+1 : ℕ) : ℤ) < 0
  · obtain ⟨j,hj,hjn,hodd,hlast,hneg⟩ := hR
    exact step_r1 hw hj hjn hodd hlast hneg
  obtain ⟨q,hq,hqn,hm,hfix⟩ := last_moved_exists hw.1 hne
  obtain ⟨g,h⟩ := active_of_no_r1 hw hq hqn hm hfix hR
  by_cases hex : (q : ℤ) < w (q : ℤ)
  · exact h.step_rightmost hex
  have hqA : w (q : ℤ) < (q : ℤ) := by omega
  by_cases hE : ∃ i : ℕ, g < i ∧ i ≤ q ∧ (i : ℤ) < w (i : ℤ)
  · exact h.step_partner hqA hE
  · push Not at hE
    exact h.step_outer hE

private theorem attain_aux (n k : ℕ) (w : PermZ) (hw : AffB n w)
    (hk : potential n w = k) : potential n w ∈ Costs2 n w := by
  induction k using Nat.strong_induction_on generalizing w with
  | h k ih =>
    by_cases he : w = 1
    · subst w
      refine ⟨[], ?_, rfl, ?_⟩
      · simp
      · simp [potential_one]
    obtain ⟨t, ht, hpos, hcost⟩ := step_exists hw he
    have hk' : potential n (w*t) < k := by omega
    obtain ⟨ts, hts, hprod, hsum⟩ := ih (potential n (w*t)) hk' (w*t) (hw.mul ht.1) rfl
    have htt : t * t = (1 : PermZ) := by
      ext x
      exact ht.involutive x
    refine ⟨ts ++ [t], ?_, ?_, ?_⟩
    · intro r hr
      rw [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hts r hr
      · exact ht
    · rw [List.prod_append, List.prod_cons, List.prod_nil, mul_one, hprod, mul_assoc, htt, mul_one]
    · rw [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, hsum, hcost]

theorem lewis_tenner_4_2_attained (n : ℕ) (w : PermZ) (hw : AffB n w) :
    dis n w + 2 * (blC n w - blB n w) ∈ Costs2 n w := by
  rw [← potential_eq]
  exact attain_aux n _ w hw rfl

theorem lewis_tenner_4_2 (n : ℕ) (_hn : 0 < n) (w : PermZ) (hw : AffB n w) :
    IsLeast (Costs2 n w) (dis n w + 2 * (blC n w - blB n w)) :=
  ⟨lewis_tenner_4_2_attained n w hw, fun _ hc => lewis_tenner_4_2_lower n w hc⟩

#print axioms lewis_tenner_4_2_attained
#print axioms lewis_tenner_4_2

end AffineB
```

### `AffineBExamples.lean`

```lean
import AffineBBasics
import AffineBCost

namespace AffineB

private def extend (n : ℕ) (f : ℤ → ℤ) (x : ℤ) : ℤ :=
  f (x % period n) + (x / period n) * period n

private theorem extend_translate (n : ℕ) (f : ℤ → ℤ) (x k : ℤ) :
    extend n f (x + k * period n) = extend n f x + k * period n := by
  unfold extend
  rw [Int.add_mul_emod_self_right, Int.add_mul_ediv_right _ _ (period_pos n).ne',
    add_mul, add_assoc]

private theorem residue_decomp (n : ℕ) (x : ℤ) :
    x = x % period n + (x / period n) * period n := by
  simpa only [mul_comm] using (Int.emod_add_mul_ediv x (period n)).symm

private theorem residue_mem (n : ℕ) (x : ℤ) :
    x % period n ∈ Finset.Ico (0 : ℤ) (period n) :=
  Finset.mem_Ico.mpr
    ⟨Int.emod_nonneg _ (period_pos n).ne', Int.emod_lt_of_pos _ (period_pos n)⟩

private theorem extend_inverse (n : ℕ) (f g : ℤ → ℤ)
    (h : ∀ r ∈ Finset.Ico (0 : ℤ) (period n), extend n g (extend n f r) = r) :
    Function.LeftInverse (extend n g) (extend n f) := by
  intro x
  conv_lhs => rw [residue_decomp n x]
  rw [extend_translate, extend_translate, h _ (residue_mem n x), ← residue_decomp]

private def fromTables (n : ℕ) (f g : ℤ → ℤ)
    (hl : ∀ r ∈ Finset.Ico (0 : ℤ) (period n), extend n g (extend n f r) = r)
    (hr : ∀ r ∈ Finset.Ico (0 : ℤ) (period n), extend n f (extend n g r) = r) : PermZ :=
  ⟨extend n f, extend n g, extend_inverse n f g hl, extend_inverse n g f hr⟩

private theorem fromTables_signed {n : ℕ} {f g : ℤ → ℤ} {hl hr}
    (h : ∀ r ∈ Finset.Ico (0 : ℤ) (period n), extend n f (-r) = -extend n f r) :
    AffSigned n (fromTables n f g hl hr) := by
  constructor
  · intro x
    change extend n f (-x) = -extend n f x
    conv_lhs => rw [residue_decomp n x]
    rw [neg_add, ← neg_mul, extend_translate, h _ (residue_mem n x)]
    conv_rhs => rw [residue_decomp n x]
    rw [extend_translate]
    rw [neg_mul, neg_add]
  · intro x
    change extend n f (x + period n) = extend n f x + period n
    simpa only [one_mul] using extend_translate n f x 1

private theorem fromTables_bound {n : ℕ} {f g : ℤ → ℤ} {hl hr} {D : ℕ}
    (h : ∀ r ∈ Finset.Ico (0 : ℤ) (period n), (extend n f r - r).natAbs ≤ D) :
    ∀ x : ℤ, ((fromTables n f g hl hr) x - x).natAbs ≤ D := by
  intro x
  change (extend n f x - x).natAbs ≤ D
  have hx : extend n f x = extend n f (x % period n) + (x / period n) * period n := by
    rw [← extend_translate, ← residue_decomp]
  rw [hx, show extend n f (x % period n) + x / period n * period n - x =
    extend n f (x % period n) - x % period n by have := residue_decomp n x; omega]
  exact h _ (residue_mem n x)

theorem negCrossing_eq_filter {w : PermZ} {D : ℕ}
    (h : ∀ x : ℤ, (w x - x).natAbs ≤ D) :
    (negCrossing w).ncard = ((Finset.Icc (1 : ℤ) (D : ℤ)).filter (fun x => w x < 0)).card := by
  have he : negCrossing w =
      ↑((Finset.Icc (1 : ℤ) (D : ℤ)).filter (fun x => w x < 0)) := by
    ext x
    change (0 < x ∧ w x < 0) ↔ _
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    have hx := h x
    omega
  rw [he, Set.ncard_coe_finset]

private def goodTest (w : PermZ) (j : ℕ) : Bool :=
  (List.range j).all (fun i => decide ((w ((i + 1 : ℕ) : ℤ)).natAbs ≤ j))

private theorem goodTest_iff {n : ℕ} {w : PermZ} (hw : AffSigned n w) (j : ℕ) :
    goodTest w j = true ↔ Good w j := by
  rw [hw.good_iff_window]
  simp only [goodTest, List.all_eq_true, List.mem_range, decide_eq_true_eq, Finset.mem_Icc]
  constructor
  · intro h i hi
    have he : i - 1 + 1 = i := by omega
    simpa only [he] using h (i - 1) (by omega)
  · intro h i hi
    exact h (i + 1) (by omega)

private def veryGoodTest (w : PermZ) (j : ℕ) : Bool :=
  goodTest w j && (negPrefix w j % 2 == 0)

private theorem veryGoodTest_iff {n : ℕ} {w : PermZ} (hw : AffSigned n w) (j : ℕ) :
    veryGoodTest w j = true ↔ VeryGood w j := by
  simp only [veryGoodTest, Bool.and_eq_true, goodTest_iff hw, beq_iff_eq, VeryGood]
  exact and_congr_right fun _ => Nat.even_iff.symm

private theorem goodCuts_test {n : ℕ} {w : PermZ} (hw : AffSigned n w) (m : ℕ) :
    ((Finset.Ico 1 m).filter (goodTest w · = true)) =
      (by classical exact (Finset.Ico 1 m).filter (Good w)) := by
  classical
  ext j
  rw [Finset.mem_filter, Finset.mem_filter, goodTest_iff hw]

private theorem veryGoodCuts_test {n : ℕ} {w : PermZ} (hw : AffSigned n w) (m : ℕ) :
    ((Finset.Ico 1 m).filter (veryGoodTest w · = true)) =
      (by classical exact (Finset.Ico 1 m).filter (VeryGood w)) := by
  classical
  ext j
  rw [Finset.mem_filter, Finset.mem_filter, veryGoodTest_iff hw]

private def example41Forward (r : ℤ) : ℤ :=
  ([0, 1, -2, 4, 3, 6, -5, 7, -8, 34, 9, 11,
    12, 13, 15, -10, 32, 17, 29, 18, 21, 20, 26, 23] : List ℤ)[r.toNat]!

private def example41Inverse (r : ℤ) : ℤ :=
  ([0, 1, -2, 4, 3, -6, 5, 7, -8, 10, -15, 11,
    12, 13, 39, 14, 32, 17, 19, 30, 21, 20, 26, 23] : List ℤ)[r.toNat]!

def example41 : PermZ := fromTables 11 example41Forward example41Inverse
  (by decide) (by decide)

theorem example41_signed : AffSigned 11 example41 :=
  fromTables_signed (by decide)

theorem example41_window :
    (List.range 11).map (fun i => example41 ((i : ℤ) + 1)) =
      [1,-2,4,3,6,-5,7,-8,34,9,11] := by decide

theorem example41_crossings : (negCrossing example41).ncard = 4 := by
  rw [negCrossing_eq_filter (D := 25)
    (show ∀ x, (example41 x - x).natAbs ≤ 25 from fromTables_bound (by decide))]
  decide

theorem example41_mem : AffB 11 example41 := by
  refine ⟨example41_signed, ?_⟩
  rw [example41_crossings]
  exact ⟨2, rfl⟩

theorem example41_cuts :
    (by classical exact (Finset.Ico 1 11).filter (Good example41)) = {1,2,4,6,7,8} ∧
    (by classical exact (Finset.Ico 1 11).filter (VeryGood example41)) = {1,6,7} := by
  classical
  rw [← goodCuts_test example41_signed, ← veryGoodCuts_test example41_signed]
  constructor <;> decide

theorem example41_counts : blC 11 example41 = 7 ∧ blB 11 example41 = 4 := by
  unfold blC blB
  rw [example41_cuts.1, example41_cuts.2]
  constructor <;> decide


private theorem testBRefl {n : ℕ} {t : PermZ} (ht : AffB n t) {x y : ℤ}
    (hne : x ≠ y) (hx : t x = y) (hy : t y = x)
    (hfix : ∀ r ∈ Finset.Ico (0 : ℤ) (period n),
      r ≠ x % period n → r ≠ y % period n →
      r ≠ (-x) % period n → r ≠ (-y) % period n → t r = r) : BRefl n t := by
  refine ⟨ht, x, y, hne, ?_, ?_⟩
  · intro a b h
    obtain ⟨k, h | h | h | h⟩ := h
    all_goals obtain ⟨rfl, rfl⟩ := h
    all_goals simp only [ht.1.translate, ht.1.1, hx, hy]
  · intro a ha
    have hz (b : ℤ) (hb : a % period n = b % period n) :
        a = b + (a / period n - b / period n) * period n := by
      have ha' := residue_decomp n a
      have hb' := residue_decomp n b
      rw [sub_mul]
      omega
    have hfix' : t (a % period n) = a % period n := by
      refine hfix _ (residue_mem n a) ?_ ?_ ?_ ?_
      · intro h
        exact ha ⟨y + (a / period n - x / period n) * period n,
          _, Or.inl ⟨hz x h, rfl⟩⟩
      · intro h
        exact ha ⟨x + (a / period n - y / period n) * period n,
          _, Or.inr (Or.inl ⟨hz y h, rfl⟩)⟩
      · intro h
        exact ha ⟨-y + (a / period n - (-x) / period n) * period n,
          _, Or.inr (Or.inr (Or.inl ⟨hz (-x) h, rfl⟩))⟩
      · intro h
        exact ha ⟨-x + (a / period n - (-y) / period n) * period n,
          _, Or.inr (Or.inr (Or.inr ⟨hz (-y) h, rfl⟩))⟩
    conv_lhs => rw [residue_decomp n a]
    rw [ht.1.translate, hfix', ← residue_decomp]

private theorem based_eq {n : ℕ} {w t : PermZ}
    (hw : AffSigned n w) (ht : AffSigned n t)
    (h : ∀ r ∈ Finset.Ico (0 : ℤ) (period n), w r = t r) : w = t := by
  ext a
  change w a = t a
  rw [residue_decomp n a, hw.translate, ht.translate, h _ (residue_mem n a)]

private def table (xs : List ℤ) (r : ℤ) : ℤ := xs[r.toNat]!

private def bothFlips : PermZ :=
  fromTables 2 (table [0,-1,-2,3,8,7]) (table [0,-1,-2,3,8,7]) (by decide) (by decide)

private def flip1 : PermZ :=
  fromTables 2 (table [0,-1,2,3,4,7]) (table [0,-1,2,3,4,7]) (by decide) (by decide)

private def flip2 : PermZ :=
  fromTables 2 (table [0,1,-2,3,8,5]) (table [0,1,-2,3,8,5]) (by decide) (by decide)

private def swap12 : PermZ :=
  fromTables 2 (table [0,2,1,3,5,4]) (table [0,2,1,3,5,4]) (by decide) (by decide)

private def swapNeg12 : PermZ :=
  fromTables 2 (table [0,-2,-1,3,7,8]) (table [0,-2,-1,3,7,8]) (by decide) (by decide)

private theorem swap12_refl : BRefl 2 swap12 := by
  have h : AffB 2 swap12 := by
    refine ⟨fromTables_signed (by decide), ?_⟩
    rw [negCrossing_eq_filter (D := 1)
      (show ∀ x, (swap12 x - x).natAbs ≤ 1 from fromTables_bound (by decide))]
    exact ⟨0, rfl⟩
  exact testBRefl h (x := 1) (y := 2) (by decide) (by decide) (by decide) (by decide)

private theorem swapNeg12_refl : BRefl 2 swapNeg12 := by
  have h : AffB 2 swapNeg12 := by
    refine ⟨fromTables_signed (by decide), ?_⟩
    rw [negCrossing_eq_filter (D := 3)
      (show ∀ x, (swapNeg12 x - x).natAbs ≤ 3 from fromTables_bound (by decide))]
    exact ⟨1, rfl⟩
  exact testBRefl h (x := -1) (y := 2) (by decide) (by decide) (by decide) (by decide)

theorem rankTwo_individualFlips_excluded : ¬ BRefl 2 flip1 ∧ ¬ BRefl 2 flip2 := by
  have h1 : (negCrossing flip1).ncard = 1 := by
    rw [negCrossing_eq_filter (D := 2)
      (show ∀ x, (flip1 x - x).natAbs ≤ 2 from fromTables_bound (by decide))]
    decide
  have h2 : (negCrossing flip2).ncard = 1 := by
    rw [negCrossing_eq_filter (D := 4)
      (show ∀ x, (flip2 x - x).natAbs ≤ 4 from fromTables_bound (by decide))]
    decide
  constructor <;> intro h
  · exact (by decide : ¬ Even 1) (h1 ▸ h.1.2)
  · exact (by decide : ¬ Even 1) (h2 ▸ h.1.2)

theorem rankTwo_bothFlips :
    bothFlips 1 = -1 ∧ bothFlips 2 = -2 ∧ AffB 2 bothFlips ∧
    dis 2 bothFlips = 6 ∧ blC 2 bothFlips = 2 ∧ blB 2 bothFlips = 1 ∧
    8 ∈ Costs2 2 bothFlips := by
  have hs : AffSigned 2 bothFlips := fromTables_signed (by decide)
  have hc : AffB 2 bothFlips := by
    refine ⟨hs, ?_⟩
    rw [negCrossing_eq_filter (D := 4)
      (show ∀ x, (bothFlips x - x).natAbs ≤ 4 from fromTables_bound (by decide))]
    exact ⟨1, rfl⟩
  refine ⟨by decide, by decide, hc, by decide, ?_, ?_, ?_⟩
  · unfold blC
    rw [← goodCuts_test hs]
    decide
  · unfold blB
    rw [← veryGoodCuts_test hs]
    decide
  · refine ⟨[swap12, swapNeg12], ?_, ?_, by decide⟩
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      exacts [swap12_refl, swapNeg12_refl]
    · simp only [List.prod_cons, List.prod_nil, mul_one]
      exact based_eq (swap12_refl.1.1.mul swapNeg12_refl.1.1) hs (by decide)

private def rankOneMirror : PermZ :=
  fromTables 1 (table [0,3,2,1]) (table [0,3,2,1]) (by decide) (by decide)

theorem rankOne_mirror :
    BRefl 1 rankOneMirror ∧ rankOneMirror 1 = 3 ∧ rankOneMirror (-1) = -3 ∧
    dis 1 rankOneMirror = 2 ∧ 2 ∈ Costs2 1 rankOneMirror := by
  have hb : AffB 1 rankOneMirror := by
    refine ⟨fromTables_signed (by decide), ?_⟩
    rw [negCrossing_eq_filter (D := 2)
      (show ∀ x, (rankOneMirror x - x).natAbs ≤ 2 from fromTables_bound (by decide))]
    exact ⟨0, rfl⟩
  have hr := testBRefl hb (x := 1) (y := 3) (by decide) (by decide) (by decide) (by decide)
  refine ⟨hr, by decide, by decide, by decide, [rankOneMirror], ?_, by simp, by decide⟩
  intro t ht
  simp only [List.mem_singleton] at ht
  exact ht.symm ▸ hr


theorem rankTwo_minimum : IsLeast (Costs2 2 bothFlips) 8 := by
  have ⟨_,_,hb,hd,hc,he,_⟩ := rankTwo_bothFlips
  have h := lewis_tenner_4_2 2 (by decide) bothFlips hb
  rw [hd,hc,he] at h
  exact h

theorem rankOne_minimum : IsLeast (Costs2 1 rankOneMirror) 2 := by
  have ⟨hr,_,_,hd,_⟩ := rankOne_mirror
  have h := lewis_tenner_4_2 1 (by decide) rankOneMirror hr.1
  unfold blC blB at h
  rw [hd, Finset.Ico_eq_empty_of_le (show (1 : ℕ) ≤ 1 from le_rfl)] at h
  simpa using h

end AffineB
```

