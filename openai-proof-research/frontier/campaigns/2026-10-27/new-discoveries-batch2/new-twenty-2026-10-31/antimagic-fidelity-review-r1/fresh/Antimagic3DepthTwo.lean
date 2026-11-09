import Antimagic2Finite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
namespace Antimagic.Round3

/-- The untranslated two middle blocks in published Lemma 2.2, in the
exact tuple order used by the inherited depth-two formula. -/
def middleEntry (k a j : ℕ) : ℕ :=
  if a ≤ k then
    if j = 0 then 2 * a + 1 else 3 * k + 2 - a
  else
    if j = 0 then 2 * (a - k) else 4 * k + 3 - (a - k)

theorem middleEntry_range (k a j : ℕ) (ha : a < 2 * k + 1) (_hj : j < 2) :
    1 ≤ middleEntry k a j ∧ middleEntry k a j ≤ 4 * k + 2 := by
  unfold middleEntry
  split_ifs <;> omega

theorem middleEntry_injective (k : ℕ) :
    Function.Injective (fun p : Fin (2 * k + 1) × Fin 2 =>
      middleEntry k p.1.val p.2.val) := by
  rintro ⟨a, j⟩ ⟨b, l⟩ he
  have ha := a.isLt
  have hb := b.isLt
  have hj := j.isLt
  have hl := l.isLt
  have hj' : j.val = 0 ∨ j.val = 1 := by omega
  have hl' : l.val = 0 ∨ l.val = 1 := by omega
  have hab : a.val = b.val ∧ j.val = l.val := by
    unfold middleEntry at he
    rcases hj' with hj' | hj' <;> rcases hl' with hl' | hl' <;>
      simp only [hj', hl', reduceIte, Nat.one_ne_zero] at he <;>
      split_ifs at he <;> omega
  exact Prod.ext (Fin.ext hab.1) (Fin.ext hab.2)

def middleMap (k : ℕ) (p : Fin (2 * k + 1) × Fin 2) : Fin (4 * k + 2) :=
  ⟨middleEntry k p.1.val p.2.val - 1,
    by have := middleEntry_range k p.1.val p.2.val p.1.isLt p.2.isLt; omega⟩

theorem middleMap_bijective (k : ℕ) : Function.Bijective (middleMap k) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro p q h
    apply middleEntry_injective k
    change middleEntry k p.1.val p.2.val = middleEntry k q.1.val q.2.val
    have he := congrArg Fin.val h
    have hp := middleEntry_range k p.1.val p.2.val p.1.isLt p.2.isLt
    have hq := middleEntry_range k q.1.val q.2.val q.1.isLt q.2.isLt
    change middleEntry k p.1.val p.2.val - 1 = middleEntry k q.1.val q.2.val - 1 at he
    omega
  · simp only [Fintype.card_prod, Fintype.card_fin]
    omega

/-- No bounded enumeration: every integer in the middle run occurs uniquely. -/
theorem middleEntry_unique (k x : ℕ) (hx : 1 ≤ x ∧ x ≤ 4 * k + 2) :
    ∃! p : Fin (2 * k + 1) × Fin 2, middleEntry k p.1.val p.2.val = x := by
  obtain ⟨p, hp⟩ := (middleMap_bijective k).2 ⟨x - 1, by omega⟩
  have he := congrArg Fin.val hp
  have hr := middleEntry_range k p.1.val p.2.val p.1.isLt p.2.isLt
  have hp' : middleEntry k p.1.val p.2.val = x := by
    change middleEntry k p.1.val p.2.val - 1 = x - 1 at he
    omega
  refine ⟨p, hp', ?_⟩
  intro q hq
  exact middleEntry_injective k (hq.trans hp'.symm)

/-- Consecutive pair sums, in the inherited tuple order. -/
theorem middleEntry_sum (k a : ℕ) (ha : a < 2 * k + 1) :
    middleEntry k a 0 + middleEntry k a 1 = 3 * k + 3 + a := by
  simp only [middleEntry, ite_true, Nat.one_ne_zero, ite_false]
  split_ifs <;> omega

/-- Translation by beta preserves the exact consecutive pair sums. -/
theorem middleEntry_translated_sum (beta k a : ℕ) (ha : a < 2 * k + 1) :
    (beta + middleEntry k a 0) + (beta + middleEntry k a 1) =
      2 * beta + 3 * k + 3 + a := by
  have := middleEntry_sum k a ha
  omega

/-- The first two groups of labels: root edges and the special child's
leaf edges. They partition the entire low interval. -/
def lowEntry (s : ℕ) : Fin (2 * s) ⊕ Fin (2 * s) → ℕ
  | .inl i => if i.val = 0 then 2 else 3 * s + 2 - i.val
  | .inr j => if j.val = 0 then 1 else if j.val ≤ s then j.val + 2
      else 2 * s + 1 + j.val

theorem lowEntry_range (s : ℕ) (_hs : 2 ≤ s) (p : Fin (2 * s) ⊕ Fin (2 * s)) :
    1 ≤ lowEntry s p ∧ lowEntry s p ≤ 4 * s := by
  cases p with
  | inl i => have := i.isLt; simp only [lowEntry]; split_ifs <;> omega
  | inr j => have := j.isLt; simp only [lowEntry]; split_ifs <;> omega

theorem lowEntry_injective (s : ℕ) (_hs : 2 ≤ s) : Function.Injective (lowEntry s) := by
  intro p q he
  cases p with
  | inl i =>
    have hi := i.isLt
    cases q with
    | inl j =>
      have hj := j.isLt
      have hv : i.val = j.val := by
        simp only [lowEntry] at he
        split_ifs at he <;> omega
      exact congrArg Sum.inl (Fin.ext hv)
    | inr j =>
      have hj := j.isLt
      simp only [lowEntry] at he
      split_ifs at he <;> omega
  | inr i =>
    have hi := i.isLt
    cases q with
    | inl j =>
      have hj := j.isLt
      simp only [lowEntry] at he
      split_ifs at he <;> omega
    | inr j =>
      have hj := j.isLt
      have hv : i.val = j.val := by
        simp only [lowEntry] at he
        split_ifs at he <;> omega
      exact congrArg Sum.inr (Fin.ext hv)

def lowMap (s : ℕ) (hs : 2 ≤ s) (p : Fin (2 * s) ⊕ Fin (2 * s)) : Fin (4 * s) :=
  ⟨lowEntry s p - 1, by have := lowEntry_range s hs p; omega⟩

theorem lowMap_bijective (s : ℕ) (hs : 2 ≤ s) : Function.Bijective (lowMap s hs) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro p q h
    apply lowEntry_injective s hs
    have hp := lowEntry_range s hs p
    have hq := lowEntry_range s hs q
    have he := congrArg Fin.val h
    change lowEntry s p - 1 = lowEntry s q - 1 at he
    omega
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega

/-- Direct agreement with the frozen formula on root edges. -/
theorem lowEntry_root (s : ℕ) (i : Fin (2 * s)) :
    depthTwoLabel (2 * s) 1 i.val = lowEntry s (.inl i) := by
  simp [depthTwoLabel, lowEntry]

/-- Direct agreement with the frozen formula at the special child's leaves. -/
theorem lowEntry_special (s : ℕ) (hs : 2 ≤ s) (j : Fin (2 * s)) :
    depthTwoLabel (2 * s) 2 j.val = lowEntry s (.inr j) := by
  have ht : 0 < 2 * s := by omega
  simp [depthTwoLabel, lowEntry, Nat.div_eq_of_lt j.isLt, Nat.mod_eq_of_lt j.isLt]

/-- The two middle slots of every ordinary depth-two tuple agree exactly
with the symbolic partition above; no relabelling or shadow formula. -/
theorem depthTwo_middle (s a j : ℕ) (hs : 2 ≤ s) (ha : a < 2 * s - 1)
    (hj : j < 2) :
    depthTwoLabel (2 * s) 2 ((2 * s) * (a + 1) + (2 * s - 2 + j)) =
      4 * s + (s - 1) * (2 * s - 1) + middleEntry (s - 1) a j := by
  have ht : 0 < 2 * s := by omega
  have hslot : 2 * s - 2 + j < 2 * s := by omega
  have hdiv : ((2 * s) * (a + 1) + (2 * s - 2 + j)) / (2 * s) = a + 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ ht, Nat.div_eq_of_lt hslot, Nat.zero_add]
  have hmod : ((2 * s) * (a + 1) + (2 * s - 2 + j)) % (2 * s) = 2 * s - 2 + j := by
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt hslot]
  simp only [depthTwoLabel, show ¬ (2 = 1) by decide, ite_false,
    Nat.mul_div_cancel_left s (by decide : 0 < 2), hdiv, hmod,
    show ¬ (a + 1 = 0) by omega, Nat.add_sub_cancel, show ¬ (2 * s - 2 + j < 2 * s - 2) by omega]
  unfold middleEntry
  split_ifs <;> omega

/-- The inherited middle-slot sum is affine in the parent index. -/
theorem depthTwo_middle_sum (s a : ℕ) (hs : 2 ≤ s) (ha : a < 2 * s - 1) :
    depthTwoLabel (2 * s) 2 ((2 * s) * (a + 1) + (2 * s - 2)) +
    depthTwoLabel (2 * s) 2 ((2 * s) * (a + 1) + (2 * s - 1)) =
      2 * (4 * s + (s - 1) * (2 * s - 1)) + 3 * (s - 1) + 3 + a := by
  have h0 := depthTwo_middle s a 0 hs ha (by decide)
  have h1 := depthTwo_middle s a 1 hs ha (by decide)
  have he : 2 * s - 2 + 1 = 2 * s - 1 := by omega
  simp only [Nat.add_zero, he] at h0 h1
  rw [h0, h1]
  exact middleEntry_translated_sum _ _ _ (by omega)

open Finset in
/-- A summation identity with natural-number subtraction justified termwise. -/
theorem sum_desc_add (C m : ℕ) (hm : m ≤ C + 1) :
    (∑ i ∈ range m, (C - i)) + (∑ i ∈ range m, i) = m * C := by
  rw [← sum_add_distrib]
  calc
    _ = ∑ _i ∈ range m, C := by
      apply sum_congr rfl
      intro i hi
      have := mem_range.mp hi
      exact Nat.sub_add_cancel (by omega)
    _ = m * C := by simp

open Finset in
/-- Closed form for the actual depth-two root row. -/
theorem depthTwo_root_sum (s : ℕ) (hs : 2 ≤ s) :
    ∑ i ∈ range (2 * s), depthTwoLabel (2 * s) 1 i = (2 * s) ^ 2 + 2 * s := by
  have ht : 2 * s = (2 * s - 1) + 1 := by omega
  nth_rw 1 [ht]
  rw [sum_range_succ']
  have he : (∑ i ∈ range (2 * s - 1), depthTwoLabel (2 * s) 1 (i + 1)) =
      ∑ i ∈ range (2 * s - 1), (3 * s + 1 - i) := by
    apply sum_congr rfl
    intro i hi
    simp only [depthTwoLabel, ite_true, Nat.mul_div_cancel_left s (by decide : 0 < 2),
      show ¬ (i + 1 = 0) by omega, ite_false]
    omega
  rw [he]
  have hdesc := sum_desc_add (3 * s + 1) (2 * s - 1) (by omega)
  have htri := Finset.sum_range_id_mul_two (2 * s - 1)
  have hsub : 2 * s - 1 + 1 = 2 * s := by omega
  have hsub' : 2 * s - 1 - 1 + 2 = 2 * s := by omega
  simp only [depthTwoLabel, ite_true] 
  nlinarith

/-- Every reversed outer block pair has the same sum. -/
theorem depthTwo_outer_pair (s a b : ℕ) (hs : 2 ≤ s) (ha : a < 2 * s - 1)
    (hb : b < s - 1) :
    depthTwoLabel (2 * s) 2 ((2 * s) * (a + 1) + 2 * b) +
    depthTwoLabel (2 * s) 2 ((2 * s) * (a + 1) + (2 * b + 1)) =
      8 * s + (2 * s) * (2 * s - 1) + 1 := by
  have ht : 0 < 2 * s := by omega
  have h0 : 2 * b < 2 * s := by omega
  have h1 : 2 * b + 1 < 2 * s := by omega
  have divs (j : ℕ) (hj : j < 2 * s) :
      ((2 * s) * (a + 1) + j) / (2 * s) = a + 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ ht, Nat.div_eq_of_lt hj, Nat.zero_add]
  have mods (j : ℕ) (hj : j < 2 * s) :
      ((2 * s) * (a + 1) + j) % (2 * s) = j := by
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt hj]
  simp only [depthTwoLabel, show ¬ (2 = 1) by decide, ite_false,
    Nat.mul_div_cancel_left s (by decide : 0 < 2), divs _ h0, divs _ h1,
    mods _ h0, mods _ h1, show ¬ (a + 1 = 0) by omega, Nat.add_sub_cancel,
    show 2 * b < 2 * s - 2 by omega, show 2 * b + 1 < 2 * s - 2 by omega,
    ite_true, show 2 * b % 2 = 0 by omega, show (2 * b + 1) % 2 ≠ 0 by omega,
    show 2 * b / 2 = b by omega, show (2 * b + 1) / 2 = b by omega]
  have hqa : 2 * s - 1 - a + a = 2 * s - 1 := by omega
  have hqb : 2 * s - 1 - b + b = 2 * s - 1 := by omega
  have hq : 2 * s - 1 + 1 = 2 * s := by omega
  have hprod := congrArg (fun x => x * (2 * s - 1)) hqb
  nlinarith

open Finset in
theorem sum_range_pairs (f : ℕ → ℕ) (k : ℕ) :
    (∑ j ∈ range (2 * k), f j) = ∑ b ∈ range k, (f (2 * b) + f (2 * b + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    omega

def depthTwoConstant (s : ℕ) : ℕ :=
  (s - 1) * (8 * s + (2 * s) * (2 * s - 1) + 1) +
    2 * (4 * s + (s - 1) * (2 * s - 1)) + 6 * s + 1

open Finset in
/-- Closed form of every ordinary parent's outgoing-label sum. -/
theorem depthTwo_ordinary_sum (s a : ℕ) (hs : 2 ≤ s) (ha : a < 2 * s - 1) :
    (∑ j ∈ range (2 * s), depthTwoLabel (2 * s) 2 ((2 * s) * (a + 1) + j)) =
      (s - 1) * (8 * s + (2 * s) * (2 * s - 1) + 1) +
        2 * (4 * s + (s - 1) * (2 * s - 1)) + 3 * (s - 1) + 3 + a := by
  let f := fun j => depthTwoLabel (2 * s) 2 ((2 * s) * (a + 1) + j)
  change (∑ j ∈ range (2 * s), f j) = _
  have he : 2 * s = (2 * (s - 1) + 1) + 1 := by omega
  nth_rw 1 [he]
  rw [sum_range_succ, sum_range_succ, sum_range_pairs]
  have hout : (∑ b ∈ range (s - 1), (f (2 * b) + f (2 * b + 1))) =
      (s - 1) * (8 * s + (2 * s) * (2 * s - 1) + 1) := by
    calc
      _ = ∑ _b ∈ range (s - 1), (8 * s + (2 * s) * (2 * s - 1) + 1) := by
        apply sum_congr rfl
        intro b hb
        exact depthTwo_outer_pair s a b hs ha (mem_range.mp hb)
      _ = _ := by simp
  rw [hout]
  have hmid := depthTwo_middle_sum s a hs ha
  have hslot : 2 * (s - 1) = 2 * s - 2 := by omega
  have hslot' : 2 * (s - 1) + 1 = 2 * s - 1 := by omega
  change _ + f (2 * (s - 1)) + f (2 * (s - 1) + 1) = _
  dsimp only [f]
  rw [hslot', hslot]
  omega

open Finset in
/-- Closed form of the full ordinary-parent incidence weight. This will
feed `weight_row` after the edge bijection has been assembled. -/
theorem depthTwo_ordinary_weight (s a : ℕ) (hs : 2 ≤ s) (ha : a < 2 * s - 1) :
    depthTwoLabel (2 * s) 1 (a + 1) +
      (∑ j ∈ range (2 * s), depthTwoLabel (2 * s) 2 ((2 * s) * (a + 1) + j)) =
      depthTwoConstant s := by
  rw [depthTwo_ordinary_sum s a hs ha]
  simp only [depthTwoLabel, ite_true, Nat.mul_div_cancel_left s (by decide : 0 < 2),
    show ¬ (a + 1 = 0) by omega, ite_false]
  unfold depthTwoConstant
  omega

open Finset in
/-- The special child's leaf-edge labels sum to t squared. -/
theorem depthTwo_special_sum (s : ℕ) (hs : 2 ≤ s) :
    (∑ j ∈ range (2 * s), depthTwoLabel (2 * s) 2 j) = (2 * s) ^ 2 := by
  let e := Equiv.ofBijective (lowMap s hs) (lowMap_bijective s hs)
  have htot : (∑ p : Fin (2 * s) ⊕ Fin (2 * s), lowEntry s p) =
      ∑ i : Fin (4 * s), (i.val + 1) := by
    rw [← e.sum_comp]
    apply sum_congr rfl
    intro p _
    change lowEntry s p = lowEntry s p - 1 + 1
    exact (Nat.sub_add_cancel (lowEntry_range s hs p).1).symm
  rw [Fintype.sum_sum_type] at htot
  have hr : (∑ i : Fin (2 * s), lowEntry s (.inl i)) = (2 * s) ^ 2 + 2 * s := by
    simp_rw [← lowEntry_root]
    rw [Fin.sum_univ_eq_sum_range]
    exact depthTwo_root_sum s hs
  have hl : (∑ j : Fin (2 * s), lowEntry s (.inr j)) =
      ∑ j ∈ range (2 * s), depthTwoLabel (2 * s) 2 j := by
    simp_rw [← lowEntry_special s hs]
    rw [Fin.sum_univ_eq_sum_range]
  rw [hr, hl] at htot
  rw [Fin.sum_univ_eq_sum_range (fun i => i + 1), sum_add_distrib] at htot
  simp only [sum_const, card_range, smul_eq_mul, Nat.mul_one] at htot
  have htri := Finset.sum_range_id_mul_two (4 * s)
  have hsub : 4 * s - 1 + 1 = 4 * s := by omega
  nlinarith

open Finset in
theorem depthTwo_special_weight (s : ℕ) (hs : 2 ≤ s) :
    depthTwoLabel (2 * s) 1 0 +
      (∑ j ∈ range (2 * s), depthTwoLabel (2 * s) 2 j) = (2 * s) ^ 2 + 2 := by
  rw [depthTwo_special_sum s hs]
  simp [depthTwoLabel, Nat.add_comm]

/-- The one new colour exceeds every possible edge label. -/
theorem depthTwoConstant_large (s : ℕ) (hs : 2 ≤ s) :
    (2 * s) ^ 2 + 2 * s < depthTwoConstant s := by
  have hmul := Nat.mul_le_mul_right (8 * s + (2 * s) * (2 * s - 1) + 1)
    (show 1 ≤ s - 1 by omega)
  have hq : 2 * s - 1 + 1 = 2 * s := by omega
  have hprod := congrArg (fun x => (2 * s) * x) hq
  simp only [Nat.one_mul] at hmul
  unfold depthTwoConstant
  nlinarith

/-- The root and special-parent colours are distinct throughout t >= 4. -/
theorem depthTwo_root_special_ne (s : ℕ) (hs : 2 ≤ s) :
    (2 * s) ^ 2 + 2 * s ≠ (2 * s) ^ 2 + 2 := by omega

/-- The inherited incidence theorem specialized to any labelling realizing
its prescribed incoming-edge labels. -/
theorem literal_weight_row {t n : ℕ} (ht : 0 < t) (f : Labeling (tree t n))
    (hf : ∀ a : Nonroot t n, (f (incomingEdge ht a)).val + 1 =
      label t n a.val.1.val a.val.2.val)
    (v : Vertex t n) (hv : depth v < n) :
    weight (tree t n) f v =
      (if 0 < depth v then label t n v.1.val v.2.val else 0) +
      ∑ j : Fin t, label t n (v.1.val + 1) (t * v.2.val + j.val) := by
  rw [weight_row ht f v hv]
  simp_rw [hf]
  rfl

/-- The root closed form is a literal graph-incidence identity whenever
an edge equivalence realizes the formula. -/
theorem literal_depthTwo_root (s : ℕ) (hs : 2 ≤ s)
    (f : Labeling (tree (2 * s) 2))
    (hf : ∀ a : Nonroot (2 * s) 2,
      (f (incomingEdge (by omega) a)).val + 1 =
        label (2 * s) 2 a.val.1.val a.val.2.val) :
    weight (tree (2 * s) 2) f (root (2 * s) 2) = (2 * s) ^ 2 + 2 * s := by
  rw [literal_weight_row (by omega) f hf _ (by change 0 < 2; omega)]
  change (if 0 < 0 then _ else 0) +
    (∑ j : Fin (2 * s), label (2 * s) 2 1 ((2 * s) * 0 + j.val)) = _
  simp only [show ¬ (0 < 0) by omega, ite_false, Nat.zero_add, Nat.mul_zero,
    label, show ¬ (2 = 1) by decide, ite_true, show ¬ (2 * s = 2) by omega, ite_false, ite_true]
  rw [Fin.sum_univ_eq_sum_range]
  exact depthTwo_root_sum s hs

/-- All row-one weights, as literal incidence sums, conditional only on
realization of the inherited label formula by the supplied equivalence. -/
theorem literal_depthTwo_row_one (s : ℕ) (hs : 2 ≤ s)
    (f : Labeling (tree (2 * s) 2))
    (hf : ∀ a : Nonroot (2 * s) 2,
      (f (incomingEdge (by omega) a)).val + 1 =
        label (2 * s) 2 a.val.1.val a.val.2.val)
    (v : Vertex (2 * s) 2) (hv : v.1.val = 1) :
    weight (tree (2 * s) 2) f v =
      if v.2.val = 0 then (2 * s) ^ 2 + 2 else depthTwoConstant s := by
  rw [literal_weight_row (by omega) f hf v (by change v.1.val < 2; omega)]
  have hd : 0 < depth v := by change 0 < v.1.val; omega
  simp only [hd, ite_true, hv, label, show ¬ (2 = 1) by decide,
    show ¬ (2 * s = 2) by omega, ite_false, ite_true, show 1 + 1 = 2 by decide]
  rw [Fin.sum_univ_eq_sum_range (fun j => depthTwoLabel (2 * s) 2 ((2 * s) * v.2.val + j))]
  by_cases hi : v.2.val = 0
  · simp only [hi, ite_true, Nat.mul_zero, Nat.zero_add]
    exact depthTwo_special_weight s hs
  · simp only [hi, ite_false]
    have hib : v.2.val < 2 * s := by simpa only [hv, pow_one] using v.2.isLt
    have he : v.2.val = (v.2.val - 1) + 1 := by omega
    nth_rw 1 [he]
    conv_lhs => arg 2; arg 2; ext j; rw [he]
    exact depthTwo_ordinary_weight s (v.2.val - 1) hs (by omega)

#print axioms middleMap_bijective
#print axioms lowMap_bijective
#print axioms depthTwo_ordinary_weight
#print axioms depthTwo_special_weight
#print axioms literal_depthTwo_root
#print axioms literal_depthTwo_row_one
end Antimagic.Round3
