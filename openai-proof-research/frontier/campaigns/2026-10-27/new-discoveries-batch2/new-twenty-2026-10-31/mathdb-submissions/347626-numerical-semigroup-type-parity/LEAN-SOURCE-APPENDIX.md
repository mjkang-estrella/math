# Lean 4 source appendix for MathDB 347626

Modules are listed in build order.

### `SinghalStatement.lean`

```lean
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Set
open scoped Topology

namespace Singhal

def IsNumSg (S : Set ℕ) : Prop :=
  0 ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) ∧ Sᶜ.Finite

def HasFrob (S : Set ℕ) (f : ℕ) : Prop :=
  f ∉ S ∧ ∀ n, f < n → n ∈ S

def PF (S : Set ℕ) : Set ℕ :=
  {g | g ∉ S ∧ ∀ s ∈ S, 0 < s → g + s ∈ S}

noncomputable def sgType (S : Set ℕ) : ℕ := (PF S).ncard

def All (f : ℕ) : Set (Set ℕ) := {S | IsNumSg S ∧ HasFrob S f}

def Same (f : ℕ) : Set (Set ℕ) := {S ∈ All f | sgType S % 2 = f % 2}

noncomputable def proportion (f : ℕ) : ℝ :=
  ((Same f).ncard : ℝ) / ((All f).ncard : ℝ)

def Conjecture72 : Prop :=
  Tendsto (fun f : ℕ => ((Same f).ncard : ℝ) / ((All f).ncard : ℝ))
    atTop (𝓝 (1 / 2))

def Sgs (f : ℕ) : Finset (Finset ℕ) :=
  (Finset.Ioo 0 f).powerset.filter
    (fun A => ∀ a ∈ A, ∀ b ∈ A, a + b ≠ f ∧ (a + b < f → a + b ∈ A))

def PFenc (f : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 f).filter
    (fun g => g ∉ A ∧ ∀ s ∈ A, g + s ∈ A ∨ f < g + s)

def SameEnc (f : ℕ) : Finset (Finset ℕ) :=
  (Sgs f).filter fun A => (PFenc f A).card % 2 = f % 2

def expand (f : ℕ) (A : Finset ℕ) : Set ℕ := {x | x = 0 ∨ x ∈ A ∨ f < x}

noncomputable def restrict (f : ℕ) (S : Set ℕ) : Finset ℕ := by
  classical exact (Finset.Ioo 0 f).filter (· ∈ S)

theorem mem_sgs {f : ℕ} {A : Finset ℕ} :
    A ∈ Sgs f ↔ A ⊆ Finset.Ioo 0 f ∧
      ∀ a ∈ A, ∀ b ∈ A, a + b ≠ f ∧ (a + b < f → a + b ∈ A) := by
  simp [Sgs]

theorem pos_lt_of_mem {f : ℕ} {A : Finset ℕ} (h : A ∈ Sgs f)
    {x : ℕ} (hx : x ∈ A) : 0 < x ∧ x < f :=
  Finset.mem_Ioo.mp ((mem_sgs.mp h).1 hx)

theorem mem_expand {f x : ℕ} {A : Finset ℕ} :
    x ∈ expand f A ↔ x = 0 ∨ x ∈ A ∨ f < x := Iff.rfl

theorem mem_restrict {f x : ℕ} {S : Set ℕ} :
    x ∈ restrict f S ↔ (0 < x ∧ x < f) ∧ x ∈ S := by
  classical simp [restrict]

theorem expand_mem_all {f : ℕ} (hf : 0 < f) {A : Finset ℕ} (hA : A ∈ Sgs f) :
    expand f A ∈ All f := by
  refine ⟨⟨Or.inl rfl, ?_, ?_⟩, ?_, fun n hn => Or.inr (Or.inr hn)⟩
  · intro a ha b hb
    rcases mem_expand.mp ha with ha | ha | ha
    · simpa [ha] using hb
    rcases mem_expand.mp hb with hb | hb | hb
    · simpa [hb] using mem_expand.mpr (Or.inr (Or.inl ha))
    · have h := (mem_sgs.mp hA).2 a ha b hb
      by_cases hlt : a + b < f
      · exact Or.inr (Or.inl (h.2 hlt))
      · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inr (by omega))
  · apply (Set.finite_Iic f).subset
    intro x hx
    change x ≤ f
    exact Nat.le_of_not_gt fun h => hx (Or.inr (Or.inr h))
  · intro h
    rcases mem_expand.mp h with h | h | h
    · omega
    · exact (Nat.lt_irrefl f) (pos_lt_of_mem hA h).2
    · omega

theorem restrict_mem_sgs {f : ℕ} {S : Set ℕ} (hS : S ∈ All f) :
    restrict f S ∈ Sgs f := by
  refine mem_sgs.mpr ⟨fun x hx => Finset.mem_Ioo.mpr (mem_restrict.mp hx).1, ?_⟩
  intro a ha b hb
  obtain ⟨hapos, haS⟩ := mem_restrict.mp ha
  obtain ⟨_, hbS⟩ := mem_restrict.mp hb
  have hab := hS.1.2.1 a haS b hbS
  refine ⟨fun he => hS.2.1 (he ▸ hab), fun hl => mem_restrict.mpr ⟨⟨?_, hl⟩, hab⟩⟩
  omega

theorem expand_restrict {f : ℕ} {S : Set ℕ} (hS : S ∈ All f) :
    expand f (restrict f S) = S := by
  ext x
  rw [mem_expand, mem_restrict]
  constructor
  · rintro (rfl | hx | hx)
    · exact hS.1.1
    · exact hx.2
    · exact hS.2.2 _ hx
  · intro hx
    by_cases h0 : x = 0
    · exact Or.inl h0
    by_cases hlt : x < f
    · exact Or.inr (Or.inl ⟨⟨by omega, hlt⟩, hx⟩)
    · refine Or.inr (Or.inr (Nat.lt_of_not_ge fun hle => ?_))
      have he : x = f := by omega
      exact hS.2.1 (he ▸ hx)

theorem restrict_expand {f : ℕ} {A : Finset ℕ} (hA : A ∈ Sgs f) :
    restrict f (expand f A) = A := by
  ext x
  rw [mem_restrict, mem_expand]
  constructor
  · rintro ⟨⟨hp, hl⟩, h0 | hx | hu⟩
    · omega
    · exact hx
    · omega
  · intro hx
    exact ⟨pos_lt_of_mem hA hx, Or.inr (Or.inl hx)⟩

theorem pf_expand {f : ℕ} {A : Finset ℕ} (hA : A ∈ Sgs f) :
    PF (expand f A) = (PFenc f A : Set ℕ) := by
  ext g
  change (g ∉ expand f A ∧ _) ↔ g ∈ PFenc f A
  simp only [PFenc, Finset.mem_filter, Finset.mem_Icc, mem_expand]
  constructor
  · rintro ⟨hg, hs⟩
    refine ⟨⟨?_, ?_⟩, fun h => hg (Or.inr (Or.inl h)), ?_⟩
    · by_contra! h
      exact hg (Or.inl (by omega))
    · exact Nat.le_of_not_gt fun h => hg (Or.inr (Or.inr h))
    · intro s hsA
      rcases hs s (Or.inr (Or.inl hsA)) (pos_lt_of_mem hA hsA).1 with h | h | h
      · omega
      · exact Or.inl h
      · exact Or.inr h
  · rintro ⟨⟨hp, hl⟩, hg, hs⟩
    refine ⟨?_, ?_⟩
    · rintro (h | h | h)
      · omega
      · exact hg h
      · omega
    · rintro s (h | h | h) hpos
      · omega
      · exact Or.inr (hs s h)
      · exact Or.inr (Or.inr (by omega))

theorem type_expand {f : ℕ} {A : Finset ℕ} (hA : A ∈ Sgs f) :
    sgType (expand f A) = (PFenc f A).card := by
  rw [sgType, pf_expand hA, Set.ncard_coe_finset]

theorem all_image {f : ℕ} (hf : 0 < f) : All f = expand f '' (Sgs f : Set (Finset ℕ)) := by
  ext S
  constructor
  · intro hS
    exact ⟨restrict f S, restrict_mem_sgs hS, expand_restrict hS⟩
  · rintro ⟨A, hA, rfl⟩
    exact expand_mem_all hf hA

theorem same_image {f : ℕ} (hf : 0 < f) :
    Same f = expand f '' (SameEnc f : Set (Finset ℕ)) := by
  ext S
  constructor
  · rintro ⟨hS, hp⟩
    refine ⟨restrict f S, ?_, expand_restrict hS⟩
    change restrict f S ∈ SameEnc f
    refine Finset.mem_filter.mpr ⟨restrict_mem_sgs hS, ?_⟩
    rwa [← type_expand (restrict_mem_sgs hS), expand_restrict hS]
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨h, hp⟩ := Finset.mem_filter.mp hA
    exact ⟨expand_mem_all hf h, by rw [type_expand h]; exact hp⟩

theorem expand_injOn (f : ℕ) : Set.InjOn (expand f) (Sgs f : Set (Finset ℕ)) := by
  intro A hA B hB he
  simpa only [restrict_expand hA, restrict_expand hB] using congrArg (restrict f) he

theorem all_finite (f : ℕ) : (All f).Finite := by
  by_cases hf : 0 < f
  · rw [all_image hf]
    exact (Sgs f).finite_toSet.image _
  · have hz : All f = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun S h =>
      h.2.1 ((show f = 0 by omega).symm ▸ h.1.1)
    rw [hz]
    exact Set.finite_empty

theorem same_finite (f : ℕ) : (Same f).Finite :=
  (all_finite f).subset fun _ h => h.1

theorem all_ncard {f : ℕ} (hf : 0 < f) : (All f).ncard = (Sgs f).card := by
  rw [all_image hf, (expand_injOn f).ncard_image, Set.ncard_coe_finset]

theorem same_ncard {f : ℕ} (hf : 0 < f) : (Same f).ncard = (SameEnc f).card := by
  rw [same_image hf, Set.InjOn.ncard_image, Set.ncard_coe_finset]
  exact (expand_injOn f).mono fun _ h => Finset.mem_filter.mp h |>.1

theorem sgs_nonempty (f : ℕ) : (Sgs f).Nonempty := by
  exact ⟨∅, mem_sgs.mpr (by simp)⟩

theorem denominator_pos {f : ℕ} (hf : 0 < f) : 0 < (All f).ncard := by
  rw [all_ncard hf]
  exact Finset.card_pos.mpr (sgs_nonempty f)

theorem table_one_small :
    ((Sgs 2).card, (SameEnc 2).card) = (1, 1) ∧
    ((Sgs 3).card, (SameEnc 3).card) = (2, 2) ∧
    ((Sgs 4).card, (SameEnc 4).card) = (2, 2) ∧
    ((Sgs 5).card, (SameEnc 5).card) = (5, 4) ∧
    ((Sgs 6).card, (SameEnc 6).card) = (4, 3) := by decide

#print axioms Conjecture72
#print axioms all_ncard
#print axioms same_ncard
#print axioms denominator_pos
#print axioms table_one_small

end Singhal
```

### `SinghalCounting.lean`

```lean
import SinghalStatement
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset
open scoped BigOperators

namespace Singhal

/-- An injective list of recorded coordinates gives a product bound on the count. -/
theorem card_le_prod_of_coordinates {α ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (F : Finset α) (I : Finset ι) (choices : ι → Finset β) (record : α → ι → β)
    (hmem : ∀ x ∈ F, ∀ i ∈ I, record x i ∈ choices i)
    (hinj : ∀ x ∈ F, ∀ y ∈ F, (∀ i ∈ I, record x i = record y i) → x = y) :
    F.card ≤ ∏ i ∈ I, (choices i).card := by
  rw [← Finset.card_pi]
  exact Finset.card_le_card_of_injOn
    (fun x i _ => record x i)
    (fun x hx => Finset.mem_pi.mpr fun i hi => hmem x hx i hi)
    (fun x hx y hy hxy => hinj x hx y hy fun i hi => congrFun (congrFun hxy i) hi)

/-- Split a count into recorded coordinates and sum the sizes of its fibers. -/
theorem card_le_sum_of_coordinates {α ι : Type*} [DecidableEq ι]
    (F : Finset α) (I : Finset ι) (record : α → ι)
    (hmem : ∀ x ∈ F, record x ∈ I) (bound : ι → ℝ)
    (hbound : ∀ i ∈ I, ((F.filter (fun x => record x = i)).card : ℝ) ≤ bound i) :
    (F.card : ℝ) ≤ ∑ i ∈ I, bound i := by
  rw [Finset.card_eq_sum_card_fiberwise hmem, Nat.cast_sum]
  exact Finset.sum_le_sum hbound

def upper (f : ℕ) : Finset ℕ := Ioo (f / 2) f

theorem upper_card (f : ℕ) : (upper f).card = (f - 1) / 2 := by
  rw [upper, Nat.card_Ioo]
  omega

theorem large_mult_lower_bound (f : ℕ) : 2 ^ ((f - 1) / 2) ≤ (Sgs f).card := by
  rw [← upper_card, ← Finset.card_powerset]
  apply Finset.card_le_card
  intro A hA
  have hsub := Finset.mem_powerset.mp hA
  refine mem_sgs.mpr ⟨?_, ?_⟩
  · intro x hx
    have h := Finset.mem_Ioo.mp (hsub hx)
    exact Finset.mem_Ioo.mpr ⟨by omega, h.2⟩
  · intro a ha b hb
    have h1 := (Finset.mem_Ioo.mp (hsub ha)).1
    have h2 := (Finset.mem_Ioo.mp (hsub hb)).1
    omega

/-- The least positive member, with the ordinary semigroup handled by the sentinel (f+1). -/
def multiplicity (f : ℕ) (A : Finset ℕ) : ℕ := (insert (f + 1) A).min' (by simp)

theorem multiplicity_le {f : ℕ} {A : Finset ℕ} {x : ℕ} (hx : x ∈ A) :
    multiplicity f A ≤ x :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem hx)

theorem multiplicity_mem {f : ℕ} {A : Finset ℕ}
    (h : multiplicity f A ≤ f) : multiplicity f A ∈ A := by
  have hm := Finset.min'_mem (insert (f + 1) A) (by simp)
  change multiplicity f A ∈ insert (f + 1) A at hm
  rcases Finset.mem_insert.mp hm with hm | hm
  · omega
  · exact hm

theorem multiplicity_pos {f : ℕ} {A : Finset ℕ} (hA : A ∈ Sgs f) :
    0 < multiplicity f A := by
  by_cases h : multiplicity f A ≤ f
  · exact (pos_lt_of_mem hA (multiplicity_mem h)).1
  · omega

def atMult (f m : ℕ) : Finset (Finset ℕ) :=
  (Sgs f).filter (fun A => multiplicity f A = m)

theorem mem_atMult {f m : ℕ} {A : Finset ℕ} :
    A ∈ atMult f m ↔ A ∈ Sgs f ∧ multiplicity f A = m := Finset.mem_filter

theorem mult_mem {f m : ℕ} {A : Finset ℕ} (ha : A ∈ atMult f m) (hmf : m ≤ f) :
    m ∈ A := by
  rw [← (mem_atMult.mp ha).2]
  apply multiplicity_mem
  rwa [(mem_atMult.mp ha).2]

theorem mult_le_mem {f m x : ℕ} {A : Finset ℕ} (ha : A ∈ atMult f m) (hx : x ∈ A) :
    m ≤ x := (mem_atMult.mp ha).2 ▸ multiplicity_le hx

theorem sum_mem_enc {f a b : ℕ} {A : Finset ℕ} (hA : A ∈ Sgs f)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a + b < f) : a + b ∈ A :=
  ((mem_sgs.mp hA).2 a ha b hb).2 hab

theorem sum_ne_f {f a b : ℕ} {A : Finset ℕ} (hA : A ∈ Sgs f)
    (ha : a ∈ A) (hb : b ∈ A) : a + b ≠ f :=
  ((mem_sgs.mp hA).2 a ha b hb).1

theorem add_multiple_mem {f m a : ℕ} {A : Finset ℕ} (hA : A ∈ Sgs f)
    (hm : m ∈ A) (ha : a ∈ A) (k : ℕ) (hk : a + k * m < f) : a + k * m ∈ A := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc] at hk ⊢
    exact sum_mem_enc hA (ih (by omega)) hm hk

theorem add_multiple_ne_f {f m a : ℕ} {A : Finset ℕ} (hA : A ∈ Sgs f)
    (hm : m ∈ A) (ha : a ∈ A) (k : ℕ) : a + k * m ≠ f := by
  intro he
  have hpos := (pos_lt_of_mem hA hm).1
  cases k with
  | zero => have := (pos_lt_of_mem hA ha).2; simp at he; omega
  | succ k =>
    rw [Nat.succ_mul, ← Nat.add_assoc] at he
    exact sum_ne_f hA (add_multiple_mem hA hm ha k (by omega)) hm he

theorem atMult_eq_empty_of_dvd {f m : ℕ} (hmf : m ≤ f) (hd : m ∣ f) :
    atMult f m = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A hA
  have hm := mult_mem hA hmf
  have hp := pos_lt_of_mem (mem_atMult.mp hA).1 hm
  obtain ⟨k, hk⟩ := hd
  cases k with
  | zero => simp at hk; omega
  | succ k =>
    apply add_multiple_ne_f (mem_atMult.mp hA).1 hm hm k
    rw [hk, Nat.mul_succ, Nat.mul_comm m k, Nat.add_comm]

end Singhal
```

### `SinghalPairs.lean`

```lean
import SinghalCounting

open Finset
open scoped BigOperators

namespace Singhal

def agrees (p : Option Bool) (b : Bool) : Bool :=
  p.isNone || p == some b

private def singlePatterns (p : Option Bool) : Finset Bool :=
  univ.filter fun b => agrees p b

private def pairPatterns (p q : Option Bool) : Finset (Bool × Bool) :=
  univ.filter fun (a,b) => (!a || b) && agrees p a && agrees q b

private noncomputable def factor (p : Option Bool) (dear : Bool) : ℝ :=
  if dear then 1 / 2 else if p.isNone then 1 else 2 / 3

private theorem factor_nonneg (p : Option Bool) (d : Bool) : 0 ≤ factor p d := by
  cases d <;> cases p <;> norm_num [factor]

private theorem single_bound (p : Option Bool) (d : Bool) :
    ((singlePatterns p).card : ℝ) ≤ 2 * factor p d
      ∨ (d = true ∧ p = none) := by
  cases d <;> rcases p with _ | (_ | _)
  all_goals
    first
    | right; exact ⟨rfl, rfl⟩
    | left
      first
      | change ((1 : ℕ) : ℝ) ≤ _; norm_num [factor]
      | change ((2 : ℕ) : ℝ) ≤ _; norm_num [factor]

private theorem pair_bound (p q : Option Bool) (d : Bool)
    (hd : d = true → p = some true) :
    ((pairPatterns p q).card : ℝ) ≤ 3 * factor p d * factor q false := by
  rcases p with _ | (_ | _) <;> rcases q with _ | (_ | _) <;> cases d
  all_goals
    first
    | exact False.elim (by have h := hd rfl; contradiction)
    | change ((0 : ℕ) : ℝ) ≤ _; norm_num [factor]
    | change ((1 : ℕ) : ℝ) ≤ _; norm_num [factor]
    | change ((2 : ℕ) : ℝ) ≤ _; norm_num [factor]
    | change ((3 : ℕ) : ℝ) ≤ _; norm_num [factor]

def bit (X : Finset ℕ) (n : ℕ) : Bool := decide (n ∈ X)

/-- Count a family of subsets with disjoint implication pairs and prescribed bits.
A prescribed true bit away from the heads costs a factor (1/2). The other
prescribed bits cost at most (2/3) each. -/
theorem card_le_of_disjoint_pairs (F : Finset (Finset ℕ)) (U T D E : Finset ℕ)
    (d : ℕ) (pin : ℕ → Option Bool)
    (hT : T ⊆ U) (hH : T.image (· + d) ⊆ U)
    (hTH : Disjoint T (T.image (· + d)))
    (hD : D ⊆ U) (hE : E ⊆ U) (hDE : Disjoint D E)
    (hDH : Disjoint D (T.image (· + d)))
    (hpinD : ∀ x ∈ D, pin x = some true)
    (hpinE : ∀ x ∈ E, (pin x).isNone = false)
    (hpin0 : ∀ x ∉ D ∪ E, pin x = none)
    (hsub : ∀ X ∈ F, X ⊆ U)
    (hfixed : ∀ X ∈ F, ∀ x ∈ U, (agrees (pin x) (bit X x)) = true)
    (himp : ∀ X ∈ F, ∀ t ∈ T, t ∈ X → t + d ∈ X) :
    (F.card : ℝ) ≤ (2 : ℝ) ^ U.card * (3 / 4) ^ T.card *
      (1 / 2) ^ D.card * (2 / 3) ^ E.card := by
  classical
  let H := T.image (· + d)
  let J := U \ (T ∪ H)
  let P := T ∪ J
  let choice : ℕ → Finset (Bool × Bool) := fun x =>
    if x ∈ T then pairPatterns (pin x) (pin (x + d))
    else (singlePatterns (pin x)).image (·, false)
  let recode : Finset ℕ → ℕ → Bool × Bool := fun X x =>
    (bit X x, if x ∈ T then bit X (x + d) else false)
  have hTJ : Disjoint T J := Finset.disjoint_left.mpr fun x hx hJ =>
    (Finset.mem_sdiff.mp hJ).2 (Finset.mem_union_left _ hx)
  have hJH : Disjoint J H := Finset.disjoint_left.mpr fun x hx hH =>
    (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right _ hH)
  have hpart : T ∪ H ∪ J = U :=
    Finset.union_sdiff_of_subset (Finset.union_subset hT hH)
  have horig := card_le_prod_of_coordinates F P choice recode
    (by
      intro X hX x hx
      by_cases h : x ∈ T
      · simp only [choice, recode, ite_eq_left h, pairPatterns, Finset.mem_filter, Finset.mem_univ,
          true_and, Bool.and_eq_true, hfixed X hX x (hT h),
          hfixed X hX (x+d) (hH (Finset.mem_image_of_mem _ h)), and_true]
        simp only [bit, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          decide_eq_true_eq]
        exact or_iff_not_imp_left.mpr (fun hn => himp X hX x h (not_not.mp hn))
      · have hU := (Finset.mem_sdiff.mp ((Finset.mem_union.mp hx).resolve_left h)).1
        simp only [choice, recode, ite_eq_right h, singlePatterns, Finset.mem_image,
          Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, and_true]
        exact ⟨_, hfixed X hX x hU, rfl⟩)
    (by
      intro X hX Y hY he
      ext x
      by_cases hx : x ∈ U
      · rw [← hpart, Finset.mem_union, Finset.mem_union] at hx
        have eqbit : bit X x = bit Y x := by
          rcases hx with (ht | hh) | hj
          · exact congrArg Prod.fst (he x (Finset.mem_union_left _ ht))
          · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hh
            simpa [recode, ht] using congrArg Prod.snd (he t (Finset.mem_union_left _ ht))
          · exact congrArg Prod.fst (he x (Finset.mem_union_right _ hj))
        simpa [bit, decide_eq_decide] using eqbit
      · exact iff_of_false (fun h => hx (hsub X hX h)) (fun h => hx (hsub Y hY h)))
  let w : ℕ → ℝ := fun x => factor (pin x) (decide (x ∈ D))
  have hw (x : ℕ) : 0 ≤ w x := factor_nonneg _ _
  have hpb (x : ℕ) (hx : x ∈ T) :
      ((choice x).card : ℝ) ≤ 3 * w x * w (x + d) := by
    have hxd : x + d ∉ D := fun h => Finset.disjoint_left.mp hDH h (Finset.mem_image_of_mem _ hx)
    simpa [choice, w, hx, hxd] using
      pair_bound (pin x) (pin (x+d)) (decide (x ∈ D)) (by simpa using hpinD x)
  have hjb (x : ℕ) (hx : x ∈ J) : ((choice x).card : ℝ) ≤ 2 * w x := by
    have hxt : x ∉ T := fun ht => Finset.disjoint_left.mp hTJ ht hx
    simp only [choice, ite_eq_right hxt, w]
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
    apply (single_bound (pin x) (decide (x ∈ D))).resolve_right
    rintro ⟨hd, he⟩
    simpa [he] using hpinD x (of_decide_eq_true hd)
  have hProd : (F.card : ℝ) ≤
      (∏ x ∈ T, 3 * w x * w (x+d)) * ∏ x ∈ J, 2 * w x := by
    apply (show (F.card : ℝ) ≤ ∏ x ∈ P, ((choice x).card : ℝ) by exact_mod_cast horig).trans
    rw [Finset.prod_union hTJ]
    exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hpb)
      (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hjb)
      (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
      (Finset.prod_nonneg fun x _ => mul_nonneg (mul_nonneg (by norm_num) (hw x)) (hw (x+d)))
  have hShift : (∏ x ∈ T, w (x+d)) = ∏ x ∈ H, w x := by
    rw [Finset.prod_image (fun a _ b _ h => Nat.add_right_cancel h)]
  have hHC : H.card = T.card :=
    Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)
  have hPC : U.card = 2 * T.card + J.card := by
    rw [← hpart, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint hTH, hHC]
    · omega
    · exact Finset.disjoint_left.mpr fun x hx hj =>
        (Finset.mem_sdiff.mp hj).2 hx
  have hwProd : (∏ x ∈ U, w x) = (1/2 : ℝ)^D.card * (2/3 : ℝ)^E.card := by
    have hd : D ∪ E ⊆ U := Finset.union_subset hD hE
    rw [← Finset.union_sdiff_of_subset hd, Finset.prod_union,
      Finset.prod_union hDE]
    · have hpD : (∏ x ∈ D, w x) = (1/2 : ℝ)^D.card := by
        rw [← Finset.prod_const]
        exact Finset.prod_congr rfl fun x hx => by simp [w, factor, hx]
      have hpE : (∏ x ∈ E, w x) = (2/3 : ℝ)^E.card := by
        rw [← Finset.prod_const]
        exact Finset.prod_congr rfl fun x hx => by
          have hn : x ∉ D := fun h => Finset.disjoint_left.mp hDE h hx
          have he : pin x ≠ none := by intro he; simpa [he] using hpinE x hx
          simp [w, factor, hn, he]
      have hp0 : (∏ x ∈ U \ (D ∪ E), w x) = 1 := by
        apply Finset.prod_eq_one
        intro x hx
        have hn := (Finset.mem_sdiff.mp hx).2
        have hnD : x ∉ D := fun hd => hn (Finset.mem_union_left _ hd)
        simp [w, factor, hpin0 x hn, hnD]
      rw [hpD, hpE, hp0, mul_one]
    · exact Finset.disjoint_left.mpr fun x h hd => (Finset.mem_sdiff.mp hd).2 h
  have hwProd' : (∏ x ∈ T, w x) * (∏ x ∈ H, w x) * (∏ x ∈ J, w x) =
      (1/2 : ℝ)^D.card * (2/3 : ℝ)^E.card := by
    rw [← Finset.prod_union hTH, ← Finset.prod_union, hpart, hwProd]
    exact Finset.disjoint_left.mpr fun _ hx hJ => (Finset.mem_sdiff.mp hJ).2 hx
  apply hProd.trans_eq
  simp only [Finset.prod_mul_distrib, Finset.prod_const, hShift]
  rw [show (3 : ℝ)^T.card * (∏ x ∈ T, w x) * (∏ x ∈ H, w x) *
      (2^J.card * ∏ x ∈ J, w x) =
      3^T.card * 2^J.card * ((∏ x ∈ T, w x) * (∏ x ∈ H, w x) *
        ∏ x ∈ J, w x) by ring, hwProd', hPC, pow_add, pow_mul]
  rw [show (4 : ℝ) = 2^2 by norm_num]
  simp only [div_pow, mul_assoc]
  have hne : (2 : ℝ)^2 ^ T.card ≠ 0 := by positivity
  field_simp

end Singhal
```

### `SinghalMedium.lean`

```lean
import SinghalPairs

open Finset
open scoped BigOperators

namespace Singhal

private theorem sum_powerset_pow (I : Finset ℕ) (q : ℝ) :
    (∑ X ∈ I.powerset, q ^ X.card) = (1+q)^I.card := by
  simpa [add_comm] using (Finset.prod_add (fun _ : ℕ => q) (fun _ => (1:ℝ)) I).symm

/-- Backelin's bound for multiplicities between (f/4) and (f/2),
with an inessential constant dropped. -/
theorem medium_count {f m : ℕ} (hm : 0 < m) (hlo : f < 4*m)
    (hhi : 2*m < f) :
    ((atMult f m).card : ℝ) ≤
      (2 : ℝ)^((f-1)/2) * (11/12)^((f-1)/2-m) := by
  classical
  let a := (f-1)/2
  let U := upper f
  let T := Icc (f-a) (f-m-1)
  let I := Ioc m a
  let record := fun A : Finset ℕ => (A \ U).erase m
  have ha : m ≤ a := by dsimp [a]; omega
  have hUc : U.card = a := upper_card f
  have hTc : T.card = a-m := by dsimp [T]; rw [Nat.card_Icc]; omega
  have hIc : I.card = a-m := Nat.card_Ioc m a
  have hT : T ⊆ U := by
    intro t ht
    have h := Finset.mem_Icc.mp ht
    apply Finset.mem_Ioo.mpr
    dsimp [a] at h
    omega
  have hH : T.image (·+m) ⊆ U := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have h := Finset.mem_Icc.mp ht
    apply Finset.mem_Ioo.mpr
    dsimp [a] at h
    omega
  have hTH : Disjoint T (T.image (·+m)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have ht' := (Finset.mem_Icc.mp ht).1
    have hx' := (Finset.mem_Icc.mp hx).2
    dsimp [a] at ht'
    omega
  have hmA {A : Finset ℕ} (hA : A ∈ atMult f m) : m ∈ A :=
    mult_mem hA (by omega)
  have hmU : m ∉ U := by simp [U, upper]; omega
  have hmLower {A : Finset ℕ} (hA : A ∈ atMult f m) : m ∈ A \ U :=
    Finset.mem_sdiff.mpr ⟨hmA hA, hmU⟩
  have hrecord {A : Finset ℕ} (hA : A ∈ atMult f m) : record A ∈ I.powerset := by
    apply Finset.mem_powerset.mpr
    intro x hx
    obtain ⟨hn, hx⟩ := Finset.mem_erase.mp hx
    obtain ⟨hx, hxU⟩ := Finset.mem_sdiff.mp hx
    have ⟨_, hxf⟩ := pos_lt_of_mem (mem_atMult.mp hA).1 hx
    have hxmin := mult_le_mem hA hx
    have hxx : x+x ≠ f := sum_ne_f (mem_atMult.mp hA).1 hx hx
    have hnot : ¬f/2 < x := fun h => hxU (Finset.mem_Ioo.mpr ⟨h, hxf⟩)
    apply Finset.mem_Ioc.mpr
    dsimp [a]
    omega
  have hfiber (Z : Finset ℕ) (hZ : Z ∈ I.powerset) :
      (((atMult f m).filter (fun A => record A = Z)).card : ℝ) ≤
      (2:ℝ)^a * (3/4)^(a-m) * (2/9)^Z.card := by
    let G := (atMult f m).filter (fun A => record A = Z)
    change (G.card : ℝ) ≤ _
    by_cases hG : G.Nonempty
    · let X := insert m Z
      have hmZ : m ∉ Z := fun h => (Finset.mem_Ioc.mp (Finset.mem_powerset.mp hZ h)).1.false
      have hxBounds {x : ℕ} (hx : x ∈ X) : m ≤ x ∧ x ≤ a := by
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨le_rfl, ha⟩
        · have h := Finset.mem_Ioc.mp (Finset.mem_powerset.mp hZ hx)
          exact ⟨h.1.le, h.2⟩
      have hX (A : Finset ℕ) (hA : A ∈ G) : A \ U = X := by
        unfold X
        rw [← (Finset.mem_filter.mp hA).2]
        exact (Finset.insert_erase (hmLower (Finset.mem_filter.mp hA).1)).symm
      have hXA {A : Finset ℕ} (hA : A ∈ G) : X ⊆ A := by
        rw [← hX A hA]
        exact sdiff_subset
      let b := X.max' ⟨m, Finset.mem_insert_self _ _⟩
      have hb : b ∈ X := Finset.max'_mem _ _
      have hbmax {x : ℕ} (hx : x ∈ X) : x ≤ b := Finset.le_max' _ _ hx
      let D := X.image (m+·)
      let C := Z.image (b+·)
      let B := X.image (f-·)
      let E := B ∪ C
      have hDU : D ⊆ U := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        have h := hxBounds hz
        apply Finset.mem_Ioo.mpr
        dsimp [a] at h
        omega
      have hCU : C ⊆ U := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        have hz' := hxBounds (Finset.mem_insert_of_mem hz)
        have hb' := hxBounds hb
        apply Finset.mem_Ioo.mpr
        dsimp [a] at hz' hb'
        omega
      have hBU : B ⊆ U := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        have h := hxBounds hz
        apply Finset.mem_Ioo.mpr
        dsimp [a] at h
        omega
      have hDin {A : Finset ℕ} (hA : A ∈ G) {x : ℕ} (hx : x ∈ D) : x ∈ A := by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        exact sum_mem_enc (mem_atMult.mp (Finset.mem_filter.mp hA).1).1
          (hmA (Finset.mem_filter.mp hA).1) (hXA hA hz) (Finset.mem_Ioo.mp (hDU hx)).2
      have hCin {A : Finset ℕ} (hA : A ∈ G) {x : ℕ} (hx : x ∈ C) : x ∈ A := by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        exact sum_mem_enc (mem_atMult.mp (Finset.mem_filter.mp hA).1).1
          (hXA hA hb) (hXA hA (Finset.mem_insert_of_mem hz)) (Finset.mem_Ioo.mp (hCU hx)).2
      have hBout {A : Finset ℕ} (hA : A ∈ G) {x : ℕ} (hx : x ∈ B) : x ∉ A := by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        have hz' := hxBounds hz
        intro hin
        apply sum_ne_f (mem_atMult.mp (Finset.mem_filter.mp hA).1).1 (hXA hA hz) hin
        omega
      obtain ⟨A₀, hA₀⟩ := hG
      have hDB : Disjoint D B := Finset.disjoint_left.mpr fun _ hD hB =>
        hBout hA₀ hB (hDin hA₀ hD)
      have hBC : Disjoint B C := Finset.disjoint_left.mpr fun _ hB hC =>
        hBout hA₀ hB (hCin hA₀ hC)
      have hDC : Disjoint D C := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp hx
        obtain ⟨v, hv, hev⟩ := Finset.mem_image.mp hy
        have := hbmax hu
        have := (Finset.mem_Ioc.mp (Finset.mem_powerset.mp hZ hv)).1
        omega
      have hDH : Disjoint D (T.image (·+m)) := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp hx
        obtain ⟨t, ht, het⟩ := Finset.mem_image.mp hy
        have h := (hxBounds hu).2
        have ht' := (Finset.mem_Icc.mp ht).1
        dsimp [a] at h ht'
        omega
      have hDc : D.card = Z.card+1 := by
        rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),
          Finset.card_insert_of_notMem hmZ]
      have hEc : E.card = 2*Z.card+1 := by
        have hbcard : B.card = X.card := by
          apply Finset.card_image_of_injOn
          intro x hx y hy h
          have := (hxBounds hx).2
          have := (hxBounds hy).2
          change f-x = f-y at h
          omega
        rw [Finset.card_union_of_disjoint hBC, hbcard,
          Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),
          Finset.card_insert_of_notMem hmZ]
        omega
      let F := G.image (· ∩ U)
      have hGc : F.card = G.card := by
        apply Finset.card_image_of_injOn
        intro A hA A' hA' he
        change A ∩ U = A' ∩ U at he
        calc
          A = A ∩ U ∪ (A \ U) := (by rw [Finset.union_comm, Finset.sdiff_union_inter])
          _ = A' ∩ U ∪ (A' \ U) := by rw [he, hX A hA, hX A' hA']
          _ = A' := by rw [Finset.union_comm, Finset.sdiff_union_inter]
      let pin (x : ℕ) : Option Bool :=
        if x ∈ B then some false else if x ∈ D ∪ C then some true else none
      have hresult := card_le_of_disjoint_pairs F U T D E m pin hT hH hTH hDU
        (Finset.union_subset hBU hCU)
        (Finset.disjoint_left.mpr fun x hd he => by
          rcases Finset.mem_union.mp he with he | he
          · exact Finset.disjoint_left.mp hDB hd he
          · exact Finset.disjoint_left.mp hDC hd he)
        hDH
        (by
          intro x hx
          have hn : x ∉ B := fun h => Finset.disjoint_left.mp hDB hx h
          simp only [pin, ite_eq_right hn, ite_eq_left (Finset.mem_union_left C hx)])
        (by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · simp [pin, hx]
          · by_cases h : x ∈ B
            · simp [pin, h]
            · simp only [pin, ite_eq_right h, ite_eq_left (Finset.mem_union_right D hx), Option.isNone])
        (by
          intro x hx
          have hnB : x ∉ B := fun h => hx (Finset.mem_union_right _ (Finset.mem_union_left C h))
          have hnDC : x ∉ D ∪ C := by
            intro h
            rcases Finset.mem_union.mp h with h | h
            · exact hx (Finset.mem_union_left E h)
            · exact hx (Finset.mem_union_right D (Finset.mem_union_right B h))
          simp only [pin, ite_eq_right hnB, ite_eq_right hnDC])
        (by
          intro Y hY
          obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hY
          exact Finset.inter_subset_right)
        (by
          intro Y hY x hx
          obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hY
          by_cases hB : x ∈ B
          · simp [pin, hB, agrees, bit, hBout hA hB]
          · by_cases hY : x ∈ D ∪ C
            · have hxA : x ∈ A := (Finset.mem_union.mp hY).elim (hDin hA) (hCin hA)
              rw [show pin x = some true by simp only [pin, ite_eq_right hB, ite_eq_left hY]]
              simp [agrees, bit, hxA, hx]
            · simp only [pin, ite_eq_right hB, ite_eq_right hY, agrees, Option.isNone, Bool.true_or])
        (by
          intro Y hY t ht htY
          obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hY
          have htU := hH (Finset.mem_image_of_mem _ ht)
          exact Finset.mem_inter.mpr
            ⟨sum_mem_enc (mem_atMult.mp (Finset.mem_filter.mp hA).1).1
              (Finset.mem_inter.mp htY).1 (hmA (Finset.mem_filter.mp hA).1)
              (Finset.mem_Ioo.mp htU).2, htU⟩)
      rw [hGc, hUc, hTc, hDc, hEc] at hresult
      apply hresult.trans
      rw [pow_succ (1/2 : ℝ), pow_succ (2/3 : ℝ), pow_mul]
      rw [show (2/9 : ℝ)^Z.card = (1/2)^Z.card * ((2/3)^2)^Z.card by rw [← mul_pow]; norm_num]
      have hn : 0 ≤ (2:ℝ)^a * (3/4)^(a-m) *
        ((1/2 : ℝ)^Z.card * ((2/3 : ℝ)^2)^Z.card) := by positivity
      nlinarith only [hn]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hG, Finset.card_empty, Nat.cast_zero]
      positivity
  calc
    ((atMult f m).card : ℝ) ≤
        ∑ Z ∈ I.powerset, (2:ℝ)^a * (3/4)^(a-m) * (2/9)^Z.card :=
      card_le_sum_of_coordinates _ _ record (fun _ h => hrecord h) _ hfiber
    _ = _ := by
      rw [← Finset.mul_sum, sum_powerset_pow, hIc, mul_assoc, ← mul_pow]
      norm_num [a]

end Singhal
```

### `SinghalResidues.lean`

```lean
import SinghalCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open Finset
open scoped BigOperators

namespace Singhal

noncomputable def rho : ℝ := 63 / 32

theorem rho_pos : 0 < rho := by norm_num [rho]

theorem rho_gt_one : 1 < rho := by norm_num [rho]

theorem rho_lt_two : rho < 2 := by norm_num [rho]

private def triangle (j : ℕ) : Finset (ℕ × ℕ) :=
  ((range (j+1)).sigma (fun x => range (j+1-x))).map
    ⟨fun x => (x.1,x.2), fun _ _ h => Sigma.ext (congrArg Prod.fst h)
      (heq_of_eq (congrArg Prod.snd h))⟩

private theorem mem_triangle {j u v : ℕ} : (u,v) ∈ triangle j ↔ u+v ≤ j := by
  unfold triangle
  rw [Finset.mem_map]
  constructor
  · rintro ⟨⟨a,b⟩, h, he⟩
    simp only [Finset.mem_sigma, Finset.mem_range] at h
    have e1 := congrArg Prod.fst he
    have e2 := congrArg Prod.snd he
    change a = u at e1
    change b = v at e2
    omega
  · intro h
    exact ⟨⟨u,v⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (by change u < j+1; omega),
      Finset.mem_range.mpr (by change v < j+1-u; omega)⟩, rfl⟩

private theorem triangle_card (j : ℕ) :
    ((triangle j).card : ℝ) = ((j : ℝ)+1) * ((j : ℝ)+2) / 2 := by
  rw [triangle, Finset.card_map, Finset.card_sigma]
  simp only [Finset.card_range]
  have h : (∑ x ∈ range (j+1), (j+1-x)) = ∑ x ∈ range (j+1), (x+1) := by
    rw [← Finset.sum_range_reflect (fun x => j+1-x) (j+1)]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_range.mp hx
    omega
  have hsum := Finset.sum_range_id_mul_two (j+1)
  have hsum' := congrArg (fun x : ℕ => (x : ℝ)) hsum
  simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hsum'
  rw [h, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range, Nat.mul_one,
    Nat.cast_add, Nat.cast_add, Nat.cast_one]
  push_cast at hsum' ⊢
  nlinarith only [hsum']

private theorem triangle_bound {j : ℕ} (hj : 4 ≤ j) :
    ((triangle j).card : ℝ) ≤ rho ^ j := by
  induction j, hj using Nat.le_induction with
  | base => rw [triangle_card]; norm_num [rho]
  | succ j hj ih =>
    rw [pow_succ]
    apply le_trans _ (mul_le_mul_of_nonneg_right ih rho_pos.le)
    rw [triangle_card, triangle_card]
    push_cast
    have hj' : (4 : ℝ) ≤ j := by exact_mod_cast hj
    unfold rho
    nlinarith [sq_nonneg ((j : ℝ)-4)]

/-- Count a sequence on (1,ldots,b-1) recorded in reflected pairs.
The count of a middle singleton is overestimated by a whole pair. -/
private theorem reflected_count (F : Finset (ℕ → ℕ)) (b j : ℕ) (hj : 4 ≤ j)
    (hzero : ∀ A ∈ F, ∀ i, ¬(0 < i ∧ i < b) → A i = 0)
    (hpair : ∀ A ∈ F, ∀ i, 0 < i → i < b → A i + A (b-i) ≤ j) :
    (F.card : ℝ) ^ 2 ≤ rho ^ (j*b) := by
  let I := Icc 1 (b/2)
  have hcount := card_le_prod_of_coordinates F I (fun _ => triangle j)
    (fun A i => (A i,A (b-i)))
    (by
      intro A hA i hi
      have h := Finset.mem_Icc.mp hi
      exact mem_triangle.mpr (hpair A hA i (by omega) (by omega)))
    (by
      intro A hA B hB eq
      funext i
      by_cases hi : 0 < i ∧ i < b
      · by_cases hl : i ≤ b/2
        · exact congrArg Prod.fst (eq i (Finset.mem_Icc.mpr ⟨hi.1,hl⟩))
        · have hrev : b-i ∈ I := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have h := congrArg Prod.snd (eq (b-i) hrev)
          change A (b-(b-i)) = B (b-(b-i)) at h
          rwa [show b-(b-i)=i by omega] at h
      · rw [hzero A hA i hi, hzero B hB i hi])
  rw [Finset.prod_const] at hcount
  have hcardI : I.card = b/2 := by simp [I, Nat.card_Icc]
  have hcast : (F.card : ℝ) ≤ ((triangle j).card : ℝ)^I.card := by exact_mod_cast hcount
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (triangle j).card)
    (triangle_bound hj) I.card
  calc
    (F.card : ℝ)^2 ≤ ((rho^j)^I.card)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hcast.trans hpow) _
    _ = rho^(j*(I.card*2)) := by rw [← pow_mul, ← pow_mul]
    _ ≤ _ := pow_le_pow_right₀ rho_gt_one.le (Nat.mul_le_mul_left _ (by rw [hcardI]; omega))

private theorem threshold_exists (f m : ℕ) (hm : 0 < m) (A : Finset ℕ) (i : ℕ) :
    ∃ k, k*m+i ∈ expand f A := by
  refine ⟨f+1, Or.inr (Or.inr ?_)⟩
  have h := Nat.mul_le_mul_left (f+1) (show 1 ≤ m by omega)
  simp only [Nat.mul_one] at h
  omega

private noncomputable def threshold (f m : ℕ) (hm : 0 < m) (A : Finset ℕ) (i : ℕ) : ℕ :=
  by classical exact Nat.find (threshold_exists f m hm A i)

private theorem threshold_mem (f m : ℕ) (hm : 0 < m) (A : Finset ℕ) (i : ℕ) :
    threshold f m hm A i * m + i ∈ expand f A :=
  by classical exact Nat.find_spec (threshold_exists f m hm A i)

private theorem threshold_min {f m : ℕ} {hm : 0 < m} {A : Finset ℕ} {i k : ℕ}
    (hk : k*m+i ∈ expand f A) : threshold f m hm A i ≤ k :=
  by classical exact Nat.find_min' (threshold_exists f m hm A i) hk

private theorem mult_mem_expand {f m : ℕ} {A : Finset ℕ}
    (hA : A ∈ atMult f m) (hmf : m ≤ f) (hf : 0 < f) (k : ℕ) :
    k*m ∈ expand f A := by
  have hs := (expand_mem_all hf (mem_atMult.mp hA).1).1
  induction k with
  | zero => simpa using hs.1
  | succ k ih =>
    rw [Nat.succ_mul]
    exact hs.2.1 _ ih _ (Or.inr (Or.inl (mult_mem hA hmf)))

private theorem mem_of_threshold_le {f m : ℕ} {hm : 0 < m} {A : Finset ℕ} {i k : ℕ}
    (hA : A ∈ atMult f m) (hmf : m ≤ f) (hf : 0 < f)
    (hk : threshold f m hm A i ≤ k) : k*m+i ∈ expand f A := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  rw [hd, Nat.add_mul, Nat.add_right_comm]
  exact (expand_mem_all hf (mem_atMult.mp hA).1).1.2.1
    _ (threshold_mem f m hm A i) _ (mult_mem_expand hA hmf hf d)

/-- Backelin's residue-class bound with a triangular majorant. -/
theorem small_count {f m : ℕ} (hm : 0 < m) (hsmall : 4*m ≤ f) :
    ((atMult f m).card : ℝ)^2 ≤ rho^f := by
  classical
  let n := f/m
  let r := f%m
  have hmF : m ≤ f := by omega
  have hf : 0 < f := by omega
  have hn : 4 ≤ n := (Nat.le_div_iff_mul_le hm).mpr hsmall
  have hrm : r < m := Nat.mod_lt _ hm
  have hfr : n*m+r = f := by
    simpa only [n, r, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div f m
  by_cases hr : r = 0
  · have hd := Nat.dvd_of_mod_eq_zero hr
    rw [atMult_eq_empty_of_dvd hmF hd]
    simp only [Finset.card_empty, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0)]
    exact pow_nonneg rho_pos.le _
  have hrp : 0 < r := by omega
  let θ (A : Finset ℕ) (i : ℕ) := threshold f m hm A i
  have hLo {A : Finset ℕ} {i : ℕ} (h : i < r) :
      θ A i ≤ n+1 := by
    apply threshold_min
    refine Or.inr (Or.inr ?_)
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hHi {A : Finset ℕ} {i : ℕ} (h : r < i) :
      θ A i ≤ n := threshold_min (Or.inr (Or.inr (by omega)))
  have hsum {A : Finset ℕ} (hA : A ∈ atMult f m) {i j k : ℕ}
      (he : k*m+i+j = f) : k < θ A i + θ A j := by
    by_contra! h
    let b := θ A j
    have hsum : (k-b)*m+i + (b*m+j) ∈ expand f A := by
      apply (expand_mem_all hf (mem_atMult.mp hA).1).1.2.1
      · apply mem_of_threshold_le (hm := hm) hA hmF hf
        change θ A i ≤ k-b
        dsimp only [b]
        omega
      · exact threshold_mem f m hm A j
    have hk : k-b+b = k := by omega
    have heq : (k-b)*m+i + (b*m+j) = f := by
      calc
        _ = (k-b+b)*m+i+j := by rw [Nat.add_mul]; ac_rfl
        _ = f := by rw [hk, he]
    exact (expand_mem_all hf (mem_atMult.mp hA).1).2.1 (heq ▸ hsum)
  let lo (A : Finset ℕ) (i : ℕ) := if 0 < i ∧ i < r then n+1 - θ A i else 0
  let hi (A : Finset ℕ) (i : ℕ) := if 0 < i ∧ i < m-r then n - θ A (r+i) else 0
  let F := atMult f m
  let L := F.image lo
  let H := F.image hi
  have hL : (L.card : ℝ)^2 ≤ rho^((n+1)*r) :=
    reflected_count L r (n+1) (by omega)
      (by
        intro code hc i hn
        obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hc
        simp [lo, hn])
      (by
        intro code hc i hp ht
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hc
        have jcond : 0 < r-i ∧ r-i < r := by omega
        simp only [lo, ite_eq_left (show _ ∧ _ from ⟨hp,ht⟩), ite_eq_left jcond]
        have he : n*m+i+(r-i)=f := by omega
        have t := hsum hA he
        have := hLo (A := A) ht
        have := hLo (A := A) jcond.2
        omega)
  have hH : (H.card : ℝ)^2 ≤ rho^(n*(m-r)) :=
    reflected_count H (m-r) n hn
      (by
        intro code hc i hn
        obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hc
        simp [hi, hn])
      (by
        intro code hc i hp ht
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hc
        have jcond : 0 < m-r-i ∧ m-r-i < m-r := by omega
        simp only [hi, ite_eq_left (show _ ∧ _ from ⟨hp,ht⟩), ite_eq_left jcond]
        have hnm : (n-1)*m + m = n*m := by
          rw [← Nat.add_one_mul, show n-1+1=n by omega]
        have he : (n-1)*m+(r+i)+(r+(m-r-i))=f := by omega
        have t := hsum hA he
        have := hHi (A := A) (i := r+i) (by omega)
        have := hHi (A := A) (i := r+(m-r-i)) (by omega)
        omega)
  have hProd : F.card ≤ L.card * H.card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun A => (lo A, hi A))
    · intro A hA
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hA, Finset.mem_image_of_mem _ hA⟩
    · intro A hA B hB he
      have heL := congrArg Prod.fst he
      have heH := congrArg Prod.snd he
      change lo A = lo B at heL
      change hi A = hi B at heH
      apply (expand_injOn f) (mem_atMult.mp hA).1 (mem_atMult.mp hB).1
      ext x
      let i := x%m
      let k := x/m
      have hex : k*m+i = x := by
        simpa only [i,k,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div x m
      have hiM : i < m := Nat.mod_lt _ hm
      rw [← hex]
      by_cases hi0 : i = 0
      · rw [hi0, Nat.add_zero]
        exact iff_of_true (mult_mem_expand hA hmF hf k) (mult_mem_expand hB hmF hf k)
      by_cases hir : i = r
      · rw [hir]
        have hrule {C : Finset ℕ} (hC : C ∈ F) :
            k*m+r ∈ expand f C ↔ n < k := by
          constructor
          · intro h
            by_contra! hle
            have heq : k*m+r+(n-k)*m = f := by
              rw [Nat.add_right_comm, ← Nat.add_mul, Nat.add_sub_of_le hle, hfr]
            have hS := expand_mem_all hf (mem_atMult.mp hC).1
            exact hS.2.1 (heq ▸ hS.1.2.1 _ h _ (mult_mem_expand hC hmF hf (n-k)))
          · intro h
            have hmul := Nat.mul_lt_mul_of_pos_right h hm
            exact Or.inr (Or.inr (by omega))
        exact (hrule hA).trans (hrule hB).symm
      have ht : θ A i = θ B i := by
        by_cases hip : i < r
        · have h := congrFun heL i
          simp only [lo, ite_eq_left (show 0 < i ∧ i < r by omega)] at h
          have := hLo (A := A) hip
          have := hLo (A := B) hip
          omega
        · have h := congrFun heH (i-r)
          simp only [hi, ite_eq_left (show 0 < i-r ∧ i-r < m-r by omega),
            show r+(i-r)=i by omega] at h
          have := hHi (A := A) (i := i) (by omega)
          have := hHi (A := B) (i := i) (by omega)
          omega
      constructor
      · intro h
        apply mem_of_threshold_le hB hmF hf
        change θ B i ≤ k
        rw [← ht]
        exact threshold_min h
      · intro h
        apply mem_of_threshold_le hA hmF hf
        change θ A i ≤ k
        rw [ht]
        exact threshold_min h
  have hcast : (F.card : ℝ) ≤ (L.card : ℝ)*(H.card : ℝ) := by exact_mod_cast hProd
  calc
    (F.card : ℝ)^2 ≤ ((L.card : ℝ)*(H.card : ℝ))^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcast _
    _ ≤ rho^((n+1)*r) * rho^(n*(m-r)) := by
      rw [mul_pow]
      exact mul_le_mul hL hH (by positivity) (pow_nonneg rho_pos.le _)
    _ = rho^f := by
      rw [← pow_add, Nat.add_mul, Nat.one_mul,
        show n*r+r+n*(m-r)=n*m+r by
          rw [Nat.add_right_comm, ← Nat.mul_add, Nat.add_sub_of_le hrm.le], hfr]

end Singhal
```

### `SinghalConcentration.lean`

```lean
import SinghalMedium
import SinghalResidues
import Mathlib.Analysis.SpecificLimits.Normed

open Finset Filter
open scoped BigOperators Topology

namespace Singhal

def cutoff (f : ℕ) : ℕ := f/2 - f/40

def lowMult (f : ℕ) : Finset (Finset ℕ) :=
  (Sgs f).filter (fun A => multiplicity f A ≤ cutoff f)

theorem div_const_tendsto_atTop {c : ℕ} (hc : 0 < c) :
    Tendsto (fun f : ℕ => f/c) atTop atTop := by
  refine tendsto_atTop.mpr fun n => ?_
  filter_upwards [eventually_ge_atTop (n*c)] with f hf
  exact (Nat.le_div_iff_mul_le hc).mpr hf

theorem linear_mul_pow_tendsto_zero {c : ℕ} (hc : 0 < c)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun f : ℕ => (f : ℝ) * q^(f/c)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ)+1)*q^n) atTop (𝓝 0) := by
    simpa only [add_mul, one_mul, add_zero] using
      (tendsto_self_mul_const_pow_of_lt_one hq hq1).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1)
  have hupper : Tendsto (fun f : ℕ => (c:ℝ)*(((f/c : ℕ) : ℝ)+1)*q^(f/c))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_assoc, Function.comp_apply] using (hlim.comp (div_const_tendsto_atTop hc)).const_mul (c:ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => by positivity) fun f => ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  push_cast
  exact_mod_cast (Nat.lt_mul_div_succ f hc).le

private theorem small_count_linear {f m : ℕ} (hm : 0 < m) (hs : 4*m ≤ f) :
    ((atMult f m).card : ℝ) ≤ 2 * rho^((f-1)/2) := by
  let a := (f-1)/2
  have h : f ≤ 2*a+2 := by dsimp [a]; omega
  have hr := rho_pos
  apply le_of_sq_le_sq _ (by positivity : (0:ℝ) ≤ 2 * rho^a)
  calc
    ((atMult f m).card : ℝ)^2 ≤ rho^f := small_count hm hs
    _ ≤ rho^(2*a+2) := pow_le_pow_right₀ rho_gt_one.le h
    _ = rho^2 * (rho^a)^2 := by rw [pow_add, Nat.mul_comm 2 a, pow_mul, mul_comm]
    _ ≤ (2*rho^a)^2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ rho_pos.le rho_lt_two.le 2) (by positivity)

private theorem tail_card_bound {f : ℕ} (hf : 80 ≤ f) :
    ((lowMult f).card : ℝ) ≤
      (2:ℝ)^((f-1)/2) * ((f:ℝ)*(2*(rho/2)^(f/80) + (11/12)^(f/80))) := by
  let a := (f-1)/2
  have hr := rho_pos
  let q : ℝ := 2*(rho/2)^(f/80) + (11/12)^(f/80)
  have hB (m : ℕ) (hm : m ∈ Icc 1 (cutoff f)) :
      ((atMult f m).card : ℝ) ≤ (2:ℝ)^a*q := by
    have ⟨hm1,hm2⟩ := Finset.mem_Icc.mp hm
    have hpos : 0 < m := hm1
    have ha : f/80 ≤ a-m := by dsimp [a]; unfold cutoff at hm2; omega
    by_cases hs : 4*m ≤ f
    · apply (small_count_linear hpos hs).trans
      change 2*rho^a ≤ (2:ℝ)^a*q
      have hq : 2*(rho/2)^a ≤ q := by
        have hdec : (rho/2)^a ≤ (rho/2)^(f/80) :=
          pow_le_pow_of_le_one (by positivity) (by linarith [rho_lt_two]) (by omega)
        unfold q
        linarith [show (0:ℝ) ≤ (11/12)^(f/80) by positivity]
      calc
        2*rho^a = (2:ℝ)^a*(2*(rho/2)^a) := by rw [div_pow]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)
    · have hhi : 2*m < f := by unfold cutoff at hm2; omega
      apply (medium_count hpos (by omega) hhi).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hdec : (11/12 : ℝ)^(a-m) ≤ (11/12)^(f/80) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) ha
      unfold q
      linarith [show (0:ℝ) ≤ (rho/2)^(f/80) by positivity]
  have hb : ((lowMult f).card : ℝ) ≤ ∑ m ∈ Icc 1 (cutoff f), (2:ℝ)^a*q := by
    apply card_le_sum_of_coordinates _ _ (multiplicity f)
    · intro A hA
      obtain ⟨hA, hm⟩ := Finset.mem_filter.mp hA
      exact Finset.mem_Icc.mpr ⟨multiplicity_pos hA,hm⟩
    · intro m hm
      apply le_trans _ (hB m hm)
      exact_mod_cast (Finset.card_le_card (s := (lowMult f).filter
        (fun A => multiplicity f A = m)) (t := atMult f m)
        (fun A hA => mem_atMult.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1,
          (Finset.mem_filter.mp hA).2⟩))
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at hb
  apply hb.trans
  change ((cutoff f : ℕ) : ℝ) * ((2:ℝ)^a*q) ≤ (2:ℝ)^a*((f:ℝ)*q)
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (by exact_mod_cast (show cutoff f ≤ f by unfold cutoff; omega))
    (by dsimp [q]; positivity)) (by positivity)

/-- The one-sided multiplicity concentration needed for the toggle. -/
theorem lowMult_tendsto_zero :
    Tendsto (fun f : ℕ => ((lowMult f).card : ℝ) / (Sgs f).card) atTop (𝓝 0) := by
  have hr := rho_pos
  have hq : (0:ℝ) ≤ rho/2 := by positivity
  have hq1 : rho/2 < 1 := by linarith [rho_lt_two]
  have h1 := (linear_mul_pow_tendsto_zero (c := 80) (by decide) hq hq1).const_mul (2:ℝ)
  have h2 := linear_mul_pow_tendsto_zero (c := 80) (q := 11/12) (by decide) (by norm_num) (by norm_num)
  have hb : Tendsto (fun f : ℕ => (f:ℝ)*(2*(rho/2)^(f/80) + (11/12)^(f/80))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, mul_add, mul_left_comm] using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun f => by positivity) ?_
  filter_upwards [eventually_ge_atTop 80] with f hf
  have hp : (0:ℝ) < (Sgs f).card := by exact_mod_cast Finset.card_pos.mpr (sgs_nonempty f)
  rw [div_le_iff₀ hp]
  apply (tail_card_bound hf).trans
  have hden : (2:ℝ)^((f-1)/2) ≤ (Sgs f).card := by
    exact_mod_cast large_mult_lower_bound f
  rw [mul_comm _ ((Sgs f).card : ℝ)]
  exact mul_le_mul_of_nonneg_right hden (by positivity)

#print axioms lowMult_tendsto_zero

end Singhal
```

### `SinghalMatching.lean`

```lean
import SinghalConcentration

open Finset
open scoped BigOperators

namespace Singhal

/-- A greedy choice of disjoint pairs ((t,t+d)). Each chosen pair
removes at most three candidate tails. -/
theorem exists_disjoint_shift (d : ℕ) (hd : 0 < d) (T : Finset ℕ) :
    ∃ P ⊆ T, Disjoint P (P.image (·+d)) ∧ T.card ≤ 3*P.card := by
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
    by_cases h : T.Nonempty
    · obtain ⟨t, ht⟩ := h
      let B : Finset ℕ := {t, t+d, t-d}
      let R := T \ B
      have htB : t ∈ B := by simp [B]
      have hR : R ⊂ T := by
        refine lt_of_le_of_ne Finset.sdiff_subset ?_
        intro he
        exact (Finset.mem_sdiff.mp (show t ∈ R by rwa [he])).2 htB
      obtain ⟨P, hP, hDis, hcard⟩ := ih R hR
      have htP : t ∉ P := fun h => (Finset.mem_sdiff.mp (hP h)).2 htB
      refine ⟨insert t P, Finset.insert_subset ht (hP.trans Finset.sdiff_subset), ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro x hx hy
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
        rcases Finset.mem_insert.mp hx with he | hx
        · rcases Finset.mem_insert.mp hs with rfl | hs
          · omega
          · have hb := (Finset.mem_sdiff.mp (hP hs)).2
            apply hb
            have : s = t-d := by omega
            simp [B, this]
        · rcases Finset.mem_insert.mp hs with he | hs
          · subst s
            exact (Finset.mem_sdiff.mp (hP hx)).2 (by simp [B])
          · exact Finset.disjoint_left.mp hDis hx (Finset.mem_image_of_mem _ hs)
      · have hsub : T ⊆ R ∪ B := fun x hx => by
          by_cases hB : x ∈ B
          · exact Finset.mem_union_right _ hB
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx,hB⟩)
        have hb : B.card ≤ 3 := by
          calc
            _ ≤ ({t+d,t-d} : Finset ℕ).card+1 := Finset.card_insert_le _ _
            _ ≤ (({t-d} : Finset ℕ).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
            _ = 3 := by simp
        have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le R B)
        rw [Finset.card_insert_of_notMem htP]
        omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]
      exact ⟨∅, by simp⟩

def obeysShift (M : Finset ℕ) (x g : ℕ) (U : Finset ℕ) : Prop :=
  ∀ s ∈ M.erase x, s+g ∈ M.erase x → s ∈ U → s+g ∈ U

instance (M : Finset ℕ) (x g : ℕ) : DecidablePred (obeysShift M x g) :=
  fun U => by unfold obeysShift; infer_instance

theorem shift_count {l u x g p : ℕ} (hg : 0 < g) (hu : g ≤ u)
    (hp : 3*p+g+2 ≤ (Icc l u).card) :
    (((Icc l u).powerset.filter (obeysShift (Icc l u) x g)).card : ℝ) ≤
      (2 : ℝ)^(Icc l u).card*(3/4)^p := by
  classical
  let M := Icc l u
  let S := ((Icc l (u-g)).erase x).erase (x-g)
  let F := M.powerset.filter (obeysShift M x g)
  have hs : 3*p ≤ S.card := by
    have h1 := Finset.card_erase_le (s := Icc l (u-g)) (a := x)
    have h2 : (Icc l (u-g)).card ≤ ((Icc l (u-g)).erase x).card+1 := by
      by_cases h : x ∈ Icc l (u-g)
      · rw [Finset.card_erase_of_mem h]; omega
      · rw [Finset.erase_eq_of_notMem h]; omega
    have h3 : ((Icc l (u-g)).erase x).card ≤ S.card+1 := by
      by_cases h : x-g ∈ (Icc l (u-g)).erase x
      · dsimp [S]; rw [Finset.card_erase_of_mem h]; omega
      · dsimp [S]; rw [Finset.erase_eq_of_notMem h]; omega
    rw [Nat.card_Icc] at hp h1 h2
    omega
  have hS {t : ℕ} (ht : t ∈ S) :
      t ∈ M.erase x ∧ t+g ∈ M.erase x := by
    obtain ⟨hxg, h⟩ := Finset.mem_erase.mp ht
    obtain ⟨hx, ht'⟩ := Finset.mem_erase.mp h
    have hb := Finset.mem_Icc.mp ht'
    exact ⟨Finset.mem_erase.mpr ⟨hx, Finset.mem_Icc.mpr ⟨hb.1, by omega⟩⟩,
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩⟩
  obtain ⟨P, hP, hDis, hcard⟩ := exists_disjoint_shift g hg S
  have hpP : p ≤ P.card := by omega
  have h := card_le_of_disjoint_pairs F M P ∅ ∅ g (fun _ => none)
    (fun t ht => Finset.mem_of_mem_erase (hS (hP ht)).1)
    (by
      intro t ht
      obtain ⟨s, hs', rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_of_mem_erase (hS (hP hs')).2)
    hDis
    (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp)
    (fun _ h => Finset.mem_powerset.mp (Finset.mem_filter.mp h).1)
    (by simp [agrees])
    (fun U hU t ht => (Finset.mem_filter.mp hU).2 t (hS (hP ht)).1 (hS (hP ht)).2)
  simp only [Finset.card_empty, pow_zero, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hpP) (by positivity))

end Singhal
```

### `SinghalToggle.lean`

```lean
import SinghalMatching

open Finset

namespace Singhal

def blockLo (f : ℕ) : ℕ := f/2 + f/40 + 1
def blockHi (f : ℕ) : ℕ := f - 2*(f/40)
def block (f : ℕ) : Finset ℕ := Icc (blockLo f) (blockHi f)
def pivot (f : ℕ) : ℕ := 3*f/4
def gapMax (f : ℕ) : ℕ := max (f-pivot f) (pivot f-cutoff f-1)

def good (f : ℕ) : Finset (Finset ℕ) :=
  (Sgs f).filter (fun A => cutoff f < multiplicity f A)

theorem mem_good {f : ℕ} {A : Finset ℕ} :
    A ∈ good f ↔ A ∈ Sgs f ∧ ∀ s ∈ A, cutoff f < s := by
  rw [good, Finset.mem_filter]
  constructor
  · intro ⟨ha, hm⟩
    exact ⟨ha, fun _ hs => hm.trans_le (multiplicity_le hs)⟩
  · intro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    by_contra! hm
    have hcut : cutoff f ≤ f := by unfold cutoff; omega
    exact Nat.not_lt_of_ge hm (h _ (multiplicity_mem (hm.trans hcut)))

theorem block_pos_lt {f y : ℕ} (hf : 80 ≤ f) (hy : y ∈ block f) :
    0 < y ∧ y < f := by
  have h := Finset.mem_Icc.mp hy
  unfold blockLo blockHi at h
  omega

theorem block_above_cutoff {f y : ℕ} (hy : y ∈ block f) : cutoff f < y := by
  have h := (Finset.mem_Icc.mp hy).1
  unfold blockLo at h
  unfold cutoff
  omega

theorem block_add {f y s : ℕ} (hy : y ∈ block f) (hs : cutoff f < s) :
    f < y+s := by
  have h := (Finset.mem_Icc.mp hy).1
  unfold blockLo at h
  unfold cutoff at hs
  omega

theorem add_not_block {f a b : ℕ} (ha : cutoff f < a) (hb : cutoff f < b) :
    a+b ∉ block f := by
  intro h
  have hl := (Finset.mem_Icc.mp h).2
  unfold blockHi at hl
  unfold cutoff at ha hb
  omega

theorem pivot_mem {f : ℕ} (hf : 80 ≤ f) : pivot f ∈ block f := by
  unfold block blockLo blockHi pivot
  apply Finset.mem_Icc.mpr
  omega

/-- The difference of the two floors is at most ((f+1)/4). -/
theorem pivot_floor (f : ℕ) : 4*pivot f ≤ 4*(f/2)+f+1 := by
  unfold pivot
  have hm : f % 4 = 0 ∨ f % 4 = 1 ∨ f % 4 = 2 ∨ f % 4 = 3 := by omega
  rcases hm with h | h | h | h <;> omega

theorem gapMax_bound {f : ℕ} (hf : 80 ≤ f) : gapMax f ≤ f/4+f/40+1 := by
  have hp := pivot_floor f
  unfold gapMax cutoff
  apply max_le
  · unfold pivot; omega
  · omega

theorem block_matching_range {f g : ℕ} (hf : 80 ≤ f) (hg : g ≤ gapMax f) :
    g ≤ blockHi f ∧ 3*(f/80)+g+2 ≤ (block f).card := by
  have hb := gapMax_bound hf
  unfold block blockLo blockHi
  rw [Nat.card_Icc]
  omega

theorem replace_block {f : ℕ} (hf : 80 ≤ f) {A U : Finset ℕ}
    (hA : A ∈ good f) (hU : U ⊆ block f) : (A \ block f) ∪ U ∈ good f := by
  obtain ⟨ha, hlo⟩ := mem_good.mp hA
  have hmin {s : ℕ} (hs : s ∈ (A \ block f) ∪ U) : cutoff f < s := by
    rcases Finset.mem_union.mp hs with hs | hs
    · exact hlo s (Finset.mem_sdiff.mp hs).1
    · exact block_above_cutoff (hU hs)
  refine mem_good.mpr ⟨mem_sgs.mpr ⟨?_, ?_⟩, fun _ hs => hmin hs⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact (mem_sgs.mp ha).1 (Finset.mem_sdiff.mp hs).1
    · exact Finset.mem_Ioo.mpr (block_pos_lt hf (hU hs))
  · intro a ha' b hb'
    have hac := hmin ha'
    have hbc := hmin hb'
    by_cases hbig : f < a+b
    · omega
    have hna : a ∉ U := fun h => hbig (block_add (hU h) hbc)
    have hnb : b ∉ U := fun h => hbig (by rw [Nat.add_comm]; exact block_add (hU h) hac)
    have ham := (Finset.mem_sdiff.mp ((Finset.mem_union.mp ha').resolve_right hna)).1
    have hbm := (Finset.mem_sdiff.mp ((Finset.mem_union.mp hb').resolve_right hnb)).1
    exact ⟨sum_ne_f ha ham hbm, fun h => Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨sum_mem_enc ha ham hbm h, add_not_block hac hbc⟩)⟩

noncomputable def badPatterns (f : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (block f).powerset.filter fun U =>
    ∃ g ∈ Icc 1 (gapMax f), obeysShift (block f) (pivot f) g U

theorem mem_badPatterns {f : ℕ} {U : Finset ℕ} :
    U ∈ badPatterns f ↔ U ⊆ block f ∧
      ∃ g ∈ Icc 1 (gapMax f), obeysShift (block f) (pivot f) g U := by
  classical simp [badPatterns]

def toggle (x : ℕ) (A : Finset ℕ) : Finset ℕ :=
  if x ∈ A then A.erase x else insert x A

theorem toggle_mem_of_ne {x y : ℕ} {A : Finset ℕ} (h : y ≠ x) :
    y ∈ toggle x A ↔ y ∈ A := by
  unfold toggle
  split <;> simp [h]

theorem toggle_involutive (x : ℕ) : Function.Involutive (toggle x) := by
  intro A
  by_cases h : x ∈ A
  · have hn : x ∉ A.erase x := Finset.notMem_erase _ _
    simp only [toggle, ite_eq_left h, ite_eq_right hn]
    exact Finset.insert_erase h
  · have hm : x ∈ insert x A := Finset.mem_insert_self _ _
    simp only [toggle, ite_eq_right h, ite_eq_left hm]
    exact Finset.erase_insert h

theorem toggle_mem_good {f : ℕ} (hf : 80 ≤ f) {A : Finset ℕ} (hA : A ∈ good f) :
    toggle (pivot f) A ∈ good f := by
  have hsub : toggle (pivot f) A ∩ block f ⊆ block f := Finset.inter_subset_right
  convert replace_block hf hA hsub using 1
  ext y
  by_cases hy : y ∈ block f
  · simp [hy]
  · have hne : y ≠ pivot f := fun he => hy (he.symm ▸ pivot_mem hf)
    simp [hy, toggle_mem_of_ne hne]

theorem toggle_bad_iff {f : ℕ} {A : Finset ℕ} :
    toggle (pivot f) A ∩ block f ∈ badPatterns f ↔ A ∩ block f ∈ badPatterns f := by
  rw [mem_badPatterns, mem_badPatterns]
  simp only [Finset.inter_subset_right, true_and]
  constructor <;> rintro ⟨g, hg, h⟩ <;> refine ⟨g, hg, ?_⟩
  all_goals
    intro s hs hs'
    have h1 := toggle_mem_of_ne (A := A) (Finset.mem_erase.mp hs).1
    have h2 := toggle_mem_of_ne (A := A) (Finset.mem_erase.mp hs').1
    simpa only [Finset.mem_inter, h1, h2] using h s hs hs'

theorem bad_of_low_pf {f g : ℕ} (hf : 80 ≤ f) {A : Finset ℕ}
    (hg : g ∈ Icc 1 (gapMax f)) (hp : g ∈ PFenc f A) :
    A ∩ block f ∈ badPatterns f := by
  refine mem_badPatterns.mpr ⟨Finset.inter_subset_right, ⟨g,hg,?_⟩⟩
  intro s hs hs' ha
  obtain ⟨_, _, hp⟩ := Finset.mem_filter.mp hp
  have hbl := Finset.mem_of_mem_erase hs'
  refine Finset.mem_inter.mpr ⟨?_, hbl⟩
  rcases hp s (Finset.mem_inter.mp ha).1 with h | h
  · rwa [Nat.add_comm]
  · have ht := (block_pos_lt hf hbl).2
    omega

private theorem mem_pfenc {f g : ℕ} {A : Finset ℕ} :
    g ∈ PFenc f A ↔ (1 ≤ g ∧ g ≤ f) ∧ g ∉ A ∧
      ∀ s ∈ A, g+s ∈ A ∨ f < g+s := by simp [PFenc]

theorem pf_insert_pivot {f : ℕ} (hf : 80 ≤ f) {A : Finset ℕ} (hA : A ∈ good f)
    (hxA : pivot f ∉ A) (hgood : A ∩ block f ∉ badPatterns f) :
    PFenc f A = insert (pivot f) (PFenc f (insert (pivot f) A)) := by
  let x := pivot f
  let B := insert x A
  have hx := pivot_mem hf
  have hh := block_pos_lt hf hx
  have hGA := (mem_good.mp hA).2
  have hTB : toggle x A = B := by unfold toggle; exact ite_eq_right hxA
  have hBG : B ∩ block f ∉ badPatterns f := by
    rw [← hTB]
    exact mt toggle_bad_iff.mp hgood
  have hxPF : x ∈ PFenc f A := mem_pfenc.mpr
    ⟨⟨hh.1, hh.2.le⟩, hxA, fun s hs => Or.inr (block_add hx (hGA s hs))⟩
  have hhigh {C : Finset ℕ} {g : ℕ} (hn : C ∩ block f ∉ badPatterns f)
      (hg : g ∈ PFenc f C) : gapMax f < g := by
    by_contra! h
    exact hn (bad_of_low_pf hf (Finset.mem_Icc.mpr ⟨(mem_pfenc.mp hg).1.1,h⟩) hg)
  ext g
  change g ∈ PFenc f A ↔ g ∈ insert x (PFenc f B)
  rw [Finset.mem_insert]
  constructor
  · intro hg
    by_cases he : g = x
    · exact Or.inl he
    · have hgH := hhigh hgood hg
      have hh₁ : f-x < g := (le_max_left _ _).trans_lt hgH
      obtain ⟨hgf, hgap, ht⟩ := mem_pfenc.mp hg
      refine Or.inr (mem_pfenc.mpr ⟨hgf, ?_, ?_⟩)
      · intro h
        exact (Finset.mem_insert.mp h).elim he hgap
      · intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact Or.inr (by omega)
        · exact (ht s hs).imp Finset.mem_insert_of_mem id
  · rintro (rfl | hg)
    · exact hxPF
    have hgH := hhigh hBG hg
    have hh₂ : x-cutoff f-1 < g := (le_max_right _ _).trans_lt hgH
    obtain ⟨hgf, hgap, ht⟩ := mem_pfenc.mp hg
    refine mem_pfenc.mpr ⟨hgf, fun h => hgap (Finset.mem_insert_of_mem h), ?_⟩
    intro s hs
    rcases ht s (Finset.mem_insert_of_mem hs) with h | h
    · rcases Finset.mem_insert.mp h with he | h
      · have hsm := hGA s hs
        omega
      · exact Or.inl h
    · exact Or.inr h

theorem type_insert_pivot {f : ℕ} (hf : 80 ≤ f) {A : Finset ℕ} (hA : A ∈ good f)
    (hxA : pivot f ∉ A) (hgood : A ∩ block f ∉ badPatterns f) :
    (PFenc f A).card = (PFenc f (insert (pivot f) A)).card + 1 := by
  rw [pf_insert_pivot hf hA hxA hgood, Finset.card_insert_of_notMem]
  exact fun h => (mem_pfenc.mp h).2.1 (Finset.mem_insert_self _ _)

end Singhal
```

### `SinghalParity.lean`

```lean
import SinghalToggle

open Finset Filter
open scoped BigOperators Topology

namespace Singhal

private def outside (f : ℕ) : Finset (Finset ℕ) := (good f).image (· \ block f)

private theorem fiber_card {f : ℕ} (hf : 80 ≤ f) (K : Finset (Finset ℕ))
    (hK : K ⊆ (block f).powerset) :
    ((good f).filter (fun A => A ∩ block f ∈ K)).card = (outside f).card*K.card := by
  rw [← Finset.card_product]
  apply Finset.card_nbij (fun A => (A \ block f, A ∩ block f))
  · intro A hA
    obtain ⟨hA, hk⟩ := Finset.mem_filter.mp hA
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hA,hk⟩
  · intro A _ B _ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change A \ block f = B \ block f at h₁
    change A ∩ block f = B ∩ block f at h₂
    rw [← Finset.sdiff_union_inter A (block f), h₁, h₂, Finset.sdiff_union_inter]
  · rintro ⟨D,U⟩ h
    obtain ⟨hD,hU⟩ := Finset.mem_product.mp h
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hD
    have hu := Finset.mem_powerset.mp (hK hU)
    have h₁ : ((A \ block f) ∪ U) \ block f = A \ block f := by
      ext x
      by_cases hx : x ∈ block f
      · simp [hx]
      · have hxu : x ∉ U := fun h => hx (hu h)
        simp [hx, hxu]
    have h₂ : ((A \ block f) ∪ U) ∩ block f = U := by
      ext x
      by_cases hx : x ∈ block f
      · simp [hx]
      · have hxu : x ∉ U := fun h => hx (hu h)
        simp [hx, hxu]
    exact ⟨(A \ block f) ∪ U,
      Finset.mem_filter.mpr ⟨replace_block hf hA hu, h₂.symm ▸ hU⟩, Prod.ext h₁ h₂⟩

private theorem good_card {f : ℕ} (hf : 80 ≤ f) :
    (good f).card = (outside f).card * 2^(block f).card := by
  have h := fiber_card hf (block f).powerset (by rfl)
  rw [Finset.filter_true_of_mem, Finset.card_powerset] at h
  · exact h
  · intro A _
    exact Finset.mem_powerset.mpr Finset.inter_subset_right

private theorem badPatterns_bound {f : ℕ} (hf : 80 ≤ f) :
    ((badPatterns f).card : ℝ) ≤ (2:ℝ)^(block f).card * ((f:ℝ)*(3/4)^(f/80)) := by
  classical
  let I := Icc 1 (gapMax f)
  let sets (g : ℕ) := (block f).powerset.filter (obeysShift (block f) (pivot f) g)
  have he : badPatterns f = I.biUnion sets := by
    ext U
    rw [mem_badPatterns, Finset.mem_biUnion]
    simp only [sets, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hU,g,hg,hs⟩
      exact ⟨g,hg,hU,hs⟩
    · rintro ⟨g,hg,hU,hs⟩
      exact ⟨hU,g,hg,hs⟩
  rw [he]
  have hsum : ((I.biUnion sets).card : ℝ) ≤ ∑ g ∈ I, ((sets g).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := I) (t := sets))
  apply hsum.trans
  have hc (g : ℕ) (hg : g ∈ I) :
      ((sets g).card : ℝ) ≤ (2:ℝ)^(block f).card*(3/4)^(f/80) := by
    have hg' := Finset.mem_Icc.mp hg
    have hb := block_matching_range hf hg'.2
    exact shift_count hg'.1 hb.1 hb.2
  apply (Finset.sum_le_sum hc).trans
  rw [Finset.sum_const, nsmul_eq_mul]
  have hI : I.card ≤ f := by
    have h := gapMax_bound hf
    dsimp [I]
    rw [Nat.card_Icc]
    omega
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (by positivity)) (by positivity)

private noncomputable def bad (f : ℕ) : Finset (Finset ℕ) :=
  (good f).filter fun A => A ∩ block f ∈ badPatterns f

private noncomputable def great (f : ℕ) : Finset (Finset ℕ) :=
  (good f).filter fun A => A ∩ block f ∉ badPatterns f

private theorem bad_card_bound {f : ℕ} (hf : 80 ≤ f) :
    ((bad f).card : ℝ) ≤ (Sgs f).card * ((f:ℝ)*(3/4)^(f/80)) := by
  have h := fiber_card hf (badPatterns f) (fun _ h => Finset.mem_powerset.mpr (mem_badPatterns.mp h).1)
  change (bad f).card = _ at h
  rw [h, Nat.cast_mul]
  have hG : ((good f).card : ℝ) ≤ (Sgs f).card := by
    exact_mod_cast (Finset.card_filter_le (Sgs f) (fun A => cutoff f < multiplicity f A))
  calc
    _ ≤ (outside f).card * ((2:ℝ)^(block f).card * ((f:ℝ)*(3/4)^(f/80))) :=
      mul_le_mul_of_nonneg_left (badPatterns_bound hf) (by positivity)
    _ = (good f).card * ((f:ℝ)*(3/4)^(f/80)) := by
      rw [good_card hf]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hG (by positivity)

private noncomputable def sign (f : ℕ) (A : Finset ℕ) : ℝ :=
  if (PFenc f A).card % 2 = f % 2 then 1 else -1

private theorem abs_sign (f : ℕ) (A : Finset ℕ) : |sign f A| = 1 := by
  unfold sign
  split <;> norm_num

private theorem sign_pair {f : ℕ} (hf : 80 ≤ f) {A : Finset ℕ} (hA : A ∈ great f) :
    sign f A + sign f (toggle (pivot f) A) = 0 := by
  have hI := toggle_involutive (pivot f) A
  let x := pivot f
  let B := toggle x A
  have hflip {C : Finset ℕ} (hC : C ∈ good f) (hx : x ∉ C)
      (hgood : C ∩ block f ∉ badPatterns f) :
      sign f C + sign f (toggle x C) = 0 := by
    have hp := type_insert_pivot hf hC hx hgood
    have ht : toggle x C = insert x C := by simp [toggle, hx]
    rw [ht]
    unfold sign
    dsimp [x] at hp ⊢
    split <;> split <;> (try norm_num) <;> omega
  obtain ⟨hg,hn⟩ := Finset.mem_filter.mp hA
  by_cases hx : x ∈ A
  · have hnB : x ∉ B := by simp [B, toggle, hx]
    have he := hflip (toggle_mem_good hf hg) hnB (mt toggle_bad_iff.mp hn)
    change sign f B + sign f (toggle x B) = 0 at he
    rw [show toggle x B = A from hI, add_comm] at he
    exact he
  · exact hflip hg hx hn

private theorem great_cancel {f : ℕ} (hf : 80 ≤ f) :
    ∑ A ∈ great f, sign f A = 0 := by
  refine Finset.sum_involution (fun A _ => toggle (pivot f) A) (fun A ha => sign_pair hf ha) ?_ ?_ ?_
  · intro A _ _ h
    by_cases hx : pivot f ∈ A
    · have hn : pivot f ∉ toggle (pivot f) A := by simp [toggle, hx]
      exact hn (h.symm ▸ hx)
    · have hm : pivot f ∈ toggle (pivot f) A := by simp [toggle, hx]
      exact hx (h ▸ hm)
  · intro A hA
    obtain ⟨hg, hb⟩ := Finset.mem_filter.mp hA
    exact Finset.mem_filter.mpr ⟨toggle_mem_good hf hg, mt toggle_bad_iff.mp hb⟩
  · intro A _
    exact toggle_involutive _ A

private theorem abs_sign_sum_le (f : ℕ) (X : Finset (Finset ℕ)) :
    |∑ A ∈ X, sign f A| ≤ X.card := by
  simpa only [abs_sign, Finset.sum_const, nsmul_eq_mul, mul_one] using
    (Finset.abs_sum_le_sum_abs (fun A => sign f A) X)

private theorem sign_sum_eq (f : ℕ) :
    ∑ A ∈ Sgs f, sign f A = 2*(SameEnc f).card - (Sgs f).card := by
  have h (A : Finset ℕ) :
      sign f A = (2:ℝ)*(if (PFenc f A).card % 2 = f % 2 then 1 else 0) - 1 := by
    unfold sign
    split <;> norm_num
  simp_rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, nsmul_eq_mul, mul_one, SameEnc]

private theorem imbalance_bound {f : ℕ} (hf : 80 ≤ f) :
    |(2:ℝ)*(SameEnc f).card - (Sgs f).card| ≤
      ((lowMult f).card : ℝ) + (Sgs f).card*((f:ℝ)*(3/4)^(f/80)) := by
  have hsplit₁ : (∑ A ∈ lowMult f, sign f A) + (∑ A ∈ good f, sign f A) =
      ∑ A ∈ Sgs f, sign f A := by
    simpa only [lowMult, good, not_le] using
      Finset.sum_filter_add_sum_filter_not (Sgs f) (fun A => multiplicity f A ≤ cutoff f) (sign f)
  have hsplit₂ : (∑ A ∈ bad f, sign f A) + (∑ A ∈ great f, sign f A) =
      ∑ A ∈ good f, sign f A :=
    Finset.sum_filter_add_sum_filter_not (good f) (fun A => A ∩ block f ∈ badPatterns f) (sign f)
  rw [great_cancel hf, add_zero] at hsplit₂
  rw [← sign_sum_eq, ← hsplit₁, ← hsplit₂]
  exact (abs_add_le _ _).trans
    (add_le_add (abs_sign_sum_le _ _) ((abs_sign_sum_le _ _).trans (bad_card_bound hf)))

theorem singhal_7_2_encoded :
    Tendsto (fun f : ℕ => ((SameEnc f).card : ℝ) / ((Sgs f).card : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have hgeom := linear_mul_pow_tendsto_zero (c := 80) (q := 3/4)
    (by decide) (by norm_num) (by norm_num)
  have hlim :
      Tendsto (fun f : ℕ => (((lowMult f).card : ℝ)/(Sgs f).card + (f:ℝ)*(3/4)^(f/80))/2)
        atTop (𝓝 0) := by
    simpa only [add_zero, zero_div] using (lowMult_tendsto_zero.add hgeom).div_const (2:ℝ)
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun f => dist_nonneg) ?_
  filter_upwards [eventually_ge_atTop 80] with f hf
  have hp : (0:ℝ) < (Sgs f).card := by exact_mod_cast Finset.card_pos.mpr (sgs_nonempty f)
  have he : ((SameEnc f).card : ℝ) / (Sgs f).card - 1/2 =
      (2*(SameEnc f).card - (Sgs f).card)/(2*(Sgs f).card) := by field_simp
  rw [Real.dist_eq, he, abs_div, abs_of_pos (by positivity : 0 < 2*((Sgs f).card : ℝ)),
      div_le_iff₀ (by positivity : 0 < 2*((Sgs f).card : ℝ))]
  apply (imbalance_bound hf).trans_eq
  field_simp

/-- Deepesh Singhal, Conjecture 7.2, with all numerical semigroups in the denominator. -/
theorem singhal_7_2 :
    Tendsto (fun f : ℕ => ((Same f).ncard : ℝ) / ((All f).ncard : ℝ))
      atTop (𝓝 (1 / 2)) := by
  refine singhal_7_2_encoded.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with f hf
  have hp : 0 < f := hf
  rw [same_ncard hp, all_ncard hp]

#check singhal_7_2
#check singhal_7_2_encoded
#print axioms singhal_7_2
#print axioms singhal_7_2_encoded

end Singhal
```
