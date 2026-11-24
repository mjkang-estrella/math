# Lean source appendix

Modules appear in import order. The fenced sources are byte-identical to the files in the certificate.

### `GarbeGrowth.lean`

```lean
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Subadditive
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Relation

namespace Garbe
open Polynomial Finset Filter
open scoped Topology
noncomputable section

abbrev P2 := Polynomial (ZMod 2)

def r (f : P2) (N : ℕ) : ℕ := ∑ n ∈ range N, (f ^ n).support.card

def HasGrowthRate (f : P2) (rate : ℝ) : Prop :=
  Tendsto (fun k : ℕ => (r f (2 ^ k) : ℝ) ^ ((1 : ℝ) / k)) atTop (𝓝 rate)

inductive SimStep : P2 → P2 → Prop
  | shift (f) (c : ℕ) (hc : 0 < c) : SimStep f (X ^ c * f)
  | dil (f) (c : ℕ) (hc : 1 < c) : SimStep f (f.comp (X ^ c))
  | rev (f) : SimStep f f.reverse
  | pow (f) (c : ℕ) (hc : 1 < c) : SimStep f (f ^ c)

def Similar (f g : P2) : Prop := Relation.EqvGen SimStep f g

abbrev w (f : P2) : ℕ := f.support.card
@[simp] theorem weight_one : w (1 : P2) = 1 := by
  simpa only [pow_zero] using (show (X ^ (0 : ℕ) : P2).support.card = 1 by rw [support_X_pow, card_singleton])

@[simp] theorem weight_X_pow (n : ℕ) : w (X ^ n : P2) = 1 := by
  change (X ^ n : P2).support.card = 1
  rw [support_X_pow, card_singleton]

theorem weight_shift (g : P2) (c : ℕ) : w (X ^ c * g) = w g := by
  have hs : (X ^ c * g).support = g.support.image (fun i => i + c) := by
    ext n
    rw [mem_support_iff, coeff_X_pow_mul', mem_image]
    by_cases h : c ≤ n
    · rw [ite_eq_left h]
      constructor
      · intro hn
        exact ⟨n - c, mem_support_iff.mpr hn, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        simpa using mem_support_iff.mp hi
    · simp only [ite_eq_right h, ne_eq, not_true_eq_false, false_iff]
      rintro ⟨i, _, rfl⟩
      omega
  change (X ^ c * g).support.card = g.support.card
  rw [hs, card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)]

theorem weight_expand (g : P2) {c : ℕ} (hc : 0 < c) : w (expand (ZMod 2) c g) = w g := by
  have hs : (expand (ZMod 2) c g).support = g.support.image (fun i => i * c) := by
    ext n
    rw [mem_support_iff, coeff_expand hc, mem_image]
    by_cases h : c ∣ n
    · rw [ite_eq_left h]
      constructor
      · intro hn
        exact ⟨n / c, mem_support_iff.mpr hn, Nat.div_mul_cancel h⟩
      · rintro ⟨i, hi, rfl⟩
        simpa [Nat.mul_div_cancel _ hc] using mem_support_iff.mp hi
    · simp only [ite_eq_right h, ne_eq, not_true_eq_false, false_iff]
      rintro ⟨i, _, rfl⟩
      exact h (dvd_mul_left _ _)
  change (expand (ZMod 2) c g).support.card = g.support.card
  rw [hs, card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_right hc h)]

theorem weight_reverse (f : P2) : w f.reverse = w f := by
  change (reflect f.natDegree f).support.card = f.support.card
  rw [reflect_support, card_image_of_injective _ (revAt f.natDegree).injective]

theorem reverse_pow (f : P2) (n : ℕ) : (f ^ n).reverse = f.reverse ^ n := by
  induction n with
  | zero => simpa only [C_1, pow_zero] using (reverse_C (1 : ZMod 2))
  | succ n ih => rw [pow_succ, reverse_mul_of_domain, ih, pow_succ]

theorem frobenius_map_eq (g : P2) (n : ℕ) :
    g.map (iterateFrobenius (ZMod 2) 2 n) = g := by
  ext i
  rw [coeff_map]
  have h : ∀ a : ZMod 2, iterateFrobenius (ZMod 2) 2 n a = a := by
    intro a
    fin_cases a
    · exact map_zero _
    · exact map_one _
  exact h _

theorem dyadic_pow (g : P2) (n : ℕ) : g ^ (2 ^ n) = expand (ZMod 2) (2 ^ n) g := by
  rw [← map_iterateFrobenius_expand 2 g n, frobenius_map_eq]

theorem weight_dyadic_pow (g : P2) (n : ℕ) : w (g ^ (2 ^ n)) = w g := by
  rw [dyadic_pow, weight_expand _ (by positivity)]

theorem sum_blocks (a b : ℕ) (F : ℕ → ℕ) :
    (∑ n ∈ range (a * b), F n) = ∑ j ∈ range a, ∑ i ∈ range b, F (j * b + i) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem r_mono (f : P2) : Monotone (r f) := fun _ _ h =>
  sum_le_sum_of_subset (range_mono h)

theorem r_pos (f : P2) {N : ℕ} (hN : 0 < N) : 0 < r f N := by
  have h : w (f ^ 0) ≤ r f N := single_le_sum (f := fun n => w (f ^ n))
    (fun _ _ => Nat.zero_le _) (mem_range.mpr hN)
  simpa [Nat.succ_le_iff] using h

theorem r_submultiplicative (f : P2) (a b : ℕ) :
    r f (2 ^ (a + b)) ≤ r f (2 ^ a) * r f (2 ^ b) := by
  unfold r
  rw [pow_add, sum_blocks, sum_mul]
  refine sum_le_sum fun j _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  change w (f ^ (j * 2 ^ b + i)) ≤ w (f ^ j) * w (f ^ i)
  rw [pow_add, pow_mul, ← weight_dyadic_pow (f ^ j) b]
  exact card_support_mul_le

theorem garbe_growth_exists (f : P2) : ∃ rate, HasGrowthRate f rate := by
  let u (n : ℕ) := Real.log (r f (2 ^ n) : ℝ)
  have hpos (n : ℕ) : (0 : ℝ) < r f (2 ^ n) := by
    exact_mod_cast r_pos f (by positivity : 0 < (2 : ℕ) ^ n)
  have ha : Subadditive u := by
    intro m n
    unfold u
    rw [← Real.log_mul (hpos m).ne' (hpos n).ne']
    apply Real.log_le_log (hpos (m+n))
    exact_mod_cast r_submultiplicative f m n
  have hb : BddBelow (Set.range fun n => u n / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply div_nonneg (Real.log_nonneg _) (Nat.cast_nonneg n)
    exact_mod_cast (r_pos f (by positivity : 0 < (2 : ℕ) ^ n))
  refine ⟨Real.exp ha.lim, ?_⟩
  have h := (Real.continuous_exp.tendsto ha.lim).comp (ha.tendsto_lim hb)
  refine h.congr fun k => ?_
  rw [Real.rpow_def_of_pos (hpos k)]
  simp [u, div_eq_mul_inv]

theorem growth_unique {f : P2} {a b : ℝ} (ha : HasGrowthRate f a) (hb : HasGrowthRate f b) :
    a = b := tendsto_nhds_unique ha hb

@[simp] theorem r_monomial (j N : ℕ) : r (X ^ j) N = N := by
  simp [r, ← pow_mul]

@[simp] theorem r_zero {N : ℕ} (hN : 0 < N) : r 0 N = 1 := by
  unfold r
  rw [Finset.sum_eq_single 0]
  · simp
  · intro n _ hn
    simp [zero_pow hn]
  · exact fun h => (h (mem_range.mpr hN)).elim

theorem garbe_monomial (j : ℕ) : HasGrowthRate (X ^ j) 2 := by
  refine tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun k hk => ?_)
  change (2 : ℝ) = (r (X ^ j) (2 ^ k) : ℝ) ^ ((1 : ℝ) / k)
  rw [r_monomial, Nat.cast_pow, Nat.cast_ofNat, one_div, Real.pow_rpow_inv_natCast (by norm_num) hk]

theorem garbe_zero : HasGrowthRate 0 1 := by
  have h (k : ℕ) : (r 0 (2 ^ k) : ℝ) ^ ((1 : ℝ) / k) = 1 := by
    rw [r_zero (by positivity), Nat.cast_one, Real.one_rpow]
  simpa only [HasGrowthRate, h] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

#print axioms garbe_growth_exists
#print axioms garbe_monomial
#print axioms garbe_zero

end
end Garbe
```

### `GarbeSimilarity.lean`

```lean
import GarbeGrowth

namespace Garbe
open Polynomial Finset Filter
open scoped Topology
noncomputable section

theorem growth_ge_one {f : P2} {a : ℝ} (ha : HasGrowthRate f a) : 1 ≤ a := by
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds ha
  intro k
  exact Real.one_le_rpow (by exact_mod_cast r_pos f (by positivity : 0 < (2 : ℕ) ^ k))
    (by positivity)

theorem growth_compare {f g : P2} {a b : ℝ}
    (ha : HasGrowthRate f a) (hb : HasGrowthRate g b)
    (C d : ℕ) (hC : 0 < C) (hle : ∀ k, r f (2 ^ k) ≤ C * r g (2 ^ (k + d))) : a ≤ b := by
  have hd : Tendsto (fun k : ℕ => ((k : ℝ) + d) / k) atTop (𝓝 1) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)).const_add (1 : ℝ)
    refine (by simpa using h : Tendsto (fun k : ℕ => 1 + (d : ℝ) / k) atTop (𝓝 1)).congr' ?_
    refine (eventually_ne_atTop 0).mono fun k hk => ?_
    change 1 + (d : ℝ) / k = ((k : ℝ) + d) / k
    rw [add_div, div_self (by exact_mod_cast hk)]
  have hs := (hb.comp (tendsto_add_atTop_nat d)).rpow hd
    (Or.inl (ne_of_gt (zero_lt_one.trans_le (growth_ge_one hb))))
  have hs' : Tendsto (fun k : ℕ => (r g (2 ^ (k + d)) : ℝ) ^ ((1 : ℝ) / k))
      atTop (𝓝 b) := by
    rw [Real.rpow_one] at hs
    refine hs.congr' ((eventually_ne_atTop 0).mono fun k hk => ?_)
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hkd : (k : ℝ) + d ≠ 0 := by
      apply ne_of_gt
      exact add_pos_of_pos_of_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hk) (Nat.cast_nonneg _)
    simp only [Function.comp_apply, Nat.cast_add]
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    field_simp
  have hC' := (tendsto_const_nhds (x := (C : ℝ))).rpow
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    (Or.inl (by exact_mod_cast hC.ne'))
  rw [Real.rpow_zero] at hC'
  have hh := hC'.mul hs'
  rw [one_mul] at hh
  apply le_of_tendsto_of_tendsto ha hh
  refine Eventually.of_forall fun k => ?_
  change (r f (2 ^ k) : ℝ) ^ ((1 : ℝ) / k) ≤
    (C : ℝ) ^ ((1 : ℝ) / k) * (r g (2 ^ (k + d)) : ℝ) ^ ((1 : ℝ) / k)
  rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle k) (by positivity)

theorem r_shift (f : P2) (c N : ℕ) : r (X ^ c * f) N = r f N := by
  simp only [r, mul_pow, ← pow_mul, weight_shift]

theorem r_expand (f : P2) {c : ℕ} (hc : 0 < c) (N : ℕ) :
    r (f.comp (X ^ c)) N = r f N := by
  simp only [r, ← expand_eq_comp_X_pow, ← map_pow, weight_expand _ hc]

theorem r_reverse (f : P2) (N : ℕ) : r f.reverse N = r f N := by
  simp only [r, ← reverse_pow, weight_reverse]

theorem weight_pow_le (f : P2) (n : ℕ) : w (f ^ n) ≤ w f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ (w f)]
    exact card_support_mul_le.trans (Nat.mul_le_mul_right _ ih)

theorem r_pow_le (f : P2) {c : ℕ} (hc : 0 < c) (N : ℕ) :
    r (f ^ c) N ≤ r f (N * c) := by
  unfold r
  rw [sum_blocks]
  refine sum_le_sum fun j _ => ?_
  simpa only [← pow_mul, mul_comm c j, add_zero] using
    (single_le_sum (f := fun i => w (f ^ (j * c + i))) (fun _ _ => Nat.zero_le _)
      (mem_range.mpr hc))

theorem r_le_pow (f : P2) (c N : ℕ) :
    r f (N * c) ≤ (∑ i ∈ range c, w f ^ i) * r (f ^ c) N := by
  unfold r
  rw [sum_blocks, mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [pow_add, ← pow_mul, mul_comm j c, mul_comm (w f ^ i)]
  exact card_support_mul_le.trans (Nat.mul_le_mul_left _ (weight_pow_le f i))

theorem growth_pow_iff (f : P2) {c : ℕ} (hc : 0 < c) (a : ℝ) :
    HasGrowthRate (f ^ c) a ↔ HasGrowthRate f a := by
  obtain ⟨b, hb⟩ := garbe_growth_exists f
  obtain ⟨b', hb'⟩ := garbe_growth_exists (f ^ c)
  have h₁ : b' ≤ b := by
    apply growth_compare hb' hb 1 c (by decide)
    intro k
    rw [one_mul, pow_add]
    have hc2 : ∀ n : ℕ, n ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ]
        have : 0 < (2 : ℕ) ^ n := by positivity
        omega
    exact (r_pow_le f hc _).trans (r_mono f (Nat.mul_le_mul_left _ (hc2 c)))
  have h₂ : b ≤ b' := by
    let C := ∑ i ∈ range c, w f ^ i
    have hC : 0 < C := by
      have h := single_le_sum (f := fun i => w f ^ i) (fun _ _ => Nat.zero_le _) (mem_range.mpr hc)
      exact Nat.succ_le_iff.mp (by simpa [C] using h)
    apply growth_compare hb hb' C 0 hC
    intro k
    rw [add_zero]
    exact (r_mono f (Nat.le_mul_of_pos_right _ hc)).trans (r_le_pow f c _)
  rw [le_antisymm h₁ h₂] at hb'
  exact ⟨fun h => growth_unique h hb' ▸ hb, fun h => growth_unique h hb ▸ hb'⟩

theorem growth_similarity {f g : P2} (h : Similar f g) (a : ℝ) :
    HasGrowthRate f a ↔ HasGrowthRate g a := by
  induction h with
  | rel p _ hs =>
    cases hs with
    | shift c _ => simp only [HasGrowthRate, r_shift]
    | dil c hc => simp only [HasGrowthRate, r_expand p (by omega : 0 < c)]
    | rev => simp only [HasGrowthRate, r_reverse]
    | pow c hc => exact (growth_pow_iff p (by omega) a).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

#print axioms growth_similarity

end
end Garbe
```

### `GarbeSections.lean`

```lean
import GarbeSimilarity

namespace Garbe
open Polynomial Finset Filter
open scoped Topology
noncomputable section

def parts (a b : P2) : P2 := expand (ZMod 2) 2 a + X * expand (ZMod 2) 2 b

def evenSection (g : P2) : P2 := g.contract 2

def oddSection (g : P2) : P2 := (g.divX).contract 2

theorem coeff_evenSection (g : P2) (i : ℕ) : (evenSection g).coeff i = g.coeff (2 * i) := by
  rw [evenSection, coeff_contract (by decide), Nat.mul_comm]

theorem coeff_oddSection (g : P2) (i : ℕ) : (oddSection g).coeff i = g.coeff (2 * i + 1) := by
  rw [oddSection, coeff_contract (by decide), coeff_divX, Nat.mul_comm i]

theorem coeff_parts_even (a b : P2) (i : ℕ) : (parts a b).coeff (2 * i) = a.coeff i := by
  rw [parts, coeff_add, coeff_expand_mul' (by decide), ← pow_one (X : P2),
    coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_expand (by decide), ite_eq_right, add_zero]
    intro hd
    omega
  · rw [add_zero]

theorem coeff_parts_odd (a b : P2) (i : ℕ) : (parts a b).coeff (2 * i + 1) = b.coeff i := by
  rw [parts, coeff_add, coeff_expand (by decide : 0 < 2),
    ite_eq_right (by omega : ¬2 ∣ 2 * i + 1), zero_add, mul_comm, coeff_mul_X,
    coeff_expand_mul' (by decide)]

theorem parts_sections (g : P2) : parts (evenSection g) (oddSection g) = g := by
  ext i
  by_cases h : i % 2 = 0
  · obtain he : i = 2 * (i / 2) := by omega
    conv_lhs => rw [he, coeff_parts_even, coeff_evenSection, ← he]
  · obtain ho : i = 2 * (i / 2) + 1 := by omega
    conv_lhs => rw [ho, coeff_parts_odd, coeff_oddSection, ← ho]

theorem parts_mul (a b q : P2) :
    parts a b * q ^ 2 = parts (a * q) (b * q) := by
  have h : q ^ 2 = expand (ZMod 2) 2 q := by simpa using dyadic_pow q 1
  rw [h, parts, parts, add_mul, map_mul, map_mul, mul_assoc]

theorem weight_parts (a b : P2) : w (parts a b) = w a + w b := by
  classical
  have hs : (parts a b).support =
      a.support.image (fun i => 2 * i) ∪ b.support.image (fun i => 2 * i + 1) := by
    ext n
    simp only [mem_union, mem_image, mem_support_iff]
    by_cases h : n % 2 = 0
    · have he : n = 2 * (n / 2) := by omega
      constructor
      · intro hn
        rw [he, coeff_parts_even] at hn
        exact Or.inl ⟨n / 2, hn, he.symm⟩
      · rintro (⟨i, hi, rfl⟩ | ⟨i, _, rfl⟩)
        · rwa [coeff_parts_even]
        · omega
    · have ho : n = 2 * (n / 2) + 1 := by omega
      constructor
      · intro hn
        rw [ho, coeff_parts_odd] at hn
        exact Or.inr ⟨n / 2, hn, ho.symm⟩
      · rintro (⟨i, _, rfl⟩ | ⟨i, hi, rfl⟩)
        · omega
        · rwa [coeff_parts_odd]
  have hd : Disjoint (a.support.image (fun i => 2 * i))
      (b.support.image (fun i => 2 * i + 1)) := by
    rw [Finset.disjoint_left]
    intro n ha hb
    obtain ⟨i, _, hi⟩ := mem_image.mp ha
    obtain ⟨j, _, hj⟩ := mem_image.mp hb
    omega
  change (parts a b).support.card = a.support.card + b.support.card
  rw [hs, card_union_of_disjoint hd,
    card_image_of_injective _ (fun _ _ _ => by omega),
    card_image_of_injective _ (fun _ _ _ => by omega)]

def mass (f g : P2) (k : ℕ) : ℕ := ∑ n ∈ range (2 ^ k), w (g * f ^ n)

@[simp] theorem mass_one (f : P2) (k : ℕ) : mass f 1 k = r f (2 ^ k) := by
  simp only [mass, r, one_mul]

@[simp] theorem mass_zero (f : P2) (k : ℕ) : mass f 0 k = 0 := by simp [mass]

@[simp] theorem mass_initial (f g : P2) : mass f g 0 = w g := by simp [mass]

theorem mass_shift (f g : P2) (c k : ℕ) : mass f (X ^ c * g) k = mass f g k := by
  simp only [mass, mul_assoc, weight_shift]

theorem mass_split (f g a b c d : P2) (k : ℕ)
    (hg : parts a b = g) (hgf : parts c d = g * f) :
    mass f g (k + 1) = mass f a k + mass f b k + mass f c k + mass f d k := by
  unfold mass
  rw [pow_succ, sum_blocks]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h (n : ℕ) :
      w (g * (f ^ n) ^ 2) + w (g * f * (f ^ n) ^ 2) =
        w (a * f ^ n) + w (b * f ^ n) + w (c * f ^ n) + w (d * f ^ n) := by
    rw [← hgf, ← hg, parts_mul, parts_mul, weight_parts, weight_parts]
    omega
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  rw [pow_add, pow_add, pow_one, mul_comm n 2, pow_mul, ← mul_assoc]
  simpa only [pow_zero, mul_one, ← pow_mul, mul_comm 2 n, mul_left_comm ((f ^ n) ^ 2),
    ← mul_assoc g, mul_right_comm g _ f] using h n

theorem mass_sections (f g : P2) (k : ℕ) :
    mass f g (k + 1) =
      mass f (evenSection g) k + mass f (oddSection g) k +
      mass f (evenSection (g * f)) k + mass f (oddSection (g * f)) k :=
  mass_split _ _ _ _ _ _ _ (parts_sections _) (parts_sections _)

#print axioms mass_sections

end
end Garbe
```

### `GarbeValues.lean`

```lean
import GarbeSections

namespace Garbe
open Polynomial Finset Filter
open scoped Topology
noncomputable section

theorem tendsto_geometric_root {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun k : ℕ => (a ^ k) ^ ((1 : ℝ) / k)) atTop (𝓝 a) := by
  refine tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun k hk => ?_)
  exact (show (a ^ k) ^ ((1 : ℝ) / k) = a by
    rw [one_div, Real.pow_rpow_inv_natCast ha hk]).symm

theorem growth_of_geometric_bounds {f : P2} {a lo hi : ℝ}
    (ha : 0 ≤ a) (hlo : 0 < lo) (hhi : 0 < hi)
    (h : ∀ k, lo * a ^ k ≤ (r f (2 ^ k) : ℝ) ∧ (r f (2 ^ k) : ℝ) ≤ hi * a ^ k) :
    HasGrowthRate f a := by
  have scaled (C : ℝ) (hC : 0 < C) :
      Tendsto (fun k : ℕ => (C * a ^ k) ^ ((1 : ℝ) / k)) atTop (𝓝 a) := by
    simp_rw [Real.mul_rpow hC.le (pow_nonneg ha _)]
    have hc := (tendsto_const_nhds (x := C)).rpow
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) (Or.inl hC.ne')
    simpa only [Real.rpow_zero, one_mul] using hc.mul (tendsto_geometric_root ha)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (scaled lo hlo) (scaled hi hhi)
  · intro k
    exact Real.rpow_le_rpow (by positivity) (h k).1 (by positivity)
  · intro k
    exact Real.rpow_le_rpow (by positivity) (h k).2 (by positivity)

theorem growth_ge_of_bound {f : P2} {a rate : ℝ} (ha : 0 ≤ a) (hr : HasGrowthRate f rate)
    (h : ∀ k, a ^ k ≤ (r f (2 ^ k) : ℝ)) : a ≤ rate :=
  le_of_tendsto_of_tendsto' (tendsto_geometric_root ha) hr fun k =>
    Real.rpow_le_rpow (pow_nonneg ha _) (h k) (by positivity)

private theorem mass_binomial (k : ℕ) : mass (1 + X) 1 k = 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := mass_split (1 + X) 1 1 0 1 1 k (by simp [parts]) (by simp [parts])
    rw [h, mass_zero, ih, pow_succ]
    omega

theorem garbe_binomial : HasGrowthRate (1 + X) 3 := by
  apply growth_of_geometric_bounds (lo := 1) (hi := 1) (by norm_num) (by norm_num) (by norm_num)
  intro k
  have h : r (1 + X) (2 ^ k) = 3 ^ k := by simpa using mass_binomial k
  simp [h]

private theorem two_P2 : (1 : P2) + 1 = 0 := by
  rw [← Nat.cast_one (R := P2), ← Nat.cast_add]
  exact CharP.cast_eq_zero P2 2

private theorem trinomial_times_binomial :
    (1 + X : P2) * (1 + X + X ^ 2) = 1 + X ^ 3 := by
  calc
    _ = 1 + X ^ 3 + (1 + 1) * X + (1 + 1) * X ^ 2 := by ring
    _ = _ := by rw [two_P2, zero_mul, zero_mul, add_zero, add_zero]

private theorem mass_trinomial (k : ℕ) :
    let f : P2 := 1 + X + X ^ 2
    mass f 1 (k + 1) = 2 * mass f 1 k + mass f (1 + X) k ∧
    mass f (1 + X) (k + 1) = 4 * mass f 1 k := by
  dsimp
  constructor
  · have h := mass_split (1 + X + X ^ 2) 1 1 0 (1 + X) 1 k
      (by simp [parts]) (by simp [parts, map_add, expand_X]; ring)
    rw [h, mass_zero]
    omega
  · have h := mass_split (1 + X + X ^ 2) (1 + X) 1 1 1 X k
      (by simp [parts]) (by rw [trinomial_times_binomial]; simp [parts, expand_X]; ring)
    rw [h, ← pow_one (X : P2), ← mul_one (X ^ 1 : P2), mass_shift]
    omega

theorem garbe_trinomial : HasGrowthRate (1 + X + X ^ 2) (1 + Real.sqrt 5) := by
  let a : ℝ := 1 + Real.sqrt 5
  have hp : 0 < a := by dsimp [a]; positivity
  have hsq : a ^ 2 = 2 * a + 4 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    dsimp [a]
    nlinarith
  let b : ℝ := 4 / a
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b * a = 4 := div_mul_cancel₀ _ hp.ne'
  have hab : 2 + b = a := by nlinarith
  let lo : ℝ := min 1 (2 / b)
  let hi : ℝ := max 1 (2 / b)
  have hlo : 0 < lo := lt_min (by norm_num) (by positivity)
  have hhi : 0 < hi := zero_lt_one.trans_le (le_max_left _ _)
  let f : P2 := 1 + X + X ^ 2
  have bounds (k : ℕ) :
      (lo * a ^ k ≤ (mass f 1 k : ℝ) ∧ (mass f 1 k : ℝ) ≤ hi * a ^ k) ∧
      (lo * (b * a ^ k) ≤ (mass f (1 + X) k : ℝ) ∧
        (mass f (1 + X) k : ℝ) ≤ hi * (b * a ^ k)) := by
    induction k with
    | zero =>
      have hw : w (1 + X : P2) = 2 := by
        simpa only [C_1, pow_zero, pow_one, one_mul] using
          (card_support_binomial (R := ZMod 2) (k := 0) (m := 1) (by decide)
            (x := 1) (y := 1) one_ne_zero one_ne_zero)
      simp only [pow_zero, mul_one, mass_initial, weight_one, hw, Nat.cast_one, Nat.cast_ofNat]
      exact ⟨⟨min_le_left _ _, le_max_left _ _⟩,
        ⟨(le_div_iff₀ hb).mp (min_le_right _ _), (div_le_iff₀ hb).mp (le_max_right _ _)⟩⟩
    | succ k ih =>
      obtain ⟨h1, h2⟩ := mass_trinomial k
      change mass f 1 (k + 1) = _ at h1
      change mass f (1 + X) (k + 1) = _ at h2
      rcases ih with ⟨⟨ih1, ih2⟩, ih3, ih4⟩
      rw [h1, h2, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat, pow_succ]
      change (lo * (a ^ k * a) ≤ 2 * (mass f 1 k : ℝ) + mass f (1 + X) k ∧
        _ ≤ _) ∧ (_ ≤ 4 * (mass f 1 k : ℝ) ∧ _ ≤ _)
      rw [mul_left_comm b, hba]
      have hae : a ^ k * a = a ^ k * (2 + b) := congrArg (fun v => a ^ k * v) hab.symm
      rw [hae]
      constructor
      · constructor <;> linarith [show lo * (a ^ k * (2+b)) = 2*(lo*a^k)+lo*(b*a^k) by ring,
          show hi * (a ^ k * (2+b)) = 2*(hi*a^k)+hi*(b*a^k) by ring]
      · constructor <;> linarith [show lo * (a ^ k * 4) = 4*(lo*a^k) by ring,
          show hi * (a ^ k * 4) = 4*(hi*a^k) by ring]
  apply growth_of_geometric_bounds hp.le hlo hhi
  exact fun k => by simpa using (bounds k).1

theorem garbe_binomial_of_similar (f : P2) (h : Similar f (1 + X)) : HasGrowthRate f 3 :=
  (growth_similarity h _).mpr garbe_binomial

theorem garbe_trinomial_of_similar (f : P2) (h : Similar f (1 + X + X ^ 2)) :
    HasGrowthRate f (1 + Real.sqrt 5) :=
  (growth_similarity h _).mpr garbe_trinomial

#print axioms garbe_binomial
#print axioms garbe_trinomial
#print axioms garbe_binomial_of_similar
#print axioms garbe_trinomial_of_similar

end
end Garbe
```

### `GarbeLower.lean`

```lean
import GarbeValues

namespace Garbe
open Polynomial
noncomputable section

theorem section_even_parts (a b : P2) : evenSection (parts a b) = a := by
  ext i
  rw [coeff_evenSection, coeff_parts_even]

theorem section_odd_parts (a b : P2) : oddSection (parts a b) = b := by
  ext i
  rw [coeff_oddSection, coeff_parts_odd]

theorem weight_sections (g : P2) : w g = w (evenSection g) + w (oddSection g) := by
  rw [← weight_parts, parts_sections]

theorem parts_zero_right (a : P2) : parts a 0 = a ^ 2 := by
  simp [parts, show a ^ 2 = expand (ZMod 2) 2 a from dyadic_pow a 1]

theorem parts_zero_left (b : P2) : parts 0 b = X * b ^ 2 := by
  simp [parts, show b ^ 2 = expand (ZMod 2) 2 b from dyadic_pow b 1]

theorem parts_odd_mul (a b q : P2) :
    parts a b * (X * q ^ 2) = parts (X * (b * q)) (a * q) := by
  calc
    _ = X * (parts a b * q ^ 2) := by ring
    _ = _ := by
      simp only [parts, map_mul, expand_X, show q ^ 2 = expand (ZMod 2) 2 q from dyadic_pow q 1]
      ring

private theorem lower_mass {f : P2} (he : evenSection f ≠ 0) (ho : oddSection f ≠ 0)
    (k : ℕ) (g : P2) (hg : g ≠ 0) : 3 ^ k ≤ mass f g k := by
  induction k generalizing g with
  | zero =>
    rw [mass_initial, pow_zero]
    exact Finset.card_pos.mpr (support_nonempty.mpr hg)
  | succ k ih =>
    rw [mass_sections, pow_succ]
    have hf : f ≠ 0 := by
      intro hf
      apply he
      rw [hf]
      ext i
      simp [coeff_evenSection]
    have hcase : (evenSection g ≠ 0 ∨ oddSection g ≠ 0) := by
      by_contra! h
      apply hg
      rw [← parts_sections g, h.1, h.2]
      simp [parts]
    have hcase' : (evenSection (g*f) ≠ 0 ∨ oddSection (g*f) ≠ 0) := by
      by_contra! h
      apply mul_ne_zero hg hf
      rw [← parts_sections (g*f), h.1, h.2]
      simp [parts]
    by_cases ha : evenSection g = 0
    · have hb := hcase.resolve_left (fun h => h ha)
      have heq : g = X * (oddSection g) ^ 2 := by
        rw [← parts_zero_left, ← ha, parts_sections]
      have hprod : g * f = parts (X * (oddSection f * oddSection g))
          (evenSection f * oddSection g) := by
        conv_lhs => rw [heq, mul_comm _ f, ← parts_sections f, parts_odd_mul]
      rw [ha, mass_zero, hprod, section_even_parts, section_odd_parts]
      have h1 := ih _ hb
      have h2 := ih _ (mul_ne_zero X_ne_zero (mul_ne_zero ho hb))
      have h3 := ih _ (mul_ne_zero he hb)
      omega
    · by_cases hb : oddSection g = 0
      · have heq : g = (evenSection g) ^ 2 := by
          rw [← parts_zero_right, ← hb, parts_sections]
        have hprod : g * f = parts (evenSection f * evenSection g)
            (oddSection f * evenSection g) := by
          conv_lhs => rw [heq, mul_comm _ f, ← parts_sections f, parts_mul]
        rw [hb, mass_zero, hprod, section_even_parts, section_odd_parts]
        have h1 := ih _ ha
        have h2 := ih _ (mul_ne_zero he ha)
        have h3 := ih _ (mul_ne_zero ho ha)
        omega
      · have h1 := ih _ ha
        have h2 := ih _ hb
        rcases hcase' with hc | hd
        · have h3 := ih _ hc
          omega
        · have h3 := ih _ hd
          omega

private theorem square_degree_lt {f g : P2} (h : 2 ≤ w g)
    (hf : f = g ^ 2 ∨ f = X * g ^ 2) : g.natDegree < f.natDegree := by
  have hg : g ≠ 0 := by
    intro he
    simp [he, w] at h
  have hp : 0 < g.natDegree := by
    by_contra! hh
    have hh' : g.natDegree = 0 := Nat.eq_zero_of_le_zero hh
    have he := eq_C_of_natDegree_eq_zero hh'
    have hle : w g ≤ 1 := by
      rw [he]
      simpa only [Finset.card_singleton] using Finset.card_le_card (support_C_subset (g.coeff 0))
    omega
  rcases hf with rfl | rfl
  · rw [natDegree_pow]
    omega
  · rw [natDegree_mul X_ne_zero (pow_ne_zero _ hg), natDegree_X, natDegree_pow]
    omega

theorem garbe_lower_bound (f : P2) (hf : 2 ≤ f.support.card)
    {rate : ℝ} (hr : HasGrowthRate f rate) : 3 ≤ rate := by
  change 2 ≤ w f at hf
  induction hd : f.natDegree using Nat.strong_induction_on generalizing f with
  | h d ih =>
    by_cases he : evenSection f = 0
    · have h : f = X * (oddSection f) ^ 2 := by
        rw [← parts_zero_left, ← he, parts_sections]
      have hw : 2 ≤ w (oddSection f) := by
        rw [weight_sections, he] at hf
        simpa only [w, support_zero, Finset.card_empty, zero_add] using hf
      have hlt := square_degree_lt hw (Or.inr h)
      refine ih _ (hd ▸ hlt) _ ?_ hw rfl
      apply (growth_pow_iff _ (by decide : 0 < 2) _).mp
      have hs := growth_similarity
        (Relation.EqvGen.rel _ _ (SimStep.shift ((oddSection f) ^ 2) 1 (by decide))) rate
      apply hs.mpr
      simpa only [pow_one, ← h] using hr
    · by_cases ho : oddSection f = 0
      · have h : f = (evenSection f) ^ 2 := by
          rw [← parts_zero_right, ← ho, parts_sections]
        have hw : 2 ≤ w (evenSection f) := by
          rw [weight_sections, ho] at hf
          simpa only [w, support_zero, Finset.card_empty, add_zero] using hf
        have hlt := square_degree_lt hw (Or.inl h)
        refine ih _ (hd ▸ hlt) _ ?_ hw rfl
        apply (growth_pow_iff _ (by decide : 0 < 2) _).mp
        rwa [← h]
      · apply growth_ge_of_bound (by norm_num : (0 : ℝ) ≤ 3) hr
        intro k
        exact_mod_cast (mass_one f k ▸ lower_mass he ho k 1 one_ne_zero)

theorem garbe_growth_and_lower_bound (f : P2) (hf : 2 ≤ f.support.card) :
    ∃ rate, HasGrowthRate f rate ∧ 3 ≤ rate := by
  obtain ⟨rate, hr⟩ := garbe_growth_exists f
  exact ⟨rate, hr, garbe_lower_bound f hf hr⟩

#print axioms garbe_growth_and_lower_bound

end
end Garbe
```

### `GarbeGraph.lean`

```lean
import GarbeLower

namespace Garbe
open Polynomial Finset Filter
open scoped Topology
noncomputable section

theorem binary_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

theorem coeff0_ne_zero {g : P2} (hg : g.coeff 0 = 1) : g ≠ 0 := by
  intro h
  rw [h, coeff_zero] at hg
  exact zero_ne_one hg

theorem normalized_factorization {g : P2} (hg : g ≠ 0) :
    ∃ q : P2, q.coeff 0 = 1 ∧ g = X ^ g.natTrailingDegree * q := by
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.mpr (fun _ => coeff_eq_zero_of_lt_natTrailingDegree
    (p := g))
  refine ⟨q, binary_one ?_, hq⟩
  have hp : g.coeff g.natTrailingDegree = q.coeff 0 := by
    calc
      _ = (X ^ g.natTrailingDegree * q).coeff (0 + g.natTrailingDegree) :=
        by simpa only [Nat.zero_add] using congrArg (fun p : P2 => p.coeff g.natTrailingDegree) hq
      _ = _ := coeff_X_pow_mul _ _ _
  exact hp ▸ (coeff_natTrailingDegree_ne_zero.mpr hg)

def trim (g : P2) : P2 := if h : g = 0 then 0 else (normalized_factorization h).choose

theorem trim_spec {g : P2} (hg : g ≠ 0) :
    (trim g).coeff 0 = 1 ∧ g = X ^ g.natTrailingDegree * trim g := by
  simpa only [trim, dite_eq_right hg] using (normalized_factorization hg).choose_spec

@[simp] theorem trim_zero : trim 0 = 0 := dite_eq_left rfl

theorem trim_ne_zero {g : P2} (hg : g ≠ 0) : trim g ≠ 0 :=
  coeff0_ne_zero (trim_spec hg).1

theorem trim_of_coeff0 {g : P2} (hg : g.coeff 0 = 1) : trim g = g := by
  have hz : g.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr
    (Or.inr (hg ▸ one_ne_zero))
  simpa only [hz, pow_zero, one_mul] using (trim_spec (coeff0_ne_zero hg)).2.symm

theorem trim_degree_le (g : P2) : (trim g).natDegree ≤ g.natDegree := by
  by_cases h : g = 0
  · simp [h]
  · conv_rhs => rw [(trim_spec h).2, natDegree_mul (pow_ne_zero _ X_ne_zero)
      (trim_ne_zero h), natDegree_X_pow]
    exact Nat.le_add_left _ _

theorem mass_trim (f g : P2) (k : ℕ) : mass f (trim g) k = mass f g k := by
  by_cases h : g = 0
  · simp [h]
  · conv_rhs => rw [(trim_spec h).2, mass_shift]

theorem evenSection_degree (g : P2) : 2 * (evenSection g).natDegree ≤ g.natDegree := by
  by_cases h : evenSection g = 0
  · simp [h]
  · have hn := show _ from (leadingCoeff_ne_zero.mpr h)
    change (evenSection g).coeff (evenSection g).natDegree ≠ 0 at hn
    rw [coeff_evenSection] at hn
    exact le_natDegree_of_ne_zero hn

theorem oddSection_degree (g : P2) : 2 * (oddSection g).natDegree ≤ g.natDegree := by
  by_cases h : oddSection g = 0
  · simp [h]
  · have hn := show _ from (leadingCoeff_ne_zero.mpr h)
    change (oddSection g).coeff (oddSection g).natDegree ≠ 0 at hn
    rw [coeff_oddSection] at hn
    have hh := le_natDegree_of_ne_zero hn
    omega

def rawChildren (f g : P2) : List P2 :=
  [evenSection g, oddSection g, evenSection (g * f), oddSection (g * f)]

def children (f g : P2) : List P2 :=
  ((rawChildren f g).filter (· ≠ 0)).map trim

theorem child_properties {f g h : P2} (hg : g.natDegree < f.natDegree)
    (hh : h ∈ children f g) : h.coeff 0 = 1 ∧ h.natDegree < f.natDegree := by
  simp only [children, List.mem_map, List.mem_filter, decide_eq_true_eq] at hh
  obtain ⟨q, ⟨hq, hn⟩, rfl⟩ := hh
  refine ⟨(trim_spec hn).1, (trim_degree_le _).trans_lt ?_⟩
  have hm : (g * f).natDegree ≤ g.natDegree + f.natDegree := natDegree_mul_le
  simp only [rawChildren, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · have := evenSection_degree g; omega
  · have := oddSection_degree g; omega
  · have := evenSection_degree (g * f); omega
  · have := oddSection_degree (g * f); omega

def IsVertex (f g : P2) : Prop := g.coeff 0 = 1 ∧ g.natDegree < f.natDegree

abbrev Vertex (f : P2) := {g : P2 // IsVertex f g}

instance (f : P2) : Finite (Vertex f) := by
  let fn (g : Vertex f) (i : Fin f.natDegree) := g.val.coeff i
  apply Finite.of_injective fn
  intro g h he
  apply Subtype.ext
  ext i
  by_cases hi : i < f.natDegree
  · exact congrFun he ⟨i, hi⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by have := g.property.2; omega),
        coeff_eq_zero_of_natDegree_lt (by have := h.property.2; omega)]

theorem mass_children (f g : P2) (k : ℕ) :
    mass f g (k + 1) = ((children f g).map (fun h => mass f h k)).sum := by
  rw [mass_sections, children, List.map_map]
  simp only [Function.comp_def, mass_trim]
  have h (l : List P2) :
      ((l.filter (· ≠ 0)).map (fun h => mass f h k)).sum =
      (l.map (fun h => mass f h k)).sum := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      by_cases ha : a = 0
      · simp [ha]
        simpa using ih
      · simp [ha]
        simpa using ih
  rw [h]
  simp only [rawChildren, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

def paths (f : P2) : ℕ → P2 → ℕ
  | 0, _ => 1
  | k+1, g => ((children f g).map (paths f k)).sum

theorem list_sum_le {α : Type*} (l : List α) (F G : α → ℕ)
    (h : ∀ g ∈ l, F g ≤ G g) : (l.map F).sum ≤ (l.map G).sum := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    exact Nat.add_le_add (h g (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem list_sum_mul {α : Type*} (l : List α) (F : α → ℕ) (c : ℕ) :
    (l.map (fun g => c * F g)).sum = c * (l.map F).sum := by
  induction l with
  | nil => simp
  | cons g l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem weight_le_degree (g : P2) : w g ≤ g.natDegree + 1 := by
  have hs : g.support ⊆ range (g.natDegree + 1) := fun i hi =>
    mem_range.mpr (Nat.lt_succ_of_le (le_natDegree_of_mem_supp i hi))
  simpa only [card_range] using card_le_card hs

theorem paths_mass_bounds (f : P2) (k : ℕ) (g : P2) (hg : IsVertex f g) :
    paths f k g ≤ mass f g k ∧ mass f g k ≤ f.natDegree * paths f k g := by
  induction k generalizing g with
  | zero =>
    rw [paths, mass_initial, mul_one]
    exact ⟨card_pos.mpr (support_nonempty.mpr (coeff0_ne_zero hg.1)),
      (weight_le_degree g).trans hg.2⟩
  | succ k ih =>
    rw [paths, mass_children, ← list_sum_mul]
    exact ⟨list_sum_le _ _ _ (fun q hq => (ih q (child_properties hg.2 hq)).1),
      list_sum_le _ _ _ (fun q hq => (ih q (child_properties hg.2 hq)).2)⟩

theorem mass_le_weight_mul_r (f g : P2) (k : ℕ) :
    mass f g k ≤ w g * r f (2 ^ k) := by
  unfold mass r
  rw [mul_sum]
  exact sum_le_sum fun _ _ => card_support_mul_le

theorem paths_le_root_mass (f g : P2) (k : ℕ) (hg : IsVertex f g) :
    paths f k g ≤ f.natDegree * r f (2 ^ k) :=
  (paths_mass_bounds f k g hg).1.trans <|
    (mass_le_weight_mul_r f g k).trans (Nat.mul_le_mul_right _ ((weight_le_degree g).trans hg.2))

theorem paths_growth_at_root {f : P2} (hd : 0 < f.natDegree) {rate : ℝ}
    (hr : HasGrowthRate f rate) :
    Tendsto (fun k : ℕ => (paths f k 1 : ℝ) ^ ((1 : ℝ) / k)) atTop (𝓝 rate) := by
  let d : ℝ := f.natDegree
  have hdp : 0 < d := by dsimp [d]; exact_mod_cast hd
  have hroot : IsVertex f 1 := ⟨by simp, by simpa using hd⟩
  have hs := (tendsto_const_nhds (x := d⁻¹)).rpow
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) (Or.inl (inv_ne_zero hdp.ne'))
  rw [Real.rpow_zero] at hs
  have hl := hs.mul hr
  rw [one_mul] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hr
  · intro k
    change d⁻¹ ^ ((1 : ℝ) / k) * (r f (2 ^ k) : ℝ) ^ ((1 : ℝ) / k) ≤
      (paths f k 1 : ℝ) ^ ((1 : ℝ) / k)
    rw [← Real.mul_rpow (inv_nonneg.mpr hdp.le) (Nat.cast_nonneg _)]
    apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    have hh := (paths_mass_bounds f k 1 hroot).2
    rw [mass_one] at hh
    have hh' : (r f (2 ^ k) : ℝ) ≤ d * (paths f k 1 : ℝ) := by dsimp [d]; exact_mod_cast hh
    rw [← div_eq_inv_mul, div_le_iff₀ hdp, mul_comm]
    exact hh'
  · intro k
    have hh := (paths_mass_bounds f k 1 hroot).1
    rw [mass_one] at hh
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hh) (by positivity)

#print axioms paths_mass_bounds
#print axioms paths_le_root_mass
#print axioms paths_growth_at_root

end
end Garbe
```

### `GarbeBranching.lean`

```lean
import GarbeGraph

namespace Garbe
open Polynomial Finset Filter
open scoped Topology
noncomputable section

theorem coeff0_mul (g f : P2) : (g*f).coeff 0 = g.coeff 0 * f.coeff 0 :=
  (constantCoeff (R := ZMod 2)).map_mul g f

theorem nonzero_even {g : P2} (h : g.coeff 0 = 1) : evenSection g ≠ 0 :=
  coeff0_ne_zero (by simpa only [coeff_evenSection, mul_zero] using h)

theorem child_length_ge_three {f g : P2} (hf : f.coeff 0 = 1)
    (hodd : oddSection f ≠ 0) (hg : g.coeff 0 = 1) : 3 ≤ (children f g).length := by
  have hgf : (g*f).coeff 0 = 1 := by rw [coeff0_mul, hg, hf, one_mul]
  have h1 := nonzero_even hg
  have h2 := nonzero_even hgf
  have ho : oddSection g ≠ 0 ∨ oddSection (g*f) ≠ 0 := by
    by_contra! hh
    have he : g = (evenSection g)^2 := by rw [← parts_zero_right, ← hh.1, parts_sections]
    have hm : g * f = parts (evenSection f * evenSection g) (oddSection f * evenSection g) := by
      conv_lhs => rw [he, mul_comm _ f, ← parts_sections f, parts_mul]
    rw [hm, section_odd_parts] at hh
    exact mul_ne_zero hodd h1 hh.2
  rcases ho with ha | hb
  · by_cases hb : oddSection (g*f) = 0 <;> simp [children, rawChildren, h1, h2, ha, hb]
  · by_cases ha : oddSection g = 0 <;> simp [children, rawChildren, h1, h2, ha, hb]

theorem child_length_four {f g : P2} (hf : f.coeff 0 = 1) (hg : g.coeff 0 = 1)
    (ha : oddSection g ≠ 0) (hb : oddSection (g*f) ≠ 0) :
    (children f g).length = 4 := by
  have hgf : (g*f).coeff 0 = 1 := by rw [coeff0_mul, hg, hf, one_mul]
  simp [children, rawChildren, nonzero_even hg, nonzero_even hgf, ha, hb]

theorem vertex_one {f : P2} (hf : 0 < f.natDegree) : IsVertex f 1 := by
  exact ⟨by simp, by simpa using hf⟩

theorem even_mem_children (f : P2) {g : P2} (hg : g.coeff 0 = 1) : evenSection g ∈ children f g := by
  have h : (evenSection g).coeff 0 = 1 := by simpa [coeff_evenSection] using hg
  exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨by simp [rawChildren], by simp [nonzero_even hg]⟩,
    trim_of_coeff0 h⟩

inductive Route (f : P2) : ℕ → P2 → P2 → Prop
  | nil (g) : Route f 0 g g
  | cons {k g h q} : h ∈ children f g → Route f k h q → Route f (k + 1) g q

theorem route_append {f : P2} {j k : ℕ} {g h q : P2}
    (a : Route f j g h) (b : Route f k h q) : Route f (j+k) g q := by
  induction a with
  | nil => simpa only [zero_add] using b
  | @cons j g m h hm _ ih =>
    simpa only [Nat.succ_add] using Route.cons hm (ih b)

theorem route_vertex {f g q : P2} {n : ℕ} (hg : IsVertex f g) (h : Route f n g q) :
    IsVertex f q := by
  induction h with
  | nil => exact hg
  | cons hh _ ih => exact ih (child_properties hg.2 hh)

theorem route_to_one (f : P2) (n : ℕ) (g : P2) (hg : g.coeff 0 = 1)
    (hd : g.natDegree ≤ n) : Route f n g 1 := by
  induction n generalizing g with
  | zero =>
    have he := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hd)
    rw [hg, C_1] at he
    rw [he]
    exact Route.nil _
  | succ n ih =>
    apply Route.cons (even_mem_children f hg)
    apply ih
    · simpa only [coeff_evenSection, mul_zero] using hg
    · have := evenSection_degree g
      omega

theorem paths_lower {f : P2} (hf : f.coeff 0 = 1) (ho : oddSection f ≠ 0)
    (k : ℕ) {g : P2} (hg : IsVertex f g) : 3 ^ k ≤ paths f k g := by
  induction k generalizing g with
  | zero => simp [paths]
  | succ k ih =>
    rw [paths, pow_succ, mul_comm]
    calc
      3 * 3 ^ k ≤ (children f g).length * 3 ^ k :=
        Nat.mul_le_mul_right _ (child_length_ge_three hf ho hg.1)
      _ = ((children f g).map (fun _ => 3 ^ k)).sum := by simp
      _ ≤ _ := list_sum_le _ _ _ (fun q hq => ih (child_properties hg.2 hq))

private theorem list_const_lt {α : Type*} (l : List α) (F : α → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, c ≤ F x) (hw : ∃ x ∈ l, c < F x) : l.length * c < (l.map F).sum := by
  induction l with
  | nil => simp at hw
  | cons x l ih =>
    rw [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons]
    obtain ⟨y, hy, hy'⟩ := hw
    rcases List.mem_cons.mp hy with rfl | hy
    · have hl : l.length * c ≤ (l.map F).sum := by
        simpa using list_sum_le l (fun _ => c) F (fun y hy => h y (List.mem_cons_of_mem _ hy))
      omega
    · have hl := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨y, hy, hy'⟩
      have hx := h x (List.mem_cons_self ..)
      omega

theorem paths_strict_along_route {f : P2} (hf : f.coeff 0 = 1) (ho : oddSection f ≠ 0)
    {j : ℕ} (k : ℕ) {g q : P2} (hg : IsVertex f g)
    (hr : Route f j g q) (hq : 3 ^ k < paths f k q) : 3 ^ (k+j) < paths f (k+j) g := by
  induction hr with
  | nil => simpa only [add_zero] using hq
  | @cons j g h q hmem hh ih =>
    rw [← Nat.add_assoc, pow_succ, mul_comm, paths]
    apply lt_of_le_of_lt (Nat.mul_le_mul_right _ (child_length_ge_three hf ho hg.1))
    exact list_const_lt _ _ _ (fun q hq => paths_lower hf ho _ (child_properties hg.2 hq))
      ⟨h, hmem, ih (child_properties hg.2 hmem) hq⟩

theorem paths_blocks (f : P2) {l C : ℕ} (h : ∀ g, IsVertex f g → C ≤ paths f l g)
    (k : ℕ) {g : P2} (hg : IsVertex f g) : C * paths f k g ≤ paths f (k+l) g := by
  induction k generalizing g with
  | zero => simpa [paths] using h g hg
  | succ k ih =>
    rw [Nat.succ_add, paths, paths, ← list_sum_mul]
    exact list_sum_le _ _ _ (fun q hq => ih (child_properties hg.2 hq))

theorem pow_paths_mul (f : P2) {l C : ℕ} (h : ∀ g, IsVertex f g → C ≤ paths f l g)
    (k : ℕ) {g : P2} (hg : IsVertex f g) : C ^ k ≤ paths f (k*l) g := by
  induction k with
  | zero => simp [paths]
  | succ k ih =>
    rw [pow_succ', Nat.succ_mul]
    exact (Nat.mul_le_mul_left _ ih).trans (paths_blocks f h _ hg)

theorem no_four_at_rate_three {f : P2} (hf : f.coeff 0 = 1) (ho : oddSection f ≠ 0)
    (hd : 0 < f.natDegree) (hRate : HasGrowthRate f 3)
    {n : ℕ} {q : P2} (hq : Route f n 1 q) :
    oddSection q = 0 ∨ oddSection (q*f) = 0 := by
  by_contra! h
  let l := 1 + (f.natDegree + n)
  let C := 3 ^ l + 1
  have hqv := route_vertex (vertex_one hd) hq
  have h4 : 3 ^ 1 < paths f 1 q := by
    change 3 < ((children f q).map (fun _ => (1 : ℕ))).sum
    calc
      3 < (children f q).length := by rw [child_length_four hf hqv.1 h.1 h.2]; decide
      _ = _ := by simp
  have hC (g : P2) (hg : IsVertex f g) : C ≤ paths f l g := by
    exact paths_strict_along_route hf ho 1 hg
      (route_append (route_to_one f _ g hg.1 hg.2.le) hq) h4
  have hall (k : ℕ) : (C : ℝ) ^ k ≤ (r f (2 ^ (k*l)) : ℝ) := by
    exact_mod_cast (pow_paths_mul f hC k (vertex_one hd)).trans
      ((paths_mass_bounds f (k*l) 1 (vertex_one hd)).1.trans_eq (mass_one _ _))
  let a : ℝ := (C : ℝ) ^ (1 / (l : ℝ))
  have hapos : 0 < a := by dsimp [a, C]; positivity
  have hl : l ≠ 0 := by dsimp [l]; omega
  have ha : a ^ l = C := by rw [show a = (C : ℝ) ^ (1 / (l : ℝ)) from rfl, one_div, Real.rpow_inv_natCast_pow (by positivity) hl]
  have ht : Tendsto (fun k : ℕ => k * l) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    refine eventually_atTop.2 ⟨b, fun k hk => hk.trans ?_⟩
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hl)
  have hle : a ≤ 3 := by
    apply le_of_tendsto_of_tendsto ((tendsto_geometric_root hapos.le).comp ht) (hRate.comp ht)
    refine Eventually.of_forall fun k => ?_
    change (a ^ (k*l)) ^ ((1 : ℝ)/(k*l : ℕ)) ≤ (r f (2 ^ (k*l)) : ℝ) ^ ((1 : ℝ)/(k*l : ℕ))
    rw [mul_comm k l, pow_mul, ha]
    apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    simpa only [mul_comm l k] using hall k
  have hh := pow_le_pow_left₀ hapos.le hle l
  rw [ha] at hh
  norm_num [C] at hh

#print axioms no_four_at_rate_three

end
end Garbe
```

### `GarbeRigidityThree.lean`

```lean
import GarbeBranching
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

namespace Garbe
open Polynomial Finset Filter
open scoped Topology
noncomputable section

def exponents (f : P2) : P2 →₀ ℕ := by
  classical
  exact factorization f

def exponentGcd (f : P2) : ℕ := (exponents f).support.gcd (exponents f)

theorem exponents_mul {a b : P2} (ha : a ≠ 0) (hb : b ≠ 0) :
    exponents (a*b) = exponents a + exponents b := by
  classical
  exact factorization_mul ha hb

theorem exponents_pow (f : P2) (n : ℕ) : exponents (f^n) = n • exponents f := by
  classical
  exact factorization_pow

theorem binary_monic {f : P2} (hf : f ≠ 0) : f.Monic :=
  binary_one (leadingCoeff_ne_zero.mpr hf)

theorem exponents_prod (f : P2) (hf : f ≠ 0) :
    ∏ p ∈ (exponents f).support, p ^ exponents f p = f := by
  classical
  unfold exponents
  rw [support_factorization]
  simp_rw [factorization_eq_count]
  rw [← Finset.prod_multiset_count, UniqueFactorizationMonoid.prod_normalizedFactors_eq hf,
    (binary_monic hf).normalize_eq_self]

theorem exponentGcd_pos {f : P2} (hf : f ≠ 0) (h1 : f ≠ 1) : 0 < exponentGcd f := by
  classical
  apply Nat.pos_of_ne_zero
  intro h
  have hs : (exponents f).support = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have := (Finset.gcd_eq_zero_iff.mp h) p hp
    exact Finsupp.mem_support_iff.mp hp this
  have hh := exponents_prod f hf
  rw [hs, Finset.prod_empty] at hh
  exact h1 hh.symm

theorem exponentGcd_root (f : P2) (hf : f ≠ 0) :
    ∃ g : P2, f = g ^ exponentGcd f := by
  classical
  let g := ∏ p ∈ (exponents f).support, p ^ (exponents f p / exponentGcd f)
  refine ⟨g, ?_⟩
  conv_rhs => dsimp only [g]; rw [← Finset.prod_pow]
  simp_rw [← pow_mul]
  nth_rw 1 [← exponents_prod f hf]
  apply Finset.prod_congr rfl
  intro p hp
  have hh : exponentGcd f ∣ exponents f p := Finset.gcd_dvd hp
  rw [Nat.div_mul_cancel hh]

theorem exponentGcd_square (g : P2) : 2 ∣ exponentGcd (g ^ 2) := by
  apply Finset.dvd_gcd
  intro p _
  rw [exponents_pow, Finsupp.nsmul_apply, nsmul_eq_mul]
  exact dvd_mul_right _ _

theorem eq_one_of_degree_zero {g : P2} (hg : g.coeff 0 = 1) (hd : g.natDegree = 0) :
    g = 1 := by
  rw [eq_C_of_natDegree_eq_zero hd, hg, C_1]

theorem even_mul_mem_children (f g : P2) (h : (g*f).coeff 0 = 1) :
    evenSection (g*f) ∈ children f g := by
  have hc : (evenSection (g*f)).coeff 0 = 1 := by
    simpa only [coeff_evenSection, mul_zero] using h
  exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨by simp [rawChildren],
    by simp [nonzero_even h]⟩, trim_of_coeff0 hc⟩

private theorem reachable_square_lift {f : P2} (hf : f.coeff 0 = 1)
    (ho : oddSection f ≠ 0) (hd : 0 < f.natDegree) (hr : HasGrowthRate f 3)
    (k : ℕ) {g : P2} {j : ℕ} (hg : Route f j 1 g) :
    ∃ q : P2, IsVertex f q ∧ ∃ s : ℕ, q ^ (2 ^ k) = g * f ^ s := by
  induction k generalizing g j with
  | zero => exact ⟨g, route_vertex (vertex_one hd) hg, 0, by simp⟩
  | succ k ih =>
    have hg0 := (route_vertex (vertex_one hd) hg).1
    have hgf0 : (g*f).coeff 0 = 1 := by rw [coeff0_mul, hg0, hf, one_mul]
    have hnext : ∃ a ∈ children f g, ∃ b : ℕ, a ^ 2 = g * f ^ b := by
      rcases no_four_at_rate_three hf ho hd hr hg with h | h
      · refine ⟨_, even_mem_children f hg0, 0, ?_⟩
        rw [pow_zero, mul_one, ← parts_zero_right, ← h, parts_sections]
      · refine ⟨_, even_mul_mem_children f g hgf0, 1, ?_⟩
        rw [pow_one, ← parts_zero_right, ← h, parts_sections]
    obtain ⟨a, ha, b, hb⟩ := hnext
    have ha' := route_append hg (Route.cons ha (Route.nil a))
    obtain ⟨q, hq, s, hs⟩ := ih ha'
    refine ⟨q, hq, b+s*2, ?_⟩
    rw [pow_succ, pow_mul, hs, mul_pow, hb, ← pow_mul, mul_assoc, ← pow_add]

private theorem proportional_of_square_lifts {f g : P2} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ k : ℕ, ∃ q : P2, q ≠ 0 ∧ ∃ s : ℕ, q ^ (2 ^ k) = g * f ^ s)
    (p : P2) : f.natDegree * exponents g p = g.natDegree * exponents f p := by
  let x := f.natDegree * exponents g p
  let y := g.natDegree * exponents f p
  let k := x+y
  obtain ⟨q, hq, s, hs⟩ := h k
  have h₁ := congrArg natDegree hs
  simp only [natDegree_mul hg (pow_ne_zero s hf), natDegree_pow] at h₁
  have h₂ := congrArg (fun z => exponents z p) hs
  simp only [exponents_mul hg (pow_ne_zero s hf), exponents_pow,
    Finsupp.add_apply, Finsupp.nsmul_apply, nsmul_eq_mul] at h₂
  change (2 ^ k : ℕ) * exponents q p = exponents g p + s * exponents f p at h₂
  have h₃ : x + s * (f.natDegree * exponents f p) = 2 ^ k * (f.natDegree * exponents q p) := by
    dsimp [x]
    calc
      _ = f.natDegree * (exponents g p + s * exponents f p) := by ring
      _ = _ := by rw [← h₂]; ring
  have h₄ : y + s * (f.natDegree * exponents f p) = 2 ^ k * (q.natDegree * exponents f p) := by
    dsimp [y]
    calc
      _ = exponents f p * (g.natDegree + s * f.natDegree) := by ring
      _ = _ := by rw [← h₁]; ring
  have hx : x < 2 ^ k := (Nat.le_add_right x y).trans_lt (Nat.lt_two_pow_self (n := k))
  have hy : y < 2 ^ k := (Nat.le_add_left y x).trans_lt (Nat.lt_two_pow_self (n := k))
  have hmod' : (x + s * (f.natDegree * exponents f p)) % (2 ^ k) =
      (y + s * (f.natDegree * exponents f p)) % (2 ^ k) := by
    rw [h₃, h₄, Nat.mul_mod_right, Nat.mul_mod_right]
  have hm : x % (2 ^ k) = y % (2 ^ k) := (Nat.ModEq.add_right_cancel' _ hmod')
  simpa only [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hm

private theorem primitive_reachable_eq_one {f g : P2} {j : ℕ}
    (hf : f.coeff 0 = 1) (ho : oddSection f ≠ 0) (hd : 0 < f.natDegree)
    (hprim : exponentGcd f = 1) (hr : HasGrowthRate f 3) (hg : Route f j 1 g) :
    g = 1 := by
  have hg' := route_vertex (vertex_one hd) hg
  have hh := proportional_of_square_lifts (coeff0_ne_zero hf) (coeff0_ne_zero hg'.1) (fun k => by
    obtain ⟨q, hq, s, hs⟩ := reachable_square_lift hf ho hd hr k hg
    exact ⟨q, coeff0_ne_zero hq.1, s, hs⟩)
  have hdvd : f.natDegree ∣ g.natDegree := by
    have hl : f.natDegree ∣ (exponents f).support.gcd (fun p => g.natDegree * exponents f p) := by
      apply Finset.dvd_gcd
      intro p _
      rw [← hh p]
      exact dvd_mul_right _ _
    rw [Finset.gcd_mul_left, normalize_eq] at hl
    change f.natDegree ∣ g.natDegree * exponentGcd f at hl
    simpa only [hprim, mul_one] using hl
  apply eq_one_of_degree_zero hg'.1
  by_contra h
  exact hg'.2.not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero h) hdvd)

private theorem primitive_three_binomial {f : P2} (hf : f.coeff 0 = 1) (hd : 0 < f.natDegree)
    (hprim : exponentGcd f = 1) (hr : HasGrowthRate f 3) :
    ∃ i : ℕ, 0 < i ∧ f = 1 + X ^ i := by
  have ho : oddSection f ≠ 0 := by
    intro he
    have hs : f = (evenSection f)^2 := by rw [← parts_zero_right, ← he, parts_sections]
    have hdvd := exponentGcd_square (evenSection f)
    rw [← hs, hprim] at hdvd
    norm_num at hdvd
  have he_child : evenSection f ∈ children f 1 := by
    simpa only [one_mul] using even_mul_mem_children f 1 (by simpa only [one_mul] using hf)
  have ho_child : trim (oddSection f) ∈ children f 1 := by
    apply List.mem_map.mpr
    exact ⟨_, List.mem_filter.mpr ⟨by simp [rawChildren], by simp [ho]⟩, rfl⟩
  have he := primitive_reachable_eq_one hf ho hd hprim hr (Route.cons he_child (Route.nil _))
  have ht := primitive_reachable_eq_one hf ho hd hprim hr (Route.cons ho_child (Route.nil _))
  have hodd : oddSection f = X ^ (oddSection f).natTrailingDegree := by
    have h := (trim_spec ho).2
    simpa only [ht, mul_one] using h
  let m := (oddSection f).natTrailingDegree
  refine ⟨2*m+1, by omega, ?_⟩
  conv_lhs => rw [← parts_sections f, he, hodd, parts, map_one, map_pow, expand_X, ← pow_mul]
  change 1 + X * X ^ (2*m) = 1 + X ^ (2*m+1)
  rw [pow_succ, mul_comm X]

theorem normalized_rate_three_similar (f : P2) (hf : f.coeff 0 = 1)
    (hp : 0 < f.natDegree) (hr : HasGrowthRate f 3) : Similar f (1 + X) := by
  induction hd : f.natDegree using Nat.strong_induction_on generalizing f with
  | h d ih =>
    by_cases hprim : exponentGcd f = 1
    · obtain ⟨i, hi, he⟩ := primitive_three_binomial hf hp hprim hr
      rw [he]
      by_cases hi' : i = 1
      · rw [hi', pow_one]
        exact Relation.EqvGen.refl _
      · apply Relation.EqvGen.symm
        have hs := Relation.EqvGen.rel _ _ (SimStep.dil (1+X) i (by omega))
        simpa only [← expand_eq_comp_X_pow, map_add, map_one, expand_X] using hs
    · have hne : f ≠ 1 := by
        intro h
        rw [h, natDegree_one] at hp
        omega
      have hge := exponentGcd_pos (coeff0_ne_zero hf) hne
      have htwo : 1 < exponentGcd f := by omega
      obtain ⟨g, h⟩ := exponentGcd_root f (coeff0_ne_zero hf)
      have hg : g.coeff 0 = 1 := by
        apply binary_one
        intro hz
        have heq := congrArg (fun p : P2 => p.coeff 0) h
        change f.coeff 0 = (g ^ exponentGcd f).coeff 0 at heq
        rw [show (g ^ exponentGcd f).coeff 0 = (g.coeff 0) ^ exponentGcd f from
          (constantCoeff (R := ZMod 2)).map_pow _ _, hz, zero_pow hge.ne', hf] at heq
        exact one_ne_zero heq
      have hh := congrArg natDegree h
      rw [natDegree_pow] at hh
      have hgpos : 0 < g.natDegree := by
        by_contra! h0
        rw [Nat.eq_zero_of_le_zero h0, mul_zero] at hh
        omega
      have hlt : g.natDegree < d := by
        rw [← hd, hh]
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right htwo hgpos
      have hRate : HasGrowthRate g 3 := (growth_pow_iff _ hge _).mp (h ▸ hr)
      have hgSim := ih _ hlt g hg hgpos hRate rfl
      have hstep := Relation.EqvGen.rel _ _ (SimStep.pow g (exponentGcd f) htwo)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (h ▸ hstep)) hgSim

theorem rate_three_similar (f : P2) (hf : 2 ≤ f.support.card)
    (hr : HasGrowthRate f 3) : Similar f (1 + X) := by
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hf
  have hspec := trim_spec hf0
  have hsim : Similar (trim f) f := by
    by_cases h : f.natTrailingDegree = 0
    · have e : f = trim f := by simpa only [h, pow_zero, one_mul] using hspec.2
      rw [← e]
      exact Relation.EqvGen.refl _
    · have hs := Relation.EqvGen.rel _ _ (SimStep.shift (trim f) _ (Nat.pos_of_ne_zero h))
      exact Eq.mp (congrArg (Similar (trim f)) hspec.2.symm) hs
  have hw : 2 ≤ w (trim f) := by
    have h := congrArg w hspec.2
    rw [weight_shift] at h
    exact h ▸ hf
  have hd : 0 < (trim f).natDegree := by
    by_contra! h
    have he := eq_one_of_degree_zero hspec.1 (Nat.eq_zero_of_le_zero h)
    rw [he, weight_one] at hw
    omega
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hsim)
    (normalized_rate_three_similar _ hspec.1 hd ((growth_similarity hsim 3).mpr hr))

theorem garbe_rate_three_iff (f : P2) (hf : 2 ≤ f.support.card) {rate : ℝ}
    (hr : HasGrowthRate f rate) : rate = 3 ↔ Similar f (1 + X) :=
  ⟨fun h => rate_three_similar f hf (h ▸ hr),
    fun h => growth_unique hr (garbe_binomial_of_similar f h)⟩

#print axioms garbe_rate_three_iff

end
end Garbe
```

### `GarbeDeferred.lean`

```lean
import GarbeValues

namespace Garbe
open Filter
open scoped Topology
noncomputable section

section Deferred

variable {A : Type*} [AddCommMonoid A]

/-- Sum over the possible indexed resolutions of one queue entry. -/
def disclose (opened : Bool) (a b : A) (F : A → ℝ) (u : A) : ℝ :=
  if opened then F u + F (u + a) + F (u + b) else F u

/-- Pending entries are ordered oldest first. The effect doubles from one entry to the next. -/
def pendingSum (a b : A) : List Bool → (A → ℝ) → A → ℝ
  | [], F => F
  | i :: is, F => disclose i a b (pendingSum (a+a) (b+b) is F)

theorem pendingSum_shift (a b d : A) (is : List Bool) (F : A → ℝ) (u : A) :
    pendingSum a b is (fun v => F (v+d)) u = pendingSum a b is F (u+d) := by
  induction is generalizing a b u with
  | nil => rfl
  | cons i is ih =>
    cases i <;> simp [pendingSum, disclose, ih, add_right_comm u]

theorem pendingSum_add (a b : A) (is : List Bool) (F G : A → ℝ) (u : A) :
    pendingSum a b is (fun v => F v + G v) u = pendingSum a b is F u + pendingSum a b is G u := by
  induction is generalizing a b u with
  | nil => rfl
  | cons i is ih =>
    cases i
    · exact ih _ _ _
    · simp [pendingSum, disclose, ih]
      ring

theorem pendingSum_append (a b : A) (is : List Bool) (i : Bool) (F : A → ℝ) (u : A) :
    pendingSum a b (is ++ [i]) F u =
      pendingSum a b is (disclose i (2 ^ is.length • a) (2 ^ is.length • b) F) u := by
  induction is generalizing a b u with
  | nil => simp [pendingSum]
  | cons j is ih =>
    have h (c : A) : 2 ^ is.length • (c+c) = 2 ^ (is.length+1) • c := by
      rw [pow_succ, mul_nsmul, two_nsmul, nsmul_add]
    cases j <;> simp [pendingSum, disclose, ih, h]

theorem pendingSum_last (a b : A) (is : List Bool) (i : Bool) (F : A → ℝ) (u : A) :
    pendingSum a b (is ++ [i]) F u =
      disclose i (2 ^ is.length • a) (2 ^ is.length • b) (pendingSum a b is F) u := by
  rw [pendingSum_append]
  cases i
  · rfl
  · change pendingSum a b is (fun x => F x + F (x+2^is.length • a) + F (x+2^is.length • b)) u = _
    rw [pendingSum_add, pendingSum_add, pendingSum_shift, pendingSum_shift]
    rfl

omit [AddCommMonoid A] in
theorem list_sum_pointwise_add (l : List A) (F G : A → ℝ) :
    (l.map (fun u => F u + G u)).sum = (l.map F).sum + (l.map G).sum := by
  induction l with
  | nil => simp
  | cons u l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Move summation over the younger pending choices through one original transition.
Each of their effects is even before that transition, and is halved by the transition. -/
theorem pendingSum_pass (next : A → List A)
    (hnext : ∀ u d, next (u+(d+d)) = (next u).map (·+d))
    (a b : A) (is : List Bool) (F : A → ℝ) (u : A) :
    pendingSum (a+a) (b+b) is (fun x => ((next x).map F).sum) u =
      ((next u).map (pendingSum a b is F)).sum := by
  induction is generalizing a b u with
  | nil => rfl
  | cons i is ih =>
    cases i
    · exact ih (a+a) (b+b) u
    · simp only [pendingSum, disclose]
      rw [ih _ _ u, ih _ _ (u+(a+a)), ih _ _ (u+(b+b)), hnext u a, hnext u b,
        List.map_map, List.map_map, ← list_sum_pointwise_add, ← list_sum_pointwise_add]
      rfl

/-- A step of the postponed process, evaluated by summing original continuation counts.
Both coincident and distinct offsets contribute once for each indexed choice. -/
theorem pendingSum_step (next : A → List A) (even : A → Bool) (base : A → A)
    (hnext : ∀ u d, next (u+(d+d)) = (next u).map (·+d))
    (a b : A) (is : List Bool) (i : Bool)
    (heven : ∀ u, even u = true →
      next u = [base u, base u + 2 ^ is.length • a, base u + 2 ^ is.length • b])
    (F : A → ℝ) (u : A) :
    pendingSum a b (i::is) (fun x => ((next x).map F).sum) u =
      disclose i a b (fun x =>
        if even x then pendingSum a b (is++[true]) F (base x)
        else ((next x).map (pendingSum a b (is++[false]) F)).sum) u := by
  simp only [pendingSum]
  congr 1
  funext x
  rw [pendingSum_pass next hnext]
  by_cases h : even x = true
  · rw [ite_eq_left h, heven x h, pendingSum_last]
    simp [disclose, add_assoc]
  · rw [ite_eq_right h]
    congr 1
    apply List.map_congr_left
    intro y _
    rw [pendingSum_last]
    rfl

private theorem pendingSum_ge_one (a b : A) (is : List Bool) (F : A → ℝ)
    (hF : ∀ u, 1 ≤ F u) (u : A) : 1 ≤ pendingSum a b is F u := by
  induction is generalizing a b u with
  | nil => exact hF u
  | cons i is ih =>
    cases i
    · exact ih _ _ _
    · change 1 ≤ pendingSum (a+a) (b+b) is F u +
        pendingSum (a+a) (b+b) is F (u+a) + pendingSum (a+a) (b+b) is F (u+b)
      linarith [ih (a+a) (b+b) u, ih (a+a) (b+b) (u+a), ih (a+a) (b+b) (u+b)]

omit [AddCommMonoid A] in
private theorem list_sum_real_lower (l : List A) (F : A → ℝ) (c : ℝ)
    (h : ∀ u, c ≤ F u) : c * l.length ≤ (l.map F).sum := by
  induction l with
  | nil => simp
  | cons u l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_succ, mul_add, mul_one]
    linarith [h u]

/-- The sharp lower bound in an affine model with three divisible offsets at even states
and four immediate choices at odd states. The hypothesis on the due offsets means
that at least one of the three possible resolutions exposes four children. -/
theorem deferred_geometric_bound (next : A → List A) (even : A → Bool) (base : A → A)
    (a b : A) (t : ℕ) (P : ℕ → A → ℝ)
    (hnext : ∀ u d, next (u+(d+d)) = (next u).map (·+d))
    (hEven : ∀ u, even u = true → next u = [base u, base u + 2 ^ t • a, base u + 2 ^ t • b])
    (hOdd : ∀ u, even u = false → (next u).length = 4)
    (hDue : ∀ u, even u = false ∨ even (u+a) = false ∨ even (u+b) = false)
    (hZero : ∀ u, 1 ≤ P 0 u)
    (hStep : ∀ k u, P (k+1) u = ((next u).map (P k)).sum)
    (k : ℕ) (u : A) :
    (1+Real.sqrt 5) ^ k ≤ (1+Real.sqrt 5) ^ (t+1) * P k u := by
  let α : ℝ := 1+Real.sqrt 5
  have hα : 1 ≤ α := le_add_of_nonneg_right (Real.sqrt_nonneg 5)
  have hα4 : α ≤ 4 := by
    dsimp [α]
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    nlinarith [Real.sqrt_nonneg 5]
  have αsq : α^2 = 2*α+4 := by
    dsimp [α]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  let C := α ^ (t+1)
  have hC : 0 ≤ C := pow_nonneg (zero_le_one.trans hα) _
  have bound (k : ℕ) (is : List Bool) (hL : is.length = t+1) (u : A) :
      α ^ k * α ^ is.count true ≤ C * pendingSum a b is (P k) u := by
    induction k generalizing is u with
    | zero =>
      rw [pow_zero, one_mul]
      have hc : is.count true ≤ t+1 := (List.count_le_length).trans_eq hL
      exact (pow_le_pow_right₀ hα hc).trans
        (by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (pendingSum_ge_one a b is _ hZero u) hC)
    | succ k ih =>
      cases is with
      | nil => simp at hL
      | cons i is =>
        have hlen : is.length = t := by simpa using hL
        let S := α ^ k * α ^ is.count true
        have hS : 0 ≤ S := by dsimp [S]; positivity
        let B (x : A) := if even x
          then pendingSum a b (is++[true]) (P k) (base x)
          else ((next x).map (pendingSum a b (is++[false]) (P k))).sum
        have hE (x : A) (hx : even x = true) : α*S ≤ C*B x := by
          have hh := ih (is++[true]) (by simp [hlen]) (base x)
          simpa [B, hx, S, List.count_append, pow_succ, mul_left_comm, mul_comm,
            mul_assoc] using hh
        have hO (x : A) (hx : even x = false) : 4*S ≤ C*B x := by
          have hh (y : A) : S ≤ C * pendingSum a b (is++[false]) (P k) y := by
            simpa [S, List.count_append] using ih (is++[false]) (by simp [hlen]) y
          have heq (l : List A) (F : A → ℝ) :
              (l.map (fun y => C * F y)).sum = C * (l.map F).sum := by
            induction l with
            | nil => simp
            | cons y ys ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]
          have hl := list_sum_real_lower (next x)
            (fun y => C * pendingSum a b (is++[false]) (P k) y) S hh
          rw [heq, hOdd x hx] at hl
          simpa [B, hx, mul_comm] using hl
        have hAll (x : A) : α*S ≤ C*B x := by
          cases hx : even x
          · exact (mul_le_mul_of_nonneg_right hα4 hS).trans (hO x hx)
          · exact hE x hx
        rw [show P (k+1) = (fun x => ((next x).map (P k)).sum) from funext (hStep k)]
        rw [pendingSum_step next even base hnext a b is i
          (fun x hx => by rw [hlen]; exact hEven x hx)]
        change _ ≤ C * disclose i a b B u
        cases i
        · simpa [disclose, S, pow_succ, mul_left_comm, mul_comm, mul_assoc] using hAll u
        · have hmul : α^(k+1) * α^((true::is).count true) = 2*(α*S)+4*S := by
            simp only [List.count_cons_self, pow_succ]
            calc
              α ^ k * α * (α ^ is.count true * α) = α^2*S := by dsimp [S]; ring
              _ = _ := by rw [αsq]; ring
          rw [hmul]
          change _ ≤ C * (B u + B (u+a) + B (u+b))
          rcases hDue u with hx | hx | hx
          · linarith [hO u hx, hAll (u+a), hAll (u+b)]
          · linarith [hAll u, hO (u+a) hx, hAll (u+b)]
          · linarith [hAll u, hAll (u+a), hO (u+b) hx]
  have he (n : ℕ) (a b : A) :
      pendingSum a b (List.replicate n false) (P k) u = P k u := by
    induction n generalizing a b with
    | zero => rfl
    | succ n ih => exact ih _ _
  have hc (n : ℕ) : (List.replicate n false).count true = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  simpa only [he, hc, pow_zero, mul_one, C, α] using
    bound k (List.replicate (t+1) false) (by simp) u

#print axioms pendingSum_step
#print axioms deferred_geometric_bound

end Deferred
end
end Garbe
```

### `GarbeProjection.lean`

```lean
import GarbeRigidityThree
import Mathlib.Data.Int.GCD

namespace Garbe
open Polynomial Finset
noncomputable section

theorem finset_gcd_bezout {ι : Type*} (s : Finset ι) (v : ι → ℕ) :
    ∃ c : ι → ℤ, (∑ i ∈ s, c i * (v i : ℤ)) = ((s.gcd v : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨c, hc⟩ := ih
    let a := Nat.gcdA (v i) (s.gcd v)
    let b := Nat.gcdB (v i) (s.gcd v)
    refine ⟨fun j => if j = i then a else b * c j, ?_⟩
    rw [sum_insert hi, Finset.gcd_insert]
    dsimp only
    rw [ite_eq_left (show i = i from rfl)]
    have he : (∑ j ∈ s, (if j = i then a else b * c j) * (v j : ℤ)) =
        b * ∑ j ∈ s, c j * (v j : ℤ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hn : j ≠ i := fun h => hi (h ▸ hj)
      rw [ite_eq_right hn, mul_assoc]
    rw [he, hc]
    have h := Nat.gcd_eq_gcd_ab (v i) (s.gcd v)
    change ((Nat.gcd (v i) (s.gcd v) : ℕ) : ℤ) = _ at h
    change a * (v i : ℤ) + b * ((s.gcd v : ℕ) : ℤ) = ((Nat.gcd (v i) (s.gcd v) : ℕ) : ℤ)
    rw [h]
    dsimp [a, b]
    ring

abbrev Valuation := P2 → ℤ

def intExponents (g : P2) : Valuation := fun p => exponents g p

def valuation (g : P2) : Valuation :=
  fun p => if p = X then 0 else intExponents g p

@[simp] theorem intExponents_one : intExponents 1 = 0 := by
  ext p
  classical
  simp [intExponents, exponents]

theorem intExponents_mul {a b : P2} (ha : a ≠ 0) (hb : b ≠ 0) :
    intExponents (a*b) = intExponents a + intExponents b := by
  ext p
  simp only [intExponents, exponents_mul ha hb, Finsupp.add_apply, Nat.cast_add, Pi.add_apply]

theorem intExponents_pow (g : P2) (n : ℕ) :
    intExponents (g ^ n) = (n : ℤ) • intExponents g := by
  ext p
  simp [intExponents, exponents_pow, Finsupp.nsmul_apply, Pi.smul_apply]

theorem exponent_X_zero_of_coeff0 {g : P2} (hg : g.coeff 0 = 1) : exponents g X = 0 := by
  classical
  rw [exponents, factorization_eq_count, Multiset.count_eq_zero]
  intro h
  have hd : (X : P2) ∣ g := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h
  exact one_ne_zero (hg ▸ (X_dvd_iff.mp hd))

theorem valuation_of_coeff0 {g : P2} (hg : g.coeff 0 = 1) : valuation g = intExponents g := by
  ext p
  by_cases h : p = X
  · subst p; simp [valuation, intExponents, exponent_X_zero_of_coeff0 hg]
  · simp [valuation, h]

theorem valuation_mul {a b : P2} (ha : a ≠ 0) (hb : b ≠ 0) :
    valuation (a*b) = valuation a + valuation b := by
  ext p
  have h := congrFun (intExponents_mul ha hb) p
  by_cases hp : p = X <;> simp [valuation, hp, h]

theorem valuation_pow (g : P2) (n : ℕ) :
    valuation (g ^ n) = (n : ℤ) • valuation g := by
  ext p
  have h := congrFun (intExponents_pow g n) p
  by_cases hp : p = X <;> simp [valuation, hp, h]

theorem valuation_X_pow (n : ℕ) : valuation (X ^ n) = 0 := by
  rw [valuation_pow]
  suffices h : valuation X = 0 by rw [h, smul_zero]
  ext p
  by_cases h : p = X
  · simp [valuation, h]
  · classical
    simp [valuation, h, intExponents, exponents, factorization_eq_count,
      UniqueFactorizationMonoid.normalizedFactors_irreducible irreducible_X,
      (monic_X (R := ZMod 2)).normalize_eq_self]

theorem valuation_trim {g : P2} (hg : g ≠ 0) : valuation (trim g) = valuation g := by
  conv_rhs => rw [(trim_spec hg).2, valuation_mul (pow_ne_zero _ X_ne_zero) (trim_ne_zero hg),
      valuation_X_pow, zero_add]

def weightedValuation (s : Finset P2) (c : P2 → ℤ) : Valuation →+ ℤ where
  toFun v := ∑ p ∈ s, c p * v p
  map_zero' := by simp
  map_add' a b := by
    simp only [Pi.add_apply, mul_add, sum_add_distrib]

theorem exists_valuation_functional (f : P2) (hf : f.coeff 0 = 1) (h : exponentGcd f = 1) :
    ∃ ℓ : Valuation →+ ℤ, ℓ (valuation f) = 1 := by
  obtain ⟨c, hc⟩ := finset_gcd_bezout (exponents f).support (exponents f)
  refine ⟨weightedValuation (exponents f).support c, ?_⟩
  rw [valuation_of_coeff0 hf]
  change (∑ p ∈ (exponents f).support, c p * (exponents f p : ℤ)) = 1
  rw [hc]
  change (exponentGcd f : ℤ) = 1
  rw [h]
  rfl

/-- Projection to the kernel of a functional taking value one on the rule direction. -/
def project (ℓ : Valuation →+ ℤ) (e : Valuation) (v : Valuation) : Valuation :=
  v - (ℓ v) • e

theorem project_ker {ℓ : Valuation →+ ℤ} {e : Valuation} (h : ℓ e = 1)
    (v : Valuation) : ℓ (project ℓ e v) = 0 := by
  rw [project, map_sub, map_zsmul, h, zsmul_eq_mul, mul_one]
  change ℓ v - ℓ v = 0
  rw [sub_self]

theorem project_add (ℓ : Valuation →+ ℤ) (e u v : Valuation) :
    project ℓ e (u+v) = project ℓ e u + project ℓ e v := by
  simp only [project, map_add, add_zsmul]
  abel

theorem project_direction {ℓ : Valuation →+ ℤ} {e : Valuation} (h : ℓ e = 1) :
    project ℓ e e = 0 := by
  rw [project, h, one_zsmul, sub_self]

theorem project_parity {ℓ : Valuation →+ ℤ} {e : Valuation} (h : ℓ e = 1)
    (v : Valuation) :
    (∃ k : Valuation, ℓ k = 0 ∧ project ℓ e v = k+k) ↔
    (∃ j : Valuation, v = j+j) ∨ (∃ j : Valuation, v = e+(j+j)) := by
  constructor
  · rintro ⟨k, hk, hproj⟩
    let n := ℓ v / 2
    have hn : ℓ v = n+n ∨ ℓ v = n+n+1 := by dsimp [n]; omega
    have hv : v = k+k+(ℓ v) • e := sub_eq_iff_eq_add.mp hproj
    rcases hn with h0 | h1
    · exact Or.inl ⟨k+n • e, by calc
        v = k+k+(n+n) • e := by conv_lhs => rw [hv, h0]
        _ = _ := by rw [add_zsmul]; abel⟩
    · exact Or.inr ⟨k+n • e, by calc
        v = k+k+(n+n+1) • e := by conv_lhs => rw [hv, h1]
        _ = _ := by rw [add_zsmul, add_zsmul, one_zsmul]; abel⟩
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨project ℓ e j, project_ker h _, by rw [hj, project_add]⟩
    · exact ⟨project ℓ e j, project_ker h _, by
        rw [hj, project_add, project_direction h, zero_add, project_add]⟩


theorem exists_power_of_dvd_exponents (f : P2) (hf : f ≠ 0) (c : ℕ)
    (hc : ∀ p, c ∣ exponents f p) : ∃ g : P2, f = g ^ c := by
  classical
  refine ⟨∏ p ∈ (exponents f).support, p ^ (exponents f p / c), ?_⟩
  rw [← Finset.prod_pow]
  simp_rw [← pow_mul, Nat.div_mul_cancel (hc _)]
  exact (exponents_prod f hf).symm

theorem normalized_square_iff {g : P2} (hg : g.coeff 0 = 1) :
    (∃ j : Valuation, valuation g = j+j) ↔ oddSection g = 0 := by
  constructor
  · rintro ⟨j, hj⟩
    have hexp (p : P2) : 2 ∣ exponents g p := by
      have h := congrFun hj p
      rw [valuation_of_coeff0 hg] at h
      change (exponents g p : ℤ) = j p + j p at h
      have hh : (2 : ℤ) ∣ (exponents g p : ℤ) := ⟨j p, by omega⟩
      exact Int.natCast_dvd_natCast.mp hh
    obtain ⟨q, hq⟩ := exists_power_of_dvd_exponents g (coeff0_ne_zero hg) 2 hexp
    rw [hq, ← parts_zero_right, section_odd_parts]
  · intro h
    have he : g = (evenSection g)^2 := by
      rw [← parts_zero_right, ← h, parts_sections]
    refine ⟨valuation (evenSection g), ?_⟩
    conv_lhs => rw [he, valuation_pow]
    change (2 : ℤ) • valuation (evenSection g) = _
    rw [two_zsmul]

theorem projected_even_iff {f g : P2} (hf : f.coeff 0 = 1) (hg : g.coeff 0 = 1)
    {ℓ : Valuation →+ ℤ} (hℓ : ℓ (valuation f) = 1) :
    (∃ k : Valuation, ℓ k = 0 ∧ project ℓ (valuation f) (valuation g) = k+k) ↔
    oddSection g = 0 ∨ oddSection (g*f) = 0 := by
  have hgf : (g*f).coeff 0 = 1 := by rw [coeff0_mul, hg, hf, one_mul]
  rw [project_parity hℓ, normalized_square_iff hg, ← normalized_square_iff hgf,
    valuation_mul (coeff0_ne_zero hg) (coeff0_ne_zero hf)]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j+valuation f, ?_⟩
    rw [hj]
    abel
  · rintro ⟨j, hj⟩
    refine ⟨j-valuation f, ?_⟩
    have he := congrArg (fun u : Valuation => u-valuation f) hj
    rw [add_sub_cancel_right] at he
    rw [he]
    abel

theorem projection_zero_vertex {f g : P2} (hf : f.coeff 0 = 1) (hg : IsVertex f g)
    {ℓ : Valuation →+ ℤ}
    (h : project ℓ (valuation f) (valuation g) = 0) : g = 1 := by
  have he : valuation g = ℓ (valuation g) • valuation f := sub_eq_zero.mp h
  have hfn : f ≠ 1 := by
    intro hn
    have hd := hg.2
    rw [hn, natDegree_one] at hd
    exact Nat.not_lt_zero _ hd
  obtain ⟨p, hp⟩ := Finset.gcd_ne_zero_iff.mp (exponentGcd_pos (coeff0_ne_zero hf) hfn).ne'
  have hpos : 0 ≤ ℓ (valuation g) := by
    have hv := congrFun he p
    have hhg := valuation_of_coeff0 hg.1
    have hhf := valuation_of_coeff0 hf
    conv_lhs at hv => rw [hhg]
    conv_rhs at hv => rw [show ℓ (valuation g) • valuation f = ℓ (valuation g) • intExponents f from
      congrArg (fun v => ℓ (valuation g) • v) hhf]
    change (exponents g p : ℤ) = ℓ (valuation g) * (exponents f p : ℤ) at hv
    have hp' : (0 : ℤ) < exponents f p := by exact_mod_cast Nat.pos_of_ne_zero hp.2
    have hn : (0 : ℤ) ≤ exponents g p := Int.natCast_nonneg _
    by_contra! hh
    nlinarith [mul_neg_of_neg_of_pos hh hp']
  let c := (ℓ (valuation g)).toNat
  have hc : (c : ℤ) = ℓ (valuation g) := Int.toNat_of_nonneg hpos
  have hv : intExponents g = intExponents (f ^ c) := by
    rw [intExponents_pow, hc, ← valuation_of_coeff0 hf, ← valuation_of_coeff0 hg.1]
    exact he
  have hexp : exponents g = exponents (f ^ c) := by
    ext p
    have hh := congrFun hv p
    exact_mod_cast (show (exponents g p : ℤ) = (exponents (f^c) p : ℤ) from hh)
  have hg' : g = f^c := by
    rw [← exponents_prod g (coeff0_ne_zero hg.1), ← exponents_prod (f^c) (pow_ne_zero _ (coeff0_ne_zero hf))]
    rw [hexp]
  have hc' : c = 0 := by
    have hd := hg.2
    rw [hg', natDegree_pow] at hd
    by_contra hn
    exact hd.not_ge (by simpa only [one_mul] using
      Nat.mul_le_mul_right f.natDegree (show 1 ≤ c from Nat.pos_of_ne_zero hn))
  simpa only [hc', pow_zero] using hg'

#print axioms exists_valuation_functional
#print axioms project_parity
#print axioms projected_even_iff
#print axioms projection_zero_vertex

end
end Garbe
```

### `GarbeTranslation.lean`

```lean
import GarbeProjection

namespace Garbe
open Polynomial Finset
noncomputable section

theorem exponent_support_irreducible {f p : P2} (h : p ∈ (exponents f).support) :
    Irreducible p := by
  classical
  rw [exponents, support_factorization, Multiset.mem_toFinset] at h
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor _ h).irreducible

theorem exponents_irreducible {p : P2} (hp : Irreducible p) :
    exponents p = Finsupp.single p 1 := by
  classical
  ext q
  rw [exponents, factorization_eq_count,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hp, (binary_monic hp.ne_zero).normalize_eq_self]
  by_cases h : p = q
  · subst q
    simp
  · simp [Ne.symm h]

private theorem factor_product_nonzero (s : Finset P2) (m : P2 → ℕ)
    (hs : ∀ p ∈ s, Irreducible p) : (∏ p ∈ s, p ^ m p) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hs p hp).ne_zero)

private theorem factor_product_exp (s : Finset P2) (m : P2 → ℕ)
    (hs : ∀ p ∈ s, Irreducible p) (q : P2) :
    exponents (∏ p ∈ s, p ^ m p) q = if q ∈ s then m q else 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp [exponents]
  | insert p s hps ih =>
    have hp := hs p (mem_insert_self ..)
    have hs' (p' : P2) (hp' : p' ∈ s) : Irreducible p' := hs p' (mem_insert_of_mem hp')
    rw [prod_insert hps, exponents_mul (pow_ne_zero _ hp.ne_zero) (factor_product_nonzero s m hs'),
      exponents_pow, exponents_irreducible hp, Finsupp.add_apply, Finsupp.nsmul_apply, ih hs']
    by_cases he : q = p
    · subst q
      simp [hps]
    · simp [he]

theorem exponents_injective_nonzero {p q : P2} (hp : p ≠ 0) (hq : q ≠ 0)
    (he : exponents p = exponents q) : p = q := by
  rw [← exponents_prod p hp, ← exponents_prod q hq, he]

/-- Clear the negative entries of the half-difference and the signed power of the rule. -/
theorem balance_valuations {f g g' : P2}
    (hf : f.coeff 0 = 1) (hg : g.coeff 0 = 1) (hg' : g'.coeff 0 = 1)
    (r : ℤ) (h : Valuation)
    (he : valuation g' = valuation g + r • valuation f + (h+h)) :
    ∃ H K : P2, H ≠ 0 ∧ K ≠ 0 ∧ valuation H - valuation K = h ∧
      g' * f ^ (-r).toNat * K^2 = g * f ^ r.toNat * H^2 := by
  classical
  let s := (exponents f).support ∪ (exponents g).support ∪ (exponents g').support
  have hs (p : P2) (hp : p ∈ s) : Irreducible p := by
    simp only [s, mem_union] at hp
    rcases hp with (hp | hp) | hp <;> exact exponent_support_irreducible hp
  have hX : X ∉ s := by
    simp [s, Finsupp.mem_support_iff, exponent_X_zero_of_coeff0 hf,
      exponent_X_zero_of_coeff0 hg, exponent_X_zero_of_coeff0 hg']
  have he' (p : P2) :
      (exponents g' p : ℤ) = exponents g p + r * exponents f p + (h p + h p) := by
    have he := congrFun he p
    rw [valuation_of_coeff0 hf, valuation_of_coeff0 hg, valuation_of_coeff0 hg'] at he
    exact he
  have hsupp (p : P2) (hp : p ∉ s) : h p = 0 := by
    simp only [s, mem_union, Finsupp.mem_support_iff, not_or, not_not] at hp
    have hh := he' p
    rcases hp with ⟨⟨hf, hg⟩, hg'⟩
    simp [hf, hg, hg'] at hh
    omega
  let H := ∏ p ∈ s, p ^ (h p).toNat
  let K := ∏ p ∈ s, p ^ (-h p).toNat
  have hH : H ≠ 0 := factor_product_nonzero _ _ hs
  have hK : K ≠ 0 := factor_product_nonzero _ _ hs
  have hdiff (p : P2) : (exponents H p : ℤ) - (exponents K p : ℤ) = h p := by
    rw [factor_product_exp _ _ hs, factor_product_exp _ _ hs]
    by_cases hp : p ∈ s
    · rw [ite_eq_left hp, ite_eq_left hp]
      omega
    · rw [ite_eq_right hp, ite_eq_right hp, hsupp p hp]
      rfl
  refine ⟨H, K, hH, hK, ?_, ?_⟩
  · ext p
    by_cases hp : p = X
    · subst p
      simp [valuation, hsupp X hX]
    · simpa [valuation, intExponents, hp] using hdiff p
  · apply exponents_injective_nonzero
    · exact mul_ne_zero (mul_ne_zero (coeff0_ne_zero hg') (pow_ne_zero _ (coeff0_ne_zero hf)))
        (pow_ne_zero _ hK)
    · exact mul_ne_zero (mul_ne_zero (coeff0_ne_zero hg) (pow_ne_zero _ (coeff0_ne_zero hf)))
        (pow_ne_zero _ hH)
    ext p
    simp only [exponents_mul (mul_ne_zero (coeff0_ne_zero hg') (pow_ne_zero _ (coeff0_ne_zero hf)))
        (pow_ne_zero _ hK), exponents_mul (mul_ne_zero (coeff0_ne_zero hg) (pow_ne_zero _ (coeff0_ne_zero hf)))
        (pow_ne_zero _ hH),
      exponents_mul (coeff0_ne_zero hg') (pow_ne_zero _ (coeff0_ne_zero hf)),
      exponents_mul (coeff0_ne_zero hg) (pow_ne_zero _ (coeff0_ne_zero hf)),
      exponents_pow, Finsupp.add_apply, Finsupp.nsmul_apply, nsmul_eq_mul]
    change exponents g' p + (-r).toNat * exponents f p + 2 * exponents K p =
      exponents g p + r.toNat * exponents f p + 2 * exponents H p
    apply Int.ofNat_inj.mp
    push_cast
    have hr : (r.toNat : ℤ) - ((-r).toNat : ℤ) = r := by omega
    have hh := he' p
    have hh' := hdiff p
    nlinarith [congrArg (fun z : ℤ => z * (exponents f p : ℤ)) hr]

theorem twice_translation_balance {f g g' : P2}
    (hf : f.coeff 0 = 1) (hg : g.coeff 0 = 1) (hg' : g'.coeff 0 = 1)
    {ℓ : Valuation →+ ℤ} {h : Valuation} (hh : ℓ h = 0)
    (he : project ℓ (valuation f) (valuation g') =
       project ℓ (valuation f) (valuation g) + (h+h)) :
    ∃ r : ℤ, ∃ H K : P2, H ≠ 0 ∧ K ≠ 0 ∧
      project ℓ (valuation f) (valuation H - valuation K) = h ∧
      g' * f ^ (-r).toNat * K^2 = g * f ^ r.toNat * H^2 := by
  let r := ℓ (valuation g') - ℓ (valuation g)
  have hbal : valuation g' = valuation g + r • valuation f + (h+h) := by
    rw [project, project] at he
    have hs := sub_eq_iff_eq_add.mp he
    rw [hs]
    dsimp only [r]
    rw [sub_zsmul]
    abel
  obtain ⟨H, K, hH, hK, hs, hb⟩ := balance_valuations hf hg hg' r h hbal
  exact ⟨r, H, K, hH, hK, by rw [hs, project, hh, zero_zsmul, sub_zero], hb⟩

def projectHom (ℓ : Valuation →+ ℤ) (e : Valuation) : Valuation →+ Valuation where
  toFun := project ℓ e
  map_zero' := by simp [project]
  map_add' := project_add ℓ e

abbrev projected (f : P2) (ℓ : Valuation →+ ℤ) (g : P2) : Valuation :=
  projectHom ℓ (valuation f) (valuation g)

theorem projected_mul {f a b : P2} (ℓ : Valuation →+ ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    projected f ℓ (a*b) = projected f ℓ a + projected f ℓ b := by
  change projectHom ℓ (valuation f) (valuation (a*b)) = _
  rw [valuation_mul ha hb, map_add]

theorem projected_fpow {f : P2} {ℓ : Valuation →+ ℤ} (hℓ : ℓ (valuation f) = 1) (n : ℕ) :
    projected f ℓ (f^n) = 0 := by
  change projectHom ℓ (valuation f) (valuation (f^n)) = _
  rw [valuation_pow, map_zsmul]
  have h : projectHom ℓ (valuation f) (valuation f) = 0 := project_direction hℓ
  rw [h, smul_zero]

def projectedSection (f : P2) (ℓ : Valuation →+ ℤ) (g : P2) : Option Valuation :=
  if g = 0 then none else some (projected f ℓ g)

def projectedPair (f : P2) (ℓ : Valuation →+ ℤ) (g : P2) : List Valuation :=
  [evenSection g, oddSection g].filterMap (projectedSection f ℓ)

theorem projected_children_pairs (f : P2) (ℓ : Valuation →+ ℤ) (g : P2) :
    (children f g).map (projected f ℓ) = projectedPair f ℓ g ++ projectedPair f ℓ (g*f) := by
  have h (l : List P2) : ((l.filter (· ≠ 0)).map trim).map (projected f ℓ) =
      l.filterMap (projectedSection f ℓ) := by
    induction l with
    | nil => rfl
    | cons q l ih =>
      by_cases hq : q = 0
      · have hfilter : l.filter (· ≠ 0) = (q::l).filter (· ≠ 0) := by simp [hq]
        rw [← hfilter, List.filterMap_cons, projectedSection, ite_eq_left hq]
        exact ih
      · have hfilter : (q::l).filter (· ≠ 0) = q :: l.filter (· ≠ 0) := by simp [hq]
        have htrim : projected f ℓ (trim q) = projected f ℓ q := by
          change projectHom ℓ (valuation f) (valuation (trim q)) = _
          rw [valuation_trim hq]
        rw [hfilter, List.map_cons, List.map_cons, htrim, ih, List.filterMap_cons,
          projectedSection, ite_eq_right hq]
  rw [children, h]
  change List.filterMap _ ([evenSection g, oddSection g] ++
    [evenSection (g*f), oddSection (g*f)]) = _
  exact List.filterMap_append

theorem sections_mul_square (g q : P2) :
    evenSection (g*q^2) = evenSection g * q ∧ oddSection (g*q^2) = oddSection g * q := by
  have he : g*q^2 = parts (evenSection g*q) (oddSection g*q) := by
    conv_lhs => rw [← parts_sections g, parts_mul]
  rw [he, section_even_parts, section_odd_parts]
  exact ⟨rfl, rfl⟩

private theorem section_match {f a' a H K : P2} (ℓ : Valuation →+ ℤ)
    (hH : H ≠ 0) (hK : K ≠ 0) (hEq : a' * K = a * H) :
    projectedSection f ℓ a' = (projectedSection f ℓ a).map
      (· + (projected f ℓ H - projected f ℓ K)) := by
  by_cases ha : a = 0
  · have hz : a' = 0 := by
      rw [ha, zero_mul] at hEq
      exact (mul_eq_zero.mp hEq).resolve_right hK
    simp [projectedSection, ha, hz]
  · have ha' : a' ≠ 0 := by
      intro hn
      rw [hn, zero_mul] at hEq
      exact mul_ne_zero ha hH hEq.symm
    simp [projectedSection, ha, ha']
    have he := congrArg (projected f ℓ) hEq
    rw [projected_mul ℓ ha' hK, projected_mul ℓ ha hH] at he
    exact eq_sub_of_add_eq he |>.trans (by abel)

private theorem pair_match {f a' a H K : P2} (ℓ : Valuation →+ ℤ)
    (hH : H ≠ 0) (hK : K ≠ 0) (hEq : a' * K^2 = a * H^2) :
    projectedPair f ℓ a' = (projectedPair f ℓ a).map
      (· + (projected f ℓ H - projected f ℓ K)) := by
  have he := congrArg evenSection hEq
  have ho := congrArg oddSection hEq
  rw [(sections_mul_square a' K).1, (sections_mul_square a H).1] at he
  rw [(sections_mul_square a' K).2, (sections_mul_square a H).2] at ho
  rw [projectedPair, projectedPair, List.map_filterMap]
  simp only [List.filterMap_cons, List.filterMap_nil, ← section_match ℓ hH hK he,
    ← section_match ℓ hH hK ho]

private theorem distribute_power_mod_two (g f H : P2) (n : ℕ) :
    g * f^n * H^2 = (g * f^(n%2)) * (f^(n/2)*H)^2 := by
  rw [mul_pow, ← pow_mul]
  calc
    _ = g * f^(n%2 + n/2*2) * H^2 := by congr 3; omega
    _ = _ := by rw [pow_add]; ring

private theorem projected_pairs_swap {f : P2} (ℓ : Valuation →+ ℤ) (g : P2) (n : ℕ) :
    (projectedPair f ℓ (g * f ^ (n % 2)) ++ projectedPair f ℓ (g * f ^ ((n+1) % 2))).Perm
      (projectedPair f ℓ g ++ projectedPair f ℓ (g*f)) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h
  · have h' : (n+1)%2 = 1 := by omega
    simp [h, h']
  · have h' : (n+1)%2 = 0 := by omega
    simpa [h, h'] using
      (List.perm_append_comm : (projectedPair f ℓ (g*f) ++ projectedPair f ℓ g).Perm _)

set_option maxHeartbeats 1200000 in
theorem translated_children {f g g' : P2}
    (hf : f.coeff 0 = 1) (hg : g.coeff 0 = 1) (hg' : g'.coeff 0 = 1)
    {ℓ : Valuation →+ ℤ} (hℓ : ℓ (valuation f) = 1)
    {h : Valuation} (hh : ℓ h = 0)
    (he : projected f ℓ g' = projected f ℓ g + (h+h)) :
    ((children f g').map (projected f ℓ)).Perm
      (((children f g).map (projected f ℓ)).map (·+h)) := by
  obtain ⟨r, H, K, hH, hK, hproj, hb⟩ := twice_translation_balance hf hg hg' hh he
  have hp : projected f ℓ H - projected f ℓ K = h := by
    have he : projectHom ℓ (valuation f) (valuation H - valuation K) = h := hproj
    rwa [map_sub] at he
  let p := r.toNat
  let n := (-r).toNat
  have hnF := coeff0_ne_zero hf
  have pairEq (b : ℕ) :
      projectedPair f ℓ (g' * f^((n+b)%2)) =
        (projectedPair f ℓ (g * f^((p+b)%2))).map (·+h) := by
    have hEq : g' * f^(n+b) * K^2 = g * f^(p+b) * H^2 := by
      rw [pow_add, pow_add]
      calc
        _ = (g' * f^n * K^2) * f^b := by ring
        _ = (g * f^p * H^2) * f^b := congrArg (· * f^b) hb
        _ = _ := by ring
    rw [distribute_power_mod_two g' f K (n+b), distribute_power_mod_two g f H (p+b)] at hEq
    have h1 := pair_match (f := f) ℓ (mul_ne_zero (pow_ne_zero _ hnF) hH)
      (mul_ne_zero (pow_ne_zero _ hnF) hK) hEq
    rwa [projected_mul ℓ (pow_ne_zero _ hnF) hH, projected_mul ℓ (pow_ne_zero _ hnF) hK,
      projected_fpow hℓ, projected_fpow hℓ, zero_add, zero_add, hp] at h1
  rw [projected_children_pairs, projected_children_pairs]
  have hs' := (projected_pairs_swap (f := f) ℓ g' n).symm
  have hs := (projected_pairs_swap (f := f) ℓ g p).map (·+h)
  apply hs'.trans
  have h0 := pairEq 0
  have h1 := pairEq 1
  simp only [Nat.add_zero] at h0 h1
  rw [h0, h1, ← List.map_append]
  exact hs

#print axioms twice_translation_balance
#print axioms translated_children

end
end Garbe
```

### `GarbeAffine.lean`

```lean
import GarbeTranslation

namespace Garbe
open Polynomial
noncomputable section

structure PrimitiveRule where
  f : P2
  constant : f.coeff 0 = 1
  degree : 0 < f.natDegree
  odd : oddSection f ≠ 0
  functional : Valuation →+ ℤ
  primitive : functional (valuation f) = 1

namespace PrimitiveRule
attribute [local instance] Classical.propDecidable

abbrev L (R : PrimitiveRule) := R.functional.ker

def state (R : PrimitiveRule) (g : P2) : R.L :=
  ⟨projected R.f R.functional g, project_ker R.primitive _⟩

def rootChildren (R : PrimitiveRule) (g : P2) : List R.L :=
  (children R.f g).map R.state

theorem state_one (R : PrimitiveRule) : R.state 1 = 0 := by
  apply Subtype.ext
  change projectHom R.functional (valuation R.f) (valuation 1) = 0
  have hv : valuation 1 = 0 := by rw [valuation_of_coeff0 (by simp : (1:P2).coeff 0 = 1), intExponents_one]
  rw [hv, map_zero]

theorem state_trim (R : PrimitiveRule) {g : P2} (hg : g ≠ 0) : R.state (trim g) = R.state g := by
  apply Subtype.ext
  change projectHom R.functional (valuation R.f) (valuation (trim g)) = _
  rw [valuation_trim hg]
  rfl

def residue (R : PrimitiveRule) (v : R.L) : Valuation := fun p => v.val p % 2

theorem residue_zero (R : PrimitiveRule) : R.residue 0 = 0 := by
  ext i
  change (0 : ℤ) % 2 = 0
  omega

theorem residue_add_double (R : PrimitiveRule) (v d : R.L) :
    R.residue (v+(d+d)) = R.residue v := by
  ext p
  change (v.val p + (d.val p+d.val p)) % 2 = v.val p % 2
  omega

theorem unique_half (R : PrimitiveRule) (v w : R.L) (h : R.residue v = R.residue w) :
    ∃! d : R.L, v = w+(d+d) := by
  let d : Valuation := fun p => (v.val p - w.val p) / 2
  have hd : v.val = w.val+(d+d) := by
    ext p
    have hp := congrFun h p
    change v.val p % 2 = w.val p % 2 at hp
    change v.val p = w.val p + ((v.val p - w.val p) / 2 + (v.val p - w.val p) / 2)
    omega
  have hd0 : R.functional d = 0 := by
    have hh := congrArg R.functional hd
    have hv : R.functional v.val = 0 := v.property
    have hw : R.functional w.val = 0 := w.property
    rw [map_add, map_add, hv, hw] at hh
    omega
  refine ⟨⟨d, hd0⟩, Subtype.ext hd, ?_⟩
  intro d' he
  apply Subtype.ext
  ext p
  have hp := congrArg (fun a : R.L => a.val p) he
  have hq := congrFun hd p
  change v.val p = w.val p + (d'.val p+d'.val p) at hp
  change v.val p = w.val p + (d p+d p) at hq
  change d'.val p = d p
  omega

def halfDiff (R : PrimitiveRule) (v w : R.L) : R.L :=
  if h : R.residue v = R.residue w then (R.unique_half v w h).exists.choose else 0

theorem halfDiff_spec (R : PrimitiveRule) {v w : R.L} (h : R.residue v = R.residue w) :
    v = w + (R.halfDiff v w + R.halfDiff v w) := by
  rw [halfDiff, dite_eq_left h]
  exact (R.unique_half v w h).exists.choose_spec

theorem halfDiff_add_double (R : PrimitiveRule) {v w : R.L}
    (h : R.residue v = R.residue w) (d : R.L) :
    R.halfDiff (v+(d+d)) w = R.halfDiff v w + d := by
  have h' : R.residue (v+(d+d)) = R.residue w := (R.residue_add_double v d).trans h
  have he := R.halfDiff_spec h'
  have he' := R.halfDiff_spec h
  rcases R.unique_half (v+(d+d)) w h' with ⟨_, _, huniq⟩
  have hb : v + (d+d) = w + ((R.halfDiff v w+d)+(R.halfDiff v w+d)) := by
    conv_lhs => rw [he']
    abel
  exact (huniq _ he).trans (huniq _ hb).symm

abbrev Residues (R : PrimitiveRule) := Set.range R.residue

def residueClass (R : PrimitiveRule) (v : R.L) : R.Residues := ⟨R.residue v, v, rfl⟩

def vertexCandidate (R : PrimitiveRule) (s : R.Residues) : Prop :=
  ∃ g : P2, IsVertex R.f g ∧ R.residue (R.state g) = s.val

def residueRepresentative (R : PrimitiveRule) (s : R.Residues) : R.L :=
  if s.val = 0 then 0
  else if h : R.vertexCandidate s then R.state h.choose
  else s.property.choose

def residueOffsets (R : PrimitiveRule) (s : R.Residues) : List R.L :=
  if s.val = 0 then R.rootChildren 1
  else if h : R.vertexCandidate s then R.rootChildren h.choose
  else [0, 0, 0, 0]

theorem residueRepresentative_spec (R : PrimitiveRule) (s : R.Residues) :
    R.residue (R.residueRepresentative s) = s.val := by
  unfold residueRepresentative
  split_ifs with h₀ h
  · rw [R.residue_zero, h₀]
  · exact h.choose_spec.2
  · exact s.property.choose_spec

def base (R : PrimitiveRule) (v : R.L) : R.L :=
  R.halfDiff v (R.residueRepresentative (R.residueClass v))

def next (R : PrimitiveRule) (v : R.L) : List R.L :=
  (R.residueOffsets (R.residueClass v)).map (· + R.base v)

def even (R : PrimitiveRule) (v : R.L) : Bool := decide (R.residue v = 0)

theorem next_affine (R : PrimitiveRule) (v d : R.L) :
    R.next (v+(d+d)) = (R.next v).map (·+d) := by
  have he : R.residueClass (v+(d+d)) = R.residueClass v := Subtype.ext (R.residue_add_double v d)
  have h := (R.residueRepresentative_spec (R.residueClass v)).symm
  simp only [next, base, he, R.halfDiff_add_double h, List.map_map, Function.comp_def, add_assoc]

theorem rootChildren_perm (R : PrimitiveRule) {g g' : P2}
    (hg : g.coeff 0 = 1) (hg' : g'.coeff 0 = 1)
    {d : R.L} (h : R.state g' = R.state g + (d+d)) :
    (R.rootChildren g').Perm ((R.rootChildren g).map (·+d)) := by
  have he := congrArg Subtype.val h
  have hp := translated_children R.constant hg hg' R.primitive d.property he
  apply (List.map_perm_map_iff Subtype.val_injective).mp
  simpa only [rootChildren, List.map_map, Function.comp_def, AddSubgroup.coe_add, state] using hp

theorem next_matches (R : PrimitiveRule) {g : P2} (hg : IsVertex R.f g) :
    (R.rootChildren g).Perm (R.next (R.state g)) := by
  let v := R.state g
  let s := R.residueClass v
  have h₁ : R.residue v = R.residue (R.residueRepresentative s) :=
    (R.residueRepresentative_spec s).symm
  have hs := R.halfDiff_spec h₁
  change (R.rootChildren g).Perm ((R.residueOffsets s).map (·+R.base v))
  unfold base
  change (R.rootChildren g).Perm ((R.residueOffsets s).map (·+R.halfDiff v (R.residueRepresentative s)))
  by_cases h : s.val = 0
  · simp only [residueOffsets, residueRepresentative, ite_eq_left h] at hs ⊢
    exact R.rootChildren_perm (g := 1) (by simp) hg.1 (by simpa only [R.state_one] using hs)
  · have hc : R.vertexCandidate s := ⟨g, hg, rfl⟩
    simp only [residueOffsets, residueRepresentative, ite_eq_right h, dite_eq_left hc] at hs ⊢
    exact R.rootChildren_perm hc.choose_spec.1.1 hg.1 hs

theorem even_of_residue (R : PrimitiveRule) {v : R.L} (h : R.residue v = 0) :
    ∃ d : R.L, v = d+d := by
  obtain ⟨d, hd, _⟩ := R.unique_half v 0 (h.trans R.residue_zero.symm)
  exact ⟨d, by simpa only [zero_add] using hd⟩

theorem residue_of_even (R : PrimitiveRule) {v : R.L} (h : ∃ d : R.L, v = d+d) :
    R.residue v = 0 := by
  obtain ⟨d, rfl⟩ := h
  simpa only [zero_add, R.residue_zero] using R.residue_add_double 0 d

theorem odd_length (R : PrimitiveRule) (v : R.L) (h : R.even v = false) :
    (R.next v).length = 4 := by
  have hz : (R.residueClass v).val ≠ 0 := of_decide_eq_false h
  rw [next, List.length_map, residueOffsets, ite_eq_right hz]
  split_ifs with hc
  · have hgc := hc.choose_spec
    have hnot : ¬∃ d : R.L, R.state hc.choose = d+d := by
      intro hd
      exact hz (hgc.2.symm.trans (R.residue_of_even hd))
    have hodd : ¬(oddSection hc.choose = 0 ∨ oddSection (hc.choose*R.f) = 0) := by
      intro he
      obtain ⟨d, hd, h⟩ := (projected_even_iff R.constant hgc.1.1 R.primitive).mpr he
      exact hnot ⟨⟨d, hd⟩, Subtype.ext h⟩
    push Not at hodd
    rw [rootChildren, List.length_map, child_length_four R.constant hgc.1.1 hodd.1 hodd.2]
  · rfl

def offsetA (R : PrimitiveRule) : R.L := R.state (evenSection R.f)
def offsetB (R : PrimitiveRule) : R.L := R.state (oddSection R.f)

theorem root_offsets (R : PrimitiveRule) :
    R.rootChildren 1 = [0, R.offsetA, R.offsetB] := by
  have he : evenSection (1 : P2) = 1 := by simpa [parts] using section_even_parts 1 0
  have ho : oddSection (1 : P2) = 0 := by simpa [parts] using section_odd_parts 1 0
  simp [rootChildren, children, rawChildren, he, ho, nonzero_even R.constant, R.odd,
    R.state_trim (show (1:P2) ≠ 0 by exact one_ne_zero), R.state_one,
    R.state_trim (nonzero_even R.constant), R.state_trim R.odd, offsetA, offsetB]

theorem even_list (R : PrimitiveRule) (v : R.L) (h : R.even v = true) :
    R.next v = [R.base v, R.base v + R.offsetA, R.base v + R.offsetB] := by
  unfold next residueOffsets
  have hz : (R.residueClass v).val = 0 := of_decide_eq_true h
  rw [ite_eq_left hz, R.root_offsets]
  simp [add_comm]

def affinePaths (R : PrimitiveRule) : ℕ → R.L → ℕ
  | 0, _ => 1
  | k+1, v => ((R.next v).map (R.affinePaths k)).sum

theorem affinePaths_spec (R : PrimitiveRule) (k : ℕ) (g : P2) (hg : IsVertex R.f g) :
    R.affinePaths k (R.state g) = paths R.f k g := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [affinePaths, paths, ← ((R.next_matches hg).map (R.affinePaths k)).sum_eq, rootChildren,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro q hq
    exact ih q (child_properties hg.2 hq)

#print axioms next_affine
#print axioms affinePaths_spec

end PrimitiveRule
end
end Garbe
```

### `GarbeGap.lean`

```lean
import GarbeAffine
import GarbeDeferred

namespace Garbe
open Polynomial Filter
open scoped Topology
noncomputable section

namespace PrimitiveRule

attribute [local instance] Classical.propDecidable

theorem cannot_divide_at_abs_coordinate (R : PrimitiveRule) {u : R.L} (hu : u ≠ 0) :
    ∃ t : ℕ, ¬ ∃ a : R.L, u = 2^t • a := by
  have h : u.val ≠ 0 := fun h => hu (Subtype.ext h)
  obtain ⟨p, hp⟩ : ∃ p : P2, u.val p ≠ 0 := by
    by_contra! hh
    exact h (funext hh)
  let t := (u.val p).natAbs
  refine ⟨t, ?_⟩
  rintro ⟨a, ha⟩
  have habs := congrArg (fun x : R.L => (x.val p).natAbs) ha
  change (u.val p).natAbs = ((2^t : ℕ) • a.val p).natAbs at habs
  rw [nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast] at habs
  have hpos : 0 < (u.val p).natAbs := Int.natAbs_pos.mpr hp
  have hapos : 0 < (a.val p).natAbs := by
    by_contra! hh
    rw [Nat.eq_zero_of_le_zero hh, mul_zero] at habs
    omega
  exact (Nat.lt_two_pow_self (n := t)).not_ge
    (by change 2 ^ t ≤ (u.val p).natAbs; rw [habs]; exact Nat.le_mul_of_pos_right _ hapos)

theorem deepest_offsets (R : PrimitiveRule) (h : R.offsetA ≠ 0 ∨ R.offsetB ≠ 0) :
    ∃ t : ℕ, ∃ a b : R.L, R.offsetA = 2^t • a ∧ R.offsetB = 2^t • b ∧
      (R.residue a ≠ 0 ∨ R.residue b ≠ 0) := by
  let Div (t : ℕ) := ∃ a b : R.L, R.offsetA = 2^t • a ∧ R.offsetB = 2^t • b
  have h0 : Div 0 := ⟨R.offsetA, R.offsetB, by simp, by simp⟩
  have hn : ∃ t, ¬ Div t := by
    rcases h with h | h
    · obtain ⟨t, ht⟩ := R.cannot_divide_at_abs_coordinate h
      exact ⟨t, fun ⟨a, _, ha, _⟩ => ht ⟨a, ha⟩⟩
    · obtain ⟨t, ht⟩ := R.cannot_divide_at_abs_coordinate h
      exact ⟨t, fun ⟨_, b, _, hb⟩ => ht ⟨b, hb⟩⟩
  let t := (Nat.find hn).pred
  have hpos : 0 < Nat.find hn := by
    by_contra! he
    exact Nat.find_spec hn (by simpa only [Nat.eq_zero_of_le_zero he] using h0)
  have ht : t + 1 = Nat.find hn := Nat.succ_pred_eq_of_pos hpos
  obtain ⟨a, b, ha, hb⟩ : Div t := not_not.mp (Nat.find_min hn (by omega))
  refine ⟨t, a, b, ha, hb, ?_⟩
  by_contra! he
  obtain ⟨a', ha'⟩ := R.even_of_residue he.1
  obtain ⟨b', hb'⟩ := R.even_of_residue he.2
  have hs : Div (t+1) := by
    refine ⟨a', b', ?_, ?_⟩
    · rw [ha, ha', pow_succ, mul_nsmul, two_nsmul, nsmul_add]
    · rw [hb, hb', pow_succ, mul_nsmul, two_nsmul, nsmul_add]
  exact Nat.find_spec hn (ht ▸ hs)

theorem due_odd (R : PrimitiveRule) (a b : R.L)
    (h : R.residue a ≠ 0 ∨ R.residue b ≠ 0) (u : R.L) :
    R.even u = false ∨ R.even (u+a) = false ∨ R.even (u+b) = false := by
  by_contra! hh
  simp only [Bool.not_eq_false] at hh
  obtain ⟨d, hd⟩ := R.even_of_residue (of_decide_eq_true hh.1)
  obtain ⟨e, he⟩ := R.even_of_residue (of_decide_eq_true hh.2.1)
  obtain ⟨j, hj⟩ := R.even_of_residue (of_decide_eq_true hh.2.2)
  have ha : a = (e-d)+(e-d) := by
    calc
      a = (u+a)-u := by abel
      _ = _ := by nth_rw 1 [he]; rw [hd]; abel
  have hb : b = (j-d)+(j-d) := by
    calc
      b = (u+b)-u := by abel
      _ = _ := by nth_rw 1 [hj]; rw [hd]; abel
  exact h.elim (fun h => h (R.residue_of_even ⟨_, ha⟩)) (fun h => h (R.residue_of_even ⟨_, hb⟩))

theorem base_zero (R : PrimitiveRule) : R.base 0 = 0 := by
  have h : (R.residueClass (0 : R.L)).val = 0 := R.residue_zero
  simp only [base, residueRepresentative, ite_eq_left h]
  obtain ⟨d, hd, hu⟩ := R.unique_half (0 : R.L) 0 rfl
  exact (hu _ (R.halfDiff_spec rfl)).trans (hu 0 (by simp)).symm

theorem offsets_of_rate_gt_three (R : PrimitiveRule) {rate : ℝ} (hr : HasGrowthRate R.f rate)
    (hgt : 3 < rate) : R.offsetA ≠ 0 ∨ R.offsetB ≠ 0 := by
  by_contra! h
  have he : R.even 0 = true := decide_eq_true R.residue_zero
  have hn : R.next 0 = [0,0,0] := by rw [R.even_list 0 he, R.base_zero, h.1, h.2, add_zero]
  have hcount (k : ℕ) : R.affinePaths k 0 = 3^k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [affinePaths, hn]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ih, pow_succ]
      omega
  have hgr : HasGrowthRate R.f 3 := by
    apply growth_of_geometric_bounds (lo := 1) (hi := (R.f.natDegree : ℝ))
      (by norm_num) (by norm_num) (by exact_mod_cast R.degree)
    intro k
    have hb := paths_mass_bounds R.f k 1 (vertex_one R.degree)
    rw [← R.affinePaths_spec _ _ (vertex_one R.degree), R.state_one, hcount, mass_one] at hb
    constructor
    · rw [one_mul]
      exact_mod_cast hb.1
    · exact_mod_cast hb.2
  exact hgt.ne' (growth_unique hr hgr)

theorem primitive_gap (R : PrimitiveRule) {rate : ℝ}
    (hr : HasGrowthRate R.f rate) (h : 3 < rate) : 1 + Real.sqrt 5 ≤ rate := by
  obtain ⟨t, a, b, ha, hb, hOdd⟩ := R.deepest_offsets (R.offsets_of_rate_gt_three hr h)
  let α : ℝ := 1+Real.sqrt 5
  let C : ℝ := α^(t+1)
  have hα : 0 < α := by dsimp [α]; positivity
  have hC : 0 < C := pow_pos hα _
  have hP (k : ℕ) :
      α^k ≤ C * (R.affinePaths k 0 : ℝ) := by
    apply deferred_geometric_bound R.next R.even R.base a b t (fun k v => R.affinePaths k v)
      R.next_affine (fun u hu => by rw [← ha, ← hb]; exact R.even_list u hu)
      R.odd_length (R.due_odd a b hOdd)
    · intro u
      simp [affinePaths]
    · intro k u
      rw [affinePaths, Nat.cast_list_sum]
      simp [List.map_map, Function.comp_def]
  have hmass (k : ℕ) : α^k ≤ C * (r R.f (2^k) : ℝ) := by
    have hb := (paths_mass_bounds R.f k 1 (vertex_one R.degree)).1
    rw [← R.affinePaths_spec _ _ (vertex_one R.degree), R.state_one, mass_one] at hb
    exact (hP k).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hb) hC.le)
  have hConst := (tendsto_const_nhds (x := C)).rpow
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) (Or.inl hC.ne')
  rw [Real.rpow_zero] at hConst
  have hh := hConst.mul hr
  rw [one_mul] at hh
  apply le_of_tendsto_of_tendsto' (tendsto_geometric_root hα.le) hh
  intro k
  change (α^k) ^ ((1:ℝ)/k) ≤ C ^ ((1:ℝ)/k) * (r R.f (2^k) : ℝ) ^ ((1:ℝ)/k)
  rw [← Real.mul_rpow hC.le (Nat.cast_nonneg _)]
  exact Real.rpow_le_rpow (pow_nonneg hα.le _) (hmass k) (by positivity)

end PrimitiveRule

theorem primitive_representative (f : P2) (hf : 2 ≤ f.support.card) :
    ∃ R : PrimitiveRule, Similar f R.f := by
  classical
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hf
  have hspec := trim_spec hf0
  have hsim : Similar f (trim f) := by
    apply Relation.EqvGen.symm
    by_cases h : f.natTrailingDegree = 0
    · have e : f = trim f := by simpa only [h, pow_zero, one_mul] using hspec.2
      rw [← e]
      exact Relation.EqvGen.refl _
    · have hs := Relation.EqvGen.rel _ _ (SimStep.shift (trim f) _ (Nat.pos_of_ne_zero h))
      exact Eq.mp (congrArg (Similar (trim f)) hspec.2.symm) hs
  have hw : 2 ≤ w (trim f) := by
    have h := congrArg w hspec.2
    rw [weight_shift] at h
    exact h ▸ hf
  have htd : 0 < (trim f).natDegree := by
    by_contra! h
    have he := eq_one_of_degree_zero hspec.1 (Nat.eq_zero_of_le_zero h)
    rw [he, weight_one] at hw
    omega
  let good (d : ℕ) := ∃ g : P2, g.coeff 0 = 1 ∧ 0 < g.natDegree ∧
    g.natDegree = d ∧ Similar f g
  have hex : ∃ d, good d := ⟨_, trim f, hspec.1, htd, rfl, hsim⟩
  obtain ⟨g, hg, hgd, hd, hsim⟩ := Nat.find_spec hex
  have hprim : exponentGcd g = 1 := by
    by_contra hn
    have he1 : g ≠ 1 := fun h => by rw [h, natDegree_one] at hgd; omega
    have he := exponentGcd_pos (coeff0_ne_zero hg) he1
    have htwo : 1 < exponentGcd g := by omega
    obtain ⟨q, hq⟩ := exponentGcd_root g (coeff0_ne_zero hg)
    have hq0 : q.coeff 0 = 1 := by
      apply binary_one
      intro hz
      have hEq : g.coeff 0 = (q^exponentGcd g).coeff 0 := congrArg (fun p : P2 => p.coeff 0) hq
      rw [show (q^exponentGcd g).coeff 0 = (q.coeff 0)^exponentGcd g from
        (constantCoeff (R := ZMod 2)).map_pow _ _, hz, zero_pow he.ne', hg] at hEq
      exact one_ne_zero hEq
    have hdeg : g.natDegree = exponentGcd g * q.natDegree := by
      conv_lhs => rw [hq, natDegree_pow]
    have hqdeg : 0 < q.natDegree := by
      by_contra! hz
      rw [Nat.eq_zero_of_le_zero hz, mul_zero] at hdeg
      omega
    have hlt : q.natDegree < Nat.find hex := by
      rw [← hd, hdeg]
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right htwo hqdeg
    apply Nat.find_min hex hlt
    refine ⟨q, hq0, hqdeg, rfl, Relation.EqvGen.trans _ _ _ hsim ?_⟩
    exact Relation.EqvGen.symm _ _ (hq ▸ Relation.EqvGen.rel _ _ (SimStep.pow q _ htwo))
  have ho : oddSection g ≠ 0 := by
    intro he
    have hs : g = (evenSection g)^2 := by rw [← parts_zero_right, ← he, parts_sections]
    have hdvd := exponentGcd_square (evenSection g)
    rw [← hs, hprim] at hdvd
    norm_num at hdvd
  obtain ⟨ℓ, hℓ⟩ := exists_valuation_functional g hg hprim
  exact ⟨⟨g, hg, hgd, ho, ℓ, hℓ⟩, hsim⟩

theorem garbe_gap (f : P2) (hf : 2 ≤ f.support.card) {rate : ℝ}
    (hr : HasGrowthRate f rate) (h : 3 < rate) : 1 + Real.sqrt 5 ≤ rate := by
  obtain ⟨R, hR⟩ := primitive_representative f hf
  exact R.primitive_gap ((growth_similarity hR rate).mp hr) h

#print axioms garbe_gap

end
end Garbe
```

### `GarbeReplay.lean`

```lean
import GarbeGap

namespace Garbe
open Polynomial
noncomputable section

namespace PrimitiveRule

structure Delay (R : PrimitiveRule) where
  t : ℕ
  a : R.L
  b : R.L
  ha : R.offsetA = 2 ^ t • a
  hb : R.offsetB = 2 ^ t • b
  odd : R.residue a ≠ 0 ∨ R.residue b ≠ 0

namespace Delay
variable {R : PrimitiveRule} (D : R.Delay)

abbrev Tag := Option (Fin 3)
abbrev Config (R : PrimitiveRule) := R.L × List Bool
abbrev Filled (R : PrimitiveRule) := R.L × List Tag

def offset (a b : R.L) (i : Tag) : R.L :=
  match i with
  | some 1 => a
  | some 2 => b
  | _ => 0

def effect (a b : R.L) : List Tag → R.L
  | [] => 0
  | i::is => offset a b i + (effect a b is + effect a b is)

theorem effect_append (a b : R.L) (is : List Tag) (i : Tag) :
    effect a b (is++[i]) = effect a b is + 2^is.length • offset a b i := by
  induction is with
  | nil => simp [effect]
  | cons j is ih =>
    simp only [List.cons_append, effect, ih, List.length_cons, pow_succ, mul_nsmul,
      two_nsmul]
    abel

def forget (s : Filled R) : Config R := (s.1, s.2.map Option.isSome)

def actual (s : Filled R) : R.L := s.1 + effect D.a D.b s.2

def label (j : Tag) (v : R.L) : Tag × R.L := (j, v)

def tagged (R : PrimitiveRule) (v : R.L) : List (Tag × R.L) :=
  if R.even v then
    [(some 0, R.base v), (some 1, R.base v + R.offsetA), (some 2, R.base v + R.offsetB)]
  else (R.next v).map (label none)

theorem tagged_map (v : R.L) : (tagged R v).map Prod.snd = R.next v := by
  by_cases h : R.even v = true
  · rw [tagged, ite_eq_left h, R.even_list v h]
    rfl
  · rw [tagged, ite_eq_right h, List.map_map]
    change List.map id (R.next v) = _
    exact List.map_id _

theorem even_add_double (v d : R.L) : R.even (v+(d+d)) = R.even v := by
  unfold even
  rw [R.residue_add_double]

theorem tagged_translate (v d : R.L) :
    tagged R (v+(d+d)) = (tagged R v).map (fun p => (p.1,p.2+d)) := by
  by_cases h : R.even v = true
  · have hbase : R.base (v+(d+d)) = R.base v+d := by
      have hh := R.next_affine v d
      rw [R.even_list _ ((even_add_double v d).trans h), R.even_list _ h] at hh
      exact (List.cons.inj hh).1
    rw [tagged, tagged, even_add_double, ite_eq_left h, ite_eq_left h, hbase]
    simp only [List.map_cons, List.map_nil, add_right_comm (R.base v) d]
  · rw [tagged, tagged, even_add_double, ite_eq_right h, ite_eq_right h, R.next_affine,
      List.map_map, List.map_map]
    rfl

def due (bit : Bool) : List Tag := if bit then [some 0, some 1, some 2] else [none]

theorem due_iff (bit : Bool) (j : Tag) : j ∈ due bit ↔ j.isSome = bit := by
  cases bit <;> cases j with
  | none => decide
  | some j => fin_cases j <;> decide

def successors (s : Config R) : List (Config R) :=
  match s.2 with
  | [] => []
  | i::is => (due i).flatMap fun z =>
    let v := s.1 + offset D.a D.b z
    if R.even v then [(R.base v, is++[true])]
    else (R.next v).map fun w => (w, is++[false])

theorem length_successors {s s' : Config R} (h : s' ∈ D.successors s) :
    s'.2.length = s.2.length := by
  obtain ⟨u, is⟩ := s
  cases is with
  | nil => simp [successors] at h
  | cons i is =>
    simp only [successors, List.mem_flatMap] at h
    obtain ⟨z, _, h⟩ := h
    split_ifs at h with hv
    · rcases List.mem_singleton.mp h with rfl
      simp
    · obtain ⟨w, _, rfl⟩ := List.mem_map.mp h
      simp

/-- A concrete tagged step can be replayed with the oldest queued choice disclosed. -/
theorem replay_step {u : R.L} {z : Tag} {zs : List Tag} (hL : zs.length = D.t)
    {j : Tag} {x : R.L}
    (h : (j,x) ∈ tagged R (D.actual (u,z::zs))) :
    ∃ v : R.L, D.actual (v,zs++[j]) = x ∧
      forget (v,zs++[j]) ∈ D.successors (forget (u,z::zs)) := by
  let v₀ := u + offset D.a D.b z
  let δ := effect D.a D.b zs
  have ha : D.actual (u,z::zs) = v₀+(δ+δ) := by simp [actual, effect, v₀, δ, add_assoc]
  rw [ha, tagged_translate, List.mem_map] at h
  obtain ⟨⟨j', y⟩, hy, hxy⟩ := h
  simp only [Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl, rfl⟩
  have hd : z ∈ due z.isSome := (due_iff _ _).mpr rfl
  by_cases he : R.even v₀ = true
  · rw [tagged, ite_eq_left he] at hy
    refine ⟨R.base v₀, ?_, ?_⟩
    · simp only [actual, effect_append, hL, δ]
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hy
      rcases hy with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · simp [offset]
      · rw [D.ha, show offset D.a D.b (some 1) = D.a from rfl]
        abel
      · rw [D.hb, show offset D.a D.b (some 2) = D.b from rfl]
        abel
    · have hj : j'.isSome = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hy
        rcases hy with (⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩) <;> rfl
      simp only [forget, List.map_cons, List.map_append, successors, List.mem_flatMap]
      exact ⟨z, hd, by rw [ite_eq_left he, hj]; exact List.mem_singleton_self _⟩
  · rw [tagged, ite_eq_right he, List.mem_map] at hy
    obtain ⟨w, hw, hj⟩ := hy
    simp only [label, Prod.mk.injEq] at hj
    rcases hj with ⟨rfl, rfl⟩
    refine ⟨w, by simp [actual,effect_append,offset,δ], ?_⟩
    simp only [forget, List.map_cons, List.map_append, successors, List.mem_flatMap]
    exact ⟨z, hd, by rw [ite_eq_right he]; exact List.mem_map.mpr ⟨w,hw,rfl⟩⟩

private theorem split_filled {xs : List Tag} {is : List Bool} {i : Bool}
    (h : xs.map Option.isSome = is++[i]) :
    ∃ zs j, xs = zs++[j] ∧ zs.map Option.isSome = is ∧ j.isSome = i := by
  induction is generalizing xs with
  | nil =>
    cases xs with
    | nil => simp at h
    | cons j js =>
      simp only [List.nil_append, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at h
      obtain ⟨hj,rfl⟩ := h
      exact ⟨[], j, rfl, rfl, hj⟩
  | cons k is ih =>
    cases xs with
    | nil => simp at h
    | cons z zs =>
      simp only [List.cons_append, List.map_cons, List.cons.injEq] at h
      obtain ⟨ys,j,rfl,hys,hj⟩ := ih h.2
      exact ⟨z::ys, j, rfl, by simp [hys,h.1], hj⟩

/-- Every choice of the still pending labels can be lifted back through a postponed step. -/
theorem lift_step {s : Config R} {s' : Filled R}
    (h : forget s' ∈ D.successors s) (hL : s.2.length = D.t+1) :
    ∃ q : Filled R, forget q = s ∧
      ∃ j : Tag, (j, D.actual s') ∈ tagged R (D.actual q) ∧ s'.2 = q.2.drop 1 ++ [j] := by
  obtain ⟨u,is⟩ := s
  obtain ⟨v,ys⟩ := s'
  cases is with
  | nil => simp [successors] at h
  | cons i is =>
    simp only [forget, successors, List.mem_flatMap] at h
    obtain ⟨z,hz,h⟩ := h
    let v₀ := u + offset D.a D.b z
    have hz' := (due_iff _ _).mp hz
    change (v, ys.map Option.isSome) ∈ (if R.even v₀ then [(R.base v₀, is++[true])]
      else (R.next v₀).map fun w => (w, is++[false])) at h
    by_cases he : R.even v₀ = true
    · rw [ite_eq_left he, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl,h⟩ := h
      obtain ⟨zs,j,rfl,hzs,hj⟩ := split_filled h
      have hlen : zs.length = D.t := by
        have hlen := congrArg List.length hzs
        simp only [List.length_map] at hlen
        simp at hL
        omega
      refine ⟨(u,z::zs), ?_, j, ?_, rfl⟩
      · simp [forget,hzs,hz']
      have ha : D.actual (u,z::zs) = v₀+(effect D.a D.b zs+effect D.a D.b zs) := by
        simp [actual,effect,v₀,add_assoc]
      rw [ha, tagged_translate, tagged, ite_eq_left he]
      simp only [actual, effect_append, hlen]
      cases j with
      | none => cases hj
      | some j =>
        fin_cases j <;> simp [offset, D.ha, D.hb, add_right_comm, add_assoc]
    · rw [ite_eq_right he, List.mem_map] at h
      obtain ⟨w,hw,h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl,h⟩ := h
      obtain ⟨zs,j,rfl,hzs,hj⟩ := split_filled h.symm
      have hj' : j = none := by cases j <;> simp_all
      subst j
      refine ⟨(u,z::zs), by simp [forget,hzs,hz'], none, ?_, rfl⟩
      have ha : D.actual (u,z::zs) = v₀+(effect D.a D.b zs+effect D.a D.b zs) := by
        simp [actual,effect,v₀,add_assoc]
      rw [ha, tagged_translate, tagged, ite_eq_right he, List.map_map]
      exact List.mem_map.mpr ⟨w,hw,by simp [label,actual,effect_append,offset]⟩

inductive Walk {A : Type*} (next : A → List A) : ℕ → A → A → Prop
  | nil (a) : Walk next 0 a a
  | snoc {n a b c} : Walk next n a b → c ∈ next b → Walk next (n+1) a c

inductive TaggedWalk (R : PrimitiveRule) : List Tag → R.L → R.L → Prop
  | nil (a) : TaggedWalk R [] a a
  | snoc {ls a b c j} : TaggedWalk R ls a b → (j,c) ∈ tagged R b →
      TaggedWalk R (ls++[j]) a c

def initial (D : R.Delay) : Config R := (0,List.replicate (D.t+1) false)

theorem walk_len {n : ℕ} {s : Config R} (h : Walk D.successors n D.initial s) :
    s.2.length = D.t+1 := by
  generalize he : D.initial = q at h
  induction h with
  | nil => rw [← he]; simp [initial]
  | snoc h hs ih => exact (D.length_successors hs).trans (ih he)

theorem replay {ls : List Tag} {s : Filled R} {x : R.L}
    (hL : s.2.length = D.t+1)
    (h : TaggedWalk R ls (D.actual s) x) :
    ∃ q : Filled R, Walk D.successors ls.length (forget s) (forget q) ∧
      D.actual q = x ∧ q.2 = (s.2++ls).drop ls.length := by
  generalize he : D.actual s = y at h
  induction h with
  | nil => exact ⟨s, Walk.nil _, he, by simp⟩
  | @snoc ls a b c j h₁ h₂ ih =>
    obtain ⟨q,hq,hb,hls⟩ := ih he
    have hlen : q.2.length = D.t+1 := by
      rw [hls, List.length_drop, List.length_append]
      omega
    obtain ⟨u,qs⟩ := q
    cases qs with
    | nil => simp at hlen
    | cons z zs =>
      have hlen' : zs.length = D.t := by simp at hlen; omega
      rw [← hb] at h₂
      obtain ⟨v,hv,hm⟩ := D.replay_step hlen' h₂
      refine ⟨(v,zs++[j]), by simpa using Walk.snoc hq hm, hv, ?_⟩
      have hdrop : List.drop (ls.length+1) (s.2++ls) = zs := by
        rw [← List.drop_drop, ← hls]
        rfl
      rw [List.length_append, List.length_singleton, ← List.append_assoc, List.drop_append,
        hdrop, show ls.length+1-(s.2++ls).length = 0 by simp; omega, List.drop_zero]

theorem lift_walk {n : ℕ} {s : Filled R} (h : Walk D.successors n D.initial (forget s)) :
    ∃ ls : List Tag, ls.length = n ∧ TaggedWalk R ls 0 (D.actual s) ∧
      s.2 = ((List.replicate (D.t+1) none)++ls).drop n := by
  generalize he : forget s = x at h
  generalize hstart : D.initial = x₀ at h
  induction h generalizing s with
  | nil =>
    rw [← hstart] at he
    obtain ⟨u,ls⟩ := s
    simp only [forget, initial, Prod.mk.injEq] at he
    obtain ⟨rfl,he⟩ := he
    have hh : ls = List.replicate (D.t+1) none := by
      generalize D.t+1 = k at he ⊢
      induction k generalizing ls with
      | zero => simpa using he
      | succ k ih =>
        cases ls with
        | nil => simp at he
        | cons j js =>
          cases j <;> simp_all [List.replicate_succ]
    have ha (k : ℕ) : effect D.a D.b (List.replicate k none) = 0 := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ,effect,offset,ih]
    refine ⟨[],rfl,?_,by simpa using hh⟩
    simpa [actual,hh,ha] using TaggedWalk.nil (R := R) 0
  | @snoc n a b c hab hbc ih =>
    rw [← he] at hbc
    have hb : Walk D.successors n D.initial b := by rw [hstart]; exact hab
    obtain ⟨q,hq,j,hj,hslots⟩ := D.lift_step hbc (D.walk_len hb)
    obtain ⟨ls,hlen,hls,hqslots⟩ := ih hq hstart
    refine ⟨ls++[j],by simp [hlen],TaggedWalk.snoc hls hj,?_⟩
    rw [hslots,hqslots,List.drop_drop, ← List.append_assoc]
    conv_rhs => rw [List.drop_append]
    have heq : n+1-(List.replicate (D.t+1) none++ls).length = 0 := by simp [hlen]
    rw [heq, List.drop_zero]

#print axioms replay
#print axioms lift_walk

end Delay
end PrimitiveRule
end
end Garbe
```

### `GarbeConnect.lean`

```lean
import GarbeReplay

namespace Garbe.PrimitiveRule.Delay
open Garbe Polynomial

noncomputable section
attribute [local instance] Classical.propDecidable
variable {R : PrimitiveRule} (D : R.Delay)

theorem walk_append {A : Type*} {next : A → List A} {j k : ℕ} {a b c : A}
    (h : Walk next j a b) (h' : Walk next k b c) : Walk next (j+k) a c := by
  induction h' with
  | nil => exact h
  | snoc _ hm ih => rw [← Nat.add_assoc]; exact Walk.snoc (ih h) hm

theorem tagged_append {ls ts : List Tag} {u v w : R.L}
    (h : TaggedWalk R ls u v) (h' : TaggedWalk R ts v w) : TaggedWalk R (ls++ts) u w := by
  induction h' with
  | nil => simpa only [List.append_nil] using h
  | snoc _ hm ih => rw [← List.append_assoc]; exact TaggedWalk.snoc (ih h) hm

theorem tagged_split {ls : List Tag} {a b : R.L} (h : TaggedWalk R ls a b)
    (k : ℕ) (hk : k ≤ ls.length) :
    ∃ c, TaggedWalk R (ls.take k) a c ∧ TaggedWalk R (ls.drop k) c b := by
  induction h with
  | nil => simp only [List.take_nil, List.drop_nil]; exact ⟨_, TaggedWalk.nil _, TaggedWalk.nil _⟩
  | @snoc ls a b c j h₁ h₂ ih =>
    by_cases hh : k ≤ ls.length
    · obtain ⟨d, hd, hd'⟩ := ih hh
      refine ⟨d, ?_, ?_⟩
      · simpa only [List.take_append_of_le_length hh] using hd
      · rw [List.drop_append, Nat.sub_eq_zero_of_le hh, List.drop_zero]
        exact TaggedWalk.snoc hd' h₂
    · have heq : k = (ls++[j]).length := by simp at hk ⊢; omega
      rw [heq, List.take_length, List.drop_length]
      exact ⟨c, TaggedWalk.snoc h₁ h₂, TaggedWalk.nil _⟩

def Realized (R : PrimitiveRule) (v : R.L) : Prop :=
  ∃ g : P2, IsVertex R.f g ∧ R.state g = v

theorem realized_next {u v : R.L} (h : Realized R u) (hv : v ∈ R.next u) :
    Realized R v := by
  obtain ⟨g,hg,rfl⟩ := h
  have he := (R.next_matches hg).mem_iff.mpr hv
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp he
  exact ⟨q,child_properties hg.2 hq,rfl⟩

theorem tagged_realized {ls : List Tag} {a b : R.L}
    (h : TaggedWalk R ls a b) (ha : Realized R a) : Realized R b := by
  induction h with
  | nil => exact ha
  | snoc _ hm ih =>
    apply realized_next (ih ha)
    rw [← tagged_map]
    exact List.mem_map.mpr ⟨_,hm,rfl⟩

theorem tagged_of_route {g q : P2} {n : ℕ} (hg : IsVertex R.f g) (h : Route R.f n g q) :
    ∃ ls : List Tag, ls.length = n ∧ TaggedWalk R ls (R.state g) (R.state q) := by
  induction h with
  | nil => exact ⟨[],rfl,TaggedWalk.nil _⟩
  | @cons n g h q hm _ ih =>
    obtain ⟨ls,hl,hr⟩ := ih (child_properties hg.2 hm)
    have hv : R.state h ∈ R.next (R.state g) := (R.next_matches hg).mem_iff.mp
      (List.mem_map.mpr ⟨h,hm,rfl⟩)
    rw [← tagged_map] at hv
    obtain ⟨⟨j,v⟩,hj,he⟩ := List.mem_map.mp hv
    dsimp at he
    subst v
    refine ⟨j::ls,by simp [hl],?_⟩
    exact tagged_append (TaggedWalk.snoc (TaggedWalk.nil _) hj) hr

def zeroFill (u : Config R) : Filled R :=
  (u.1, u.2.map fun x => if x then some 0 else none)

@[simp] theorem forget_zeroFill (s : Config R) : forget (zeroFill s) = s := by
  have he : (fun x : Bool => (if x then some (0 : Fin 3) else none).isSome) = id := by
    funext x
    cases x <;> rfl
  simp [forget,zeroFill,List.map_map,Function.comp_def,he]

@[simp] theorem actual_zeroFill (s : Config R) : D.actual (zeroFill s) = s.1 := by
  have he (ls : List Bool) :
      effect D.a D.b (ls.map fun x => if x then some 0 else none) = 0 := by
    induction ls with
    | nil => rfl
    | cons i is ih => cases i <;> simp [effect,offset,ih]
  simp [actual,zeroFill,he]

theorem realized_config {n : ℕ} {s : Config R}
    (h : Walk D.successors n D.initial s) : Realized R s.1 := by
  have h' : Walk D.successors n D.initial (forget (zeroFill s)) := by simpa using h
  obtain ⟨ls,_,hl,_⟩ := D.lift_walk h'
  rw [D.actual_zeroFill] at hl
  exact tagged_realized hl ⟨1,vertex_one R.degree,R.state_one⟩

theorem replay_last {m n : ℕ} {s s' : Config R}
    (hs : Walk D.successors m D.initial s) (hs' : Walk D.successors n D.initial s')
    (hn : D.t+1 ≤ n) :
    Walk D.successors (R.f.natDegree+n) s s' := by
  obtain ⟨g,hg,hstate⟩ := D.realized_config hs
  obtain ⟨ls,hls,hw₀⟩ := tagged_of_route hg
    (route_to_one R.f R.f.natDegree g hg.1 hg.2.le)
  rw [hstate,R.state_one] at hw₀
  have h' : Walk D.successors n D.initial (forget (zeroFill s')) := by simpa using hs'
  obtain ⟨ts,hts,hw,hq⟩ := D.lift_walk h'
  let k := n-(D.t+1)
  have hk : k ≤ ts.length := by dsimp [k]; omega
  have htail : (ts.drop k).length = D.t+1 := by rw [List.length_drop,hts]; dsimp [k]; omega
  obtain ⟨v,hp,hq'⟩ := tagged_split hw k hk
  have hroute := tagged_append (tagged_append hw₀ hp) hq'
  rw [D.actual_zeroFill] at hroute
  have hroute' : TaggedWalk R ((ls++ts.take k)++ts.drop k) (D.actual (zeroFill s)) s'.1 := by
    simpa using hroute
  have hlen : (zeroFill s).2.length = D.t+1 := by simpa [zeroFill] using D.walk_len hs
  obtain ⟨q,hq₀,hend,hslots⟩ := D.replay hlen hroute'
  have hpref : (ls++ts.take k).length = R.f.natDegree+k := by
    rw [List.length_append,hls,List.length_take,Nat.min_eq_left hk]
  have htotal : ((ls++ts.take k)++ts.drop k).length = R.f.natDegree+n := by
    rw [List.length_append,hpref,htail]
    dsimp [k]
    omega
  have hlast : q.2 = ts.drop k := by
    rw [hslots,htotal]
    have hh : ((zeroFill s).2++(ls++ts.take k)).length = R.f.natDegree+n := by
      rw [List.length_append,hlen,hpref]
      dsimp [k]
      omega
    rw [← List.append_assoc,← hh,List.drop_append]
    simp
  have hslots' : (zeroFill s').2 = ts.drop k := by
    rw [hq,List.drop_append]
    have hh : ((List.replicate (D.t+1) none : List Tag)).length ≤ n := by simpa using hn
    rw [List.drop_eq_nil_of_le hh,List.nil_append,List.length_replicate]
  have hq' : q = zeroFill s' := by
    apply Prod.ext
    · have he : D.actual (zeroFill s') = s'.1 := D.actual_zeroFill _
      rw [← he, actual,actual] at hend
      rw [hlast,← hslots'] at hend
      exact add_right_cancel hend
    · exact hlast.trans hslots'.symm
  simpa only [htotal,hq',forget_zeroFill] using hq₀

theorem early_config {n : ℕ} {s : Config R}
    (h : Walk D.successors n D.initial s) (hn : n ≤ D.t+1) :
    s = (0,List.replicate (D.t+1-n) false ++ List.replicate n true) := by
  generalize hs : D.initial = s₀ at h
  induction h with
  | nil => simp [← hs,initial]
  | @snoc n a b c h₀ h₁ ih =>
    have hb := ih (by omega) hs
    have hlen : D.t+1-n = (D.t+1-(n+1))+1 := by omega
    rw [hb,hlen,List.replicate_succ,List.cons_append] at h₁
    have he : R.even 0 = true := by
      unfold even
      rw [R.residue_zero]
      exact decide_eq_true rfl
    simp [successors,due,offset,he,R.base_zero] at h₁
    rw [h₁]
    simp [← List.replicate_succ']

#print axioms replay_last

end
end Garbe.PrimitiveRule.Delay
```

### `GarbeSharp.lean`

```lean
import GarbeConnect

namespace Garbe.PrimitiveRule.Delay
open Garbe Polynomial Filter
open scoped Topology

noncomputable section
variable {R : PrimitiveRule} (D : R.Delay)

def alpha : ℝ := 1+Real.sqrt 5
theorem alpha_ge_one : 1 ≤ alpha := le_add_of_nonneg_right (Real.sqrt_nonneg _)
theorem alpha_pos : 0 < alpha := zero_lt_one.trans_le alpha_ge_one
theorem alpha_lt_four : alpha < 4 := by
  unfold alpha
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
theorem alpha_sq : alpha^2 = 2*alpha+4 := by
  unfold alpha
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
theorem alpha_gt_three : 3 < alpha := by
  unfold alpha
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]

def weight (s : Config R) : ℝ := alpha ^ s.2.count true

def reward (R : PrimitiveRule) (v : R.L) : ℝ := if R.even v then alpha else 4

theorem reward_ge (v : R.L) : alpha ≤ reward R v := by
  unfold reward
  split_ifs
  · rfl
  · exact alpha_lt_four.le

private theorem sum_flatMap {A B : Type*} (l : List A) (g : A → List B) (F : B → ℝ) :
    ((l.flatMap g).map F).sum = (l.map fun x => ((g x).map F).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons]

private theorem sum_scale {A : Type*} (l : List A) (F : A → ℝ) (z : ℝ) :
    (l.map fun x => z * F x).sum = z * (l.map F).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

theorem weight_step_formula (u : R.L) (i : Bool) (is : List Bool) :
    ((D.successors (u,i::is)).map weight).sum =
      alpha^is.count true * disclose i D.a D.b (reward R) u := by
  simp only [successors, sum_flatMap]
  have h (j : Tag) :
      (List.map weight
        (if R.even (u + offset D.a D.b j) then [(R.base (u+offset D.a D.b j),is++[true])]
          else (R.next (u+offset D.a D.b j)).map fun v => (v,is++[false]))).sum =
      alpha^is.count true * reward R (u+offset D.a D.b j) := by
    cases hv : R.even (u+offset D.a D.b j)
    · simp only [hv, Bool.false_eq_true, ite_false, List.map_map, Function.comp_def, weight,
        List.count_append, List.count_singleton, reward]
      simp [R.odd_length _ hv]
      ring
    · simp [hv, weight, List.count_append, pow_succ, reward]
  simp_rw [h, sum_scale]
  cases i <;> simp [due, offset, disclose, add_assoc]

def Strict (s : Config R) : Prop := alpha * weight s < ((D.successors s).map weight).sum

theorem weight_step_ge (s : Config R) (h : s.2.length = D.t+1) :
    alpha * weight s ≤ ((D.successors s).map weight).sum := by
  obtain ⟨u,is⟩ := s
  cases is with
  | nil => simp at h
  | cons i is =>
    rw [D.weight_step_formula]
    cases i
    · simpa [weight,disclose,mul_comm] using
        mul_le_mul_of_nonneg_left (reward_ge u) (pow_nonneg alpha_pos.le (is.count true))
    · have he : alpha * weight (u,true::is) = alpha^is.count true * (2*alpha+4) := by
        simp only [weight,List.count_cons_self,pow_succ,← alpha_sq]
        ring
      rw [he]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg alpha_pos.le _)
      change 2*alpha+4 ≤ reward R u + reward R (u+D.a) + reward R (u+D.b)
      rcases R.due_odd D.a D.b D.odd u with hx | hx | hx
      · rw [show reward R u = 4 by simp [reward,hx]]
        linarith [reward_ge (u+D.a),reward_ge (u+D.b)]
      · rw [show reward R (u+D.a) = 4 by simp [reward,hx]]
        linarith [reward_ge u,reward_ge (u+D.b)]
      · rw [show reward R (u+D.b) = 4 by simp [reward,hx]]
        linarith [reward_ge u,reward_ge (u+D.a)]

theorem not_strict_early {n : ℕ} {s : Config R}
    (hs : Walk D.successors n D.initial s) (hn : n < D.t+1) : ¬D.Strict s := by
  have hh := D.early_config hs hn.le
  have hl : D.t+1-n = (D.t-n)+1 := by omega
  have he : R.even 0 = true := by
    classical exact decide_eq_true R.residue_zero
  rw [hh,hl,List.replicate_succ,List.cons_append,Strict,D.weight_step_formula]
  simp [weight,disclose,reward,he,mul_comm]

def continuation (D : R.Delay) (k : ℕ) (s : Config R) : ℝ :=
  pendingSum D.a D.b s.2 (fun v => R.affinePaths k v) s.1

theorem continuation_step (s : Config R) (hL : s.2.length = D.t+1) (k : ℕ) :
    D.continuation (k+1) s = ((D.successors s).map (D.continuation k)).sum := by
  obtain ⟨u,is⟩ := s
  cases is with
  | nil => simp at hL
  | cons i is =>
    have hlen : is.length = D.t := by simp at hL; omega
    have hp : (fun v => (R.affinePaths (k+1) v : ℝ)) =
        (fun v => ((R.next v).map (fun w => (R.affinePaths k w : ℝ))).sum) := by
      funext v
      rw [affinePaths,Nat.cast_list_sum]
      simp [List.map_map,Function.comp_def]
    rw [continuation,hp]
    change pendingSum D.a D.b (i::is) _ u = _
    rw [pendingSum_step R.next R.even R.base R.next_affine D.a D.b is i
      (fun v hv => by rw [hlen,← D.ha,← D.hb]; exact R.even_list _ hv)]
    simp only [successors,sum_flatMap]
    have hh (z : Tag) :
        (List.map (D.continuation k)
          (if R.even (u+offset D.a D.b z) then [(R.base (u+offset D.a D.b z),is++[true])]
            else (R.next (u+offset D.a D.b z)).map (fun w => (w,is++[false])))).sum =
        (if R.even (u+offset D.a D.b z)
          then pendingSum D.a D.b (is++[true]) (fun v => (R.affinePaths k v : ℝ)) (R.base (u+offset D.a D.b z))
          else ((R.next (u+offset D.a D.b z)).map
            (pendingSum D.a D.b (is++[false]) (fun v => (R.affinePaths k v : ℝ)))).sum) := by
      split_ifs <;> simp [continuation,List.map_map,Function.comp_def]
    simp_rw [hh]
    cases i <;> simp [disclose,due,offset,add_assoc]

theorem continuation_zero_ge (s : Config R) : 1 ≤ D.continuation 0 s := by
  obtain ⟨u,is⟩ := s
  unfold continuation
  simp only [affinePaths,Nat.cast_one]
  generalize D.a = a
  generalize D.b = b
  induction is generalizing a b u with
  | nil => simp [pendingSum]
  | cons i is ih =>
    cases i
    · exact ih _ _ _
    · change 1 ≤ pendingSum (a+a) (b+b) is (fun _ => (1:ℝ)) u +
        pendingSum (a+a) (b+b) is (fun _ => (1:ℝ)) (u+a) +
        pendingSum (a+a) (b+b) is (fun _ => (1:ℝ)) (u+b)
      linarith [ih u (a+a) (b+b),ih (u+a) (a+a) (b+b),ih (u+b) (a+a) (b+b)]

theorem continuation_initial (k : ℕ) : D.continuation k D.initial = R.affinePaths k 0 := by
  change pendingSum D.a D.b (List.replicate (D.t+1) false) _ 0 = _
  have hh (n : ℕ) (a b : R.L) : pendingSum a b (List.replicate n false)
      (fun v => (R.affinePaths k v : ℝ)) 0 = R.affinePaths k 0 := by
    induction n generalizing a b with
    | zero => rfl
    | succ n ih => exact ih _ _
  exact hh _ _ _

section Iteration
variable {A : Type*} (next : A → List A)

def iterateSum (F : A → ℝ) : ℕ → A → ℝ
  | 0, s => F s
  | k+1, s => ((next s).map (iterateSum F k)).sum

theorem iterateSum_add_steps (F : A → ℝ) (j k : ℕ) (s : A) :
    iterateSum next F (j+k) s = iterateSum next (iterateSum next F k) j s := by
  induction j generalizing s with
  | zero => simp [iterateSum]
  | succ j ih => rw [Nat.succ_add,iterateSum,iterateSum,funext ih]

theorem iterateSum_linear (F G : A → ℝ) (k : ℕ) (c : ℝ) (s : A) :
    iterateSum next (fun x => c*F x+G x) k s =
      c*iterateSum next F k s + iterateSum next G k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [iterateSum,iterateSum,iterateSum,funext ih,list_sum_pointwise_add,sum_scale]

private theorem real_list_le (l : List A) {F G : A → ℝ} (h : ∀ x ∈ l, F x ≤ G x) :
    (l.map F).sum ≤ (l.map G).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    exact add_le_add (h _ (List.mem_cons_self ..)) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem iterateSum_mono {ok : A → Prop} (hc : ∀ x, ok x → ∀ y ∈ next x, ok y)
    {F G : A → ℝ} (hle : ∀ s, ok s → F s ≤ G s) (k : ℕ) {s : A} (hs : ok s) :
    iterateSum next F k s ≤ iterateSum next G k s := by
  induction k generalizing s with
  | zero => exact hle _ hs
  | succ k ih => exact real_list_le _ (fun y hy => ih (hc _ hs _ hy))

private theorem real_child_le_sum (l : List A) {F : A → ℝ} (h : ∀ x ∈ l, 0 ≤ F x)
    {y : A} (hy : y ∈ l) : F y ≤ (l.map F).sum := by
  induction l with
  | nil => cases hy
  | cons x l ih =>
    have hl := fun y hy => h y (List.mem_cons_of_mem x hy)
    rcases List.mem_cons.mp hy with rfl | hy
    · have hh := real_list_le l (F := fun _ => 0) (G := F) hl
      simp at hh
      simpa only [List.map_cons,List.sum_cons] using le_add_of_nonneg_right hh
    · exact (ih hl hy).trans (le_add_of_nonneg_left (h x (List.mem_cons_self ..)))

theorem iterateSum_walk {ok : A → Prop} (hc : ∀ x, ok x → ∀ y ∈ next x, ok y)
    (F : A → ℝ) (hF : ∀ s, ok s → 0 ≤ F s) {j : ℕ} {s q : A}
    (hs : ok s) (h : Walk next j s q) :
    ok q ∧ F q ≤ iterateSum next F j s := by
  induction h generalizing F with
  | nil => exact ⟨hs,le_rfl⟩
  | @snoc j a b c h₁ h₂ ih =>
    have hF' (x : A) (hx : ok x) : 0 ≤ iterateSum next F 1 x := by
      have hh := real_list_le (next x) (F := fun _ => 0) (G := F) (fun y hy => hF y (hc x hx y hy))
      simpa [iterateSum] using hh
    have hb := ih F hF hs
    have hI := ih (iterateSum next F 1) hF' hs
    refine ⟨hc _ hb.1 _ h₂, ?_⟩
    rw [iterateSum_add_steps]
    exact (real_child_le_sum _ (fun y hy => hF y (hc _ hb.1 y hy)) h₂).trans hI.2

end Iteration

def Accessible (s : Config R) := ∃ n, Walk D.successors n D.initial s

theorem accessible_step (s : Config R) (hs : D.Accessible s)
    (q : Config R) (hq : q ∈ D.successors s) : D.Accessible q := by
  obtain ⟨n,hn⟩ := hs
  exact ⟨n+1,Walk.snoc hn hq⟩

theorem weighted_exp (k : ℕ) (s : Config R) (hs : D.Accessible s) :
    alpha^k * weight s ≤ iterateSum D.successors weight k s := by
  induction k generalizing s with
  | zero => simp [iterateSum]
  | succ k ih =>
    rw [pow_succ,mul_assoc,iterateSum]
    obtain ⟨n,hn⟩ := hs
    have hb := mul_le_mul_of_nonneg_left (D.weight_step_ge s (D.walk_len hn))
      (pow_nonneg alpha_pos.le k)
    rw [← sum_scale] at hb
    exact hb.trans (real_list_le _ (fun x hx => ih x (D.accessible_step s ⟨n,hn⟩ x hx)))

theorem iteration_continuation (k : ℕ) (s : Config R) (hs : D.Accessible s) :
    iterateSum D.successors (D.continuation 0) k s = D.continuation k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    obtain ⟨n,hn⟩ := hs
    rw [iterateSum,D.continuation_step s (D.walk_len hn)]
    congr 1
    exact List.map_congr_left (fun x hx => ih x (D.accessible_step s ⟨n,hn⟩ x hx))

theorem no_strict_at_alpha (hr : HasGrowthRate R.f alpha)
    {s₀ : Config R} (hs₀ : D.Accessible s₀) : ¬ D.Strict s₀ := by
  intro hs
  obtain ⟨n,hn⟩ := hs₀
  have hn' : D.t+1 ≤ n := by
    by_contra! h
    exact D.not_strict_early hn h hs
  let K := R.f.natDegree+n
  let δ (s : Config R) := iterateSum D.successors weight 1 s - alpha*weight s
  have hδ (s : Config R) (hs : D.Accessible s) : 0 ≤ δ s := by
    obtain ⟨m,hm⟩ := hs
    exact sub_nonneg.mpr (D.weight_step_ge s (D.walk_len hm))
  have hδ0 : 0 < δ s₀ := sub_pos.mpr hs
  let C := alpha^(D.t+1)
  have hC : 0 < C := pow_pos alpha_pos _
  let B := alpha^(K+1)+δ s₀/C
  have hBw (s : Config R) (hs : D.Accessible s) :
      B * weight s ≤ iterateSum D.successors weight (K+1) s := by
    obtain ⟨j,hj⟩ := hs
    have hd := (iterateSum_walk D.successors D.accessible_step δ hδ ⟨j,hj⟩
      (D.replay_last hj hn hn')).2
    have hle : weight s ≤ C := by
      exact pow_le_pow_right₀ alpha_ge_one (List.count_le_length.trans_eq (D.walk_len hj))
    have he : iterateSum D.successors weight 1 =
        (fun s => alpha*weight s+δ s) := by funext s; dsimp [δ]; ring
    rw [iterateSum_add_steps,he,iterateSum_linear]
    have hh := D.weighted_exp K s ⟨j,hj⟩
    have hm := mul_le_mul_of_nonneg_right hle (div_nonneg hδ0.le hC.le)
    rw [mul_comm C,div_mul_cancel₀ _ hC.ne'] at hm
    dsimp [B]
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hh alpha_pos.le]
  have hB : 0 < B := add_pos (pow_pos alpha_pos _) (div_pos hδ0 hC)
  have hscale (c : ℝ) (F : Config R → ℝ) (k : ℕ) (s : Config R) :
      iterateSum D.successors (fun u => c * F u) k s = c * iterateSum D.successors F k s := by
    induction k generalizing s with
    | zero => rfl
    | succ k ih => rw [iterateSum,iterateSum,funext ih,sum_scale]
  have hbig (k : ℕ) (s : Config R) (hs : D.Accessible s) :
      B^k * weight s ≤ iterateSum D.successors weight (k*(K+1)) s := by
    induction k generalizing s with
    | zero => simp [iterateSum]
    | succ k ih =>
      rw [Nat.succ_mul,pow_succ,add_comm (k*(K+1)),iterateSum_add_steps,mul_assoc]
      have hh := mul_le_mul_of_nonneg_left (hBw s hs) (pow_nonneg hB.le k)
      refine hh.trans ?_
      have hi := iterateSum_mono D.successors D.accessible_step
        (fun x hx => ih x hx) (K+1) hs
      rwa [hscale] at hi
  have hinitial : D.Accessible D.initial := ⟨0,Walk.nil _⟩
  have hcap (s : Config R) (hs : D.Accessible s) : weight s ≤ C*D.continuation 0 s := by
    obtain ⟨j,hj⟩ := hs
    have hw : weight s ≤ C := pow_le_pow_right₀ alpha_ge_one
      (List.count_le_length.trans_eq (D.walk_len hj))
    exact hw.trans (by simpa using mul_le_mul_of_nonneg_left (D.continuation_zero_ge s) hC.le)
  have hroot : weight D.initial = 1 := by
    have he (n : ℕ) : (List.replicate n false).count true = 0 := by
      induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ,ih]
    simp [weight,initial,he]
  have hpath (k : ℕ) : B^k ≤ C*(r R.f (2^(k*(K+1))) : ℝ) := by
    have hlarge := hbig k _ hinitial
    rw [hroot,mul_one] at hlarge
    have hbound := iterateSum_mono D.successors D.accessible_step hcap (k*(K+1)) hinitial
    rw [hscale,D.iteration_continuation _ _ hinitial,D.continuation_initial] at hbound
    have hp := (paths_mass_bounds R.f (k*(K+1)) 1 (vertex_one R.degree)).1
    rw [← R.affinePaths_spec _ _ (vertex_one R.degree),R.state_one,mass_one] at hp
    exact hlarge.trans (hbound.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hp) hC.le))
  let a := B ^ ((1:ℝ)/(K+1 : ℕ))
  have ha : 0 < a := Real.rpow_pos_of_pos hB _
  have ha' : a ^ (K+1) = B := by
    change (B ^ ((1:ℝ)/(↑(K+1) : ℝ))) ^ (K+1) = B
    rw [one_div,Real.rpow_inv_natCast_pow hB.le (by omega)]
  have ht : Tendsto (fun k : ℕ => k*(K+1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b,fun k hk => hk.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos K))⟩
  have hConst := (tendsto_const_nhds (x := C)).rpow
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) (Or.inl hC.ne')
  rw [Real.rpow_zero] at hConst
  have hh := ((hConst.mul hr).comp ht)
  rw [one_mul] at hh
  have hale : a ≤ alpha := by
    apply le_of_tendsto_of_tendsto' ((tendsto_geometric_root ha.le).comp ht) hh
    intro k
    change (a^(k*(K+1))) ^ ((1:ℝ)/(↑(k*(K+1)) : ℝ)) ≤
      C ^ ((1:ℝ)/(↑(k*(K+1)) : ℝ)) * (r R.f (2^(k*(K+1))) : ℝ) ^ ((1:ℝ)/(↑(k*(K+1)) : ℝ))
    rw [← Real.mul_rpow hC.le (Nat.cast_nonneg _),mul_comm k,pow_mul,ha']
    exact Real.rpow_le_rpow (pow_nonneg hB.le _) (by simpa only [Nat.mul_comm] using hpath k) (by positivity)
  have hf := pow_le_pow_left₀ ha.le hale (K+1)
  rw [ha'] at hf
  have hpos := div_pos hδ0 hC
  dsimp [B] at hf
  linarith

#print axioms no_strict_at_alpha

end
end Garbe.PrimitiveRule.Delay
```

### `GarbeMarker.lean`

```lean
import GarbeSharp

namespace Garbe.PrimitiveRule.Delay
open Garbe Polynomial
noncomputable section
attribute [local instance] Classical.propDecidable

variable {R : PrimitiveRule} (D : R.Delay)

theorem even_zero : R.even 0 = true := decide_eq_true R.residue_zero

private theorem reward_eq_iff (u : R.L) : reward R u = alpha ↔ R.even u = true := by
  cases h : R.even u <;> simp [reward,h,alpha_lt_four.ne.symm]

theorem exact_weight (hr : HasGrowthRate R.f alpha) {s : Config R} (h : D.Accessible s) :
    alpha * weight s = ((D.successors s).map weight).sum := by
  obtain ⟨n,hn⟩ := h
  exact le_antisymm (D.weight_step_ge s (D.walk_len hn))
    (not_lt.mp (D.no_strict_at_alpha hr ⟨n,hn⟩))

theorem exact_empty (hr : HasGrowthRate R.f alpha) (u : R.L) (is : List Bool)
    (h : D.Accessible (u,false::is)) : R.even u = true := by
  have he := D.exact_weight hr h
  rw [D.weight_step_formula] at he
  have he' : alpha^is.count true * alpha = alpha^is.count true * reward R u := by
    simpa [weight,disclose,mul_comm] using he
  exact (reward_eq_iff u).mp ((mul_left_cancel₀ (pow_ne_zero _ alpha_pos.ne') he').symm)

theorem exact_occupied (hr : HasGrowthRate R.f alpha) (u : R.L) (is : List Bool)
    (h : D.Accessible (u,true::is)) :
    reward R u + reward R (u+D.a) + reward R (u+D.b) = 2*alpha+4 := by
  have he := D.exact_weight hr h
  rw [D.weight_step_formula] at he
  have he' : alpha^is.count true * (2*alpha+4) =
      alpha^is.count true * (reward R u + reward R (u+D.a) + reward R (u+D.b)) := by
    change _ = alpha^is.count true * disclose true D.a D.b (reward R) u
    rw [← he]
    simp only [weight,List.count_cons_self,pow_succ,← alpha_sq]
    ring
  exact (mul_left_cancel₀ (pow_ne_zero _ alpha_pos.ne') he').symm

theorem some_walk (n : ℕ) : ∃ s, Walk D.successors n D.initial s := by
  induction n with
  | zero => exact ⟨D.initial,Walk.nil _⟩
  | succ n ih =>
    obtain ⟨s,hs⟩ := ih
    cases he : D.successors s with
    | nil =>
      have hb := D.weight_step_ge s (D.walk_len hs)
      rw [he] at hb
      have hp : 0 < alpha * weight s := mul_pos alpha_pos (pow_pos alpha_pos _)
      simp at hb
      linarith
    | cons q qs => exact ⟨q,Walk.snoc hs (by simp [he])⟩

structure Marker (D : R.Delay) where
  tag : Tag
  section_label : tag = some 1 ∨ tag = some 2
  odd_offset : ∀ z : Tag, R.even (offset D.a D.b z) = false ↔ z = tag
  ordinary_even : R.even D.a = true ∨ R.even D.b = true

theorem exists_marker (hr : HasGrowthRate R.f alpha) : Nonempty D.Marker := by
  obtain ⟨s,hs⟩ := D.some_walk (D.t+1)
  have hq := D.early_config hs le_rfl
  rw [Nat.sub_self,List.replicate_zero,List.nil_append,List.replicate_succ] at hq
  have he := D.exact_occupied hr 0 (List.replicate D.t true) ⟨_,hq ▸ hs⟩
  simp only [zero_add,reward,even_zero,ite_true] at he
  cases ha : R.even D.a <;> cases hb : R.even D.b
  · simp [ha,hb] at he
    linarith [alpha_lt_four]
  · refine ⟨⟨some 1,Or.inl rfl,?_,Or.inr hb⟩⟩
    intro z
    cases z with
    | none => simp [offset,even_zero]
    | some z => fin_cases z <;> simp [offset,even_zero,ha,hb]
  · refine ⟨⟨some 2,Or.inr rfl,?_,Or.inl ha⟩⟩
    intro z
    cases z with
    | none => simp [offset,even_zero]
    | some z => fin_cases z <;> simp [offset,even_zero,ha,hb]
  · simp [ha,hb] at he
    linarith [alpha_lt_four]

namespace Marker
variable {D : R.Delay} (M : D.Marker)

theorem not_none : M.tag ≠ none := by rcases M.section_label with h | h <;> simp [h]
theorem not_zero : M.tag ≠ some 0 := by rcases M.section_label with h | h <;> simp [h]

include M in
theorem default_even (hr : HasGrowthRate R.f alpha) {s : Config R} (hs : D.Accessible s) :
    R.even s.1 = true := by
  obtain ⟨u,is⟩ := s
  cases is with
  | nil =>
    obtain ⟨n,hn⟩ := hs
    have h := D.walk_len hn
    simp at h
  | cons i is =>
    cases i
    · exact D.exact_empty hr u is hs
    · by_contra! hu
      have huf : R.even u = false := Bool.eq_false_of_not_eq_true hu
      have he := D.exact_occupied hr u is hs
      have h₁ : reward R u = 4 := by simp [reward,huf]
      rcases M.ordinary_even with h | h
      · obtain ⟨d,hd⟩ := R.even_of_residue (of_decide_eq_true h)
        have h₂ : reward R (u+D.a) = 4 := by
          simp [reward,hd,even_add_double,huf]
        rw [h₁,h₂] at he
        linarith [reward_ge (u+D.b), alpha_lt_four]
      · obtain ⟨d,hd⟩ := R.even_of_residue (of_decide_eq_true h)
        have h₂ : reward R (u+D.b) = 4 := by
          simp [reward,hd,even_add_double,huf]
        rw [h₁,h₂] at he
        linarith [reward_ge (u+D.a), alpha_lt_four]

theorem actual_odd (hr : HasGrowthRate R.f alpha) (u : R.L) (z : Tag) (zs : List Tag)
    (hs : D.Accessible (forget (u,z::zs))) :
    R.even (D.actual (u,z::zs)) = false ↔ z = M.tag := by
  have hu : R.even u = true := M.default_even hr hs
  obtain ⟨d,hd⟩ := R.even_of_residue (of_decide_eq_true hu)
  have he : D.actual (u,z::zs) =
      (offset D.a D.b z + (d+d)) + (effect D.a D.b zs + effect D.a D.b zs) := by
    simp only [actual,effect,hd]
    abel
  rw [he,even_add_double,even_add_double,M.odd_offset]

theorem half_at_even (v : R.L) (h : R.even v = true) : v = R.base v + R.base v := by
  have hh : (R.residueClass v).val = 0 := of_decide_eq_true h
  have he := R.halfDiff_spec (v := v) (w := R.residueRepresentative (R.residueClass v))
    (R.residueRepresentative_spec (R.residueClass v)).symm
  simpa only [base,residueRepresentative,ite_eq_left hh,zero_add] using he

theorem no_marker_zero (hr : HasGrowthRate R.f alpha) {s : Filled R}
    (hs : D.Accessible (forget s)) (hm : M.tag ∉ s.2) : D.actual s = 0 := by
  have hdvd (k : ℕ) (s : Filled R) (hs : D.Accessible (forget s)) (hm : M.tag ∉ s.2) :
      ∃ q : R.L, D.actual s = 2^k • q := by
    induction k generalizing s with
    | zero => exact ⟨D.actual s,by simp⟩
    | succ k ih =>
      obtain ⟨u,ls⟩ := s
      obtain ⟨n,hn⟩ := hs
      have hL := D.walk_len hn
      cases ls with
      | nil => simp [forget] at hL
      | cons z zs =>
        have hne : z ≠ M.tag := fun h => hm (h ▸ List.mem_cons_self ..)
        have htrue : R.even (D.actual (u,z::zs)) = true := by
          by_contra! h
          exact hne ((M.actual_odd hr u z zs ⟨n,hn⟩).mp (Bool.eq_false_of_not_eq_true h))
        let q0 := R.base (D.actual (u,z::zs))
        have he : (some 0,q0) ∈ tagged R (D.actual (u,z::zs)) := by simp [tagged,htrue,q0]
        have hl : zs.length = D.t := by simpa [forget] using hL
        obtain ⟨v,hv,hv'⟩ := D.replay_step hl he
        have hn' : D.Accessible (forget (v,zs++[some 0])) := ⟨n+1,Walk.snoc hn hv'⟩
        have hm' : M.tag ∉ zs++[some 0] := by
          simp only [List.mem_append,List.mem_singleton,not_or]
          exact ⟨fun h => hm (List.mem_cons_of_mem _ h),M.not_zero⟩
        obtain ⟨q,hq⟩ := ih _ hn' hm'
        have ha := half_at_even (D.actual (u,z::zs)) htrue
        change D.actual (u,z::zs) = q0+q0 at ha
        refine ⟨q,?_⟩
        rw [ha,← hv,hq,pow_succ',mul_nsmul,two_nsmul,nsmul_add]
  by_contra hn
  obtain ⟨t,ht⟩ := R.cannot_divide_at_abs_coordinate hn
  exact ht (hdvd t s hs hm)

private theorem root_replay {ls : List Tag} {v : R.L} (h : TaggedWalk R ls 0 v) :
    ∃ s : Filled R, D.Accessible (forget s) ∧ D.actual s = v ∧
      s.2 = ((List.replicate (D.t+1) none)++ls).drop ls.length := by
  let s0 : Filled R := (0,List.replicate (D.t+1) none)
  have he (n : ℕ) : effect D.a D.b (List.replicate n none) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ,effect,offset,ih]
  have ha : D.actual s0 = 0 := by simp [actual,s0,he]
  have hl : s0.2.length = D.t+1 := by simp [s0]
  obtain ⟨s,hs,hv,hls⟩ := D.replay hl (ha ▸ h)
  have h0 : forget s0 = D.initial := by simp [forget,initial,s0]
  exact ⟨s,⟨_,h0 ▸ hs⟩,hv,hls⟩

include M in
theorem before_special (hr : HasGrowthRate R.f alpha) {ls : List Tag} {v : R.L}
    (h : TaggedWalk R ls 0 v) (hk : ls.length < D.t+1) : R.even v = true := by
  obtain ⟨s,hs,hv,hslots⟩ := root_replay (D := D) h
  have hlen : (D.t+1-ls.length) = (D.t-ls.length)+1 := by omega
  rw [List.drop_append,List.drop_replicate,List.length_replicate,Nat.sub_eq_zero_of_le hk.le,
    List.drop_zero,hlen,List.replicate_succ,List.cons_append] at hslots
  obtain ⟨u,sl⟩ := s
  change sl = _ at hslots
  subst sl
  rw [← hv]
  by_contra! hh
  exact M.not_none ((M.actual_odd hr _ _ _ hs).mp (Bool.eq_false_of_not_eq_true hh)).symm

theorem zero_of_ordinary_walk (hr : HasGrowthRate R.f alpha) {ls : List Tag} {v : R.L}
    (h : TaggedWalk R ls 0 v) (hm : M.tag ∉ ls) : v = 0 := by
  obtain ⟨s,hs,hv,hslots⟩ := root_replay (D := D) h
  rw [← hv]
  apply M.no_marker_zero hr hs
  rw [hslots]
  intro hx
  have hx' := List.mem_of_mem_drop hx
  have hn : M.tag ∉ List.replicate (D.t+1) (none : Tag) := by
    intro h
    exact M.not_none (List.eq_of_mem_replicate h)
  exact (List.mem_append.mp hx').elim hn hm

theorem special_walk (hr : HasGrowthRate R.f alpha) (k : ℕ) (hk : k ≤ D.t) :
    ∃ v, TaggedWalk R ([M.tag]++List.replicate k (some 0)) 0 v := by
  induction k with
  | zero =>
    have he : R.even 0 = true := even_zero
    rcases M.section_label with h | h
    · refine ⟨R.base 0+R.offsetA,?_⟩
      simpa only [List.replicate_zero,List.append_nil,List.nil_append,h] using
        TaggedWalk.snoc (TaggedWalk.nil (R := R) 0) (j := some 1)
        (by simp [tagged,he] : (some 1,R.base 0+R.offsetA) ∈ tagged R 0)
    · refine ⟨R.base 0+R.offsetB,?_⟩
      simpa only [List.replicate_zero,List.append_nil,List.nil_append,h] using
        TaggedWalk.snoc (TaggedWalk.nil (R := R) 0) (j := some 2)
        (by simp [tagged,he] : (some 2,R.base 0+R.offsetB) ∈ tagged R 0)
  | succ k ih =>
    obtain ⟨v,hv⟩ := ih (by omega)
    have he := M.before_special hr hv (by simp; omega)
    refine ⟨R.base v,?_⟩
    rw [List.replicate_succ',← List.append_assoc]
    exact TaggedWalk.snoc hv (by simp [tagged,he])

include M in
theorem special_vertex (hr : HasGrowthRate R.f alpha) :
    ∃ g : P2, IsVertex R.f g ∧ R.even (R.state g) = false ∧
      ∀ v ∈ R.next (R.state g), v = 0 := by
  obtain ⟨x,hx⟩ := M.special_walk hr D.t le_rfl
  obtain ⟨g,hg,hgx⟩ := tagged_realized hx ⟨1,vertex_one R.degree,R.state_one⟩
  obtain ⟨q,hq,hqv,hl⟩ := root_replay (D := D) hx
  simp only [List.length_append,List.length_singleton,List.length_replicate] at hl
  have hsum : 1+D.t = (List.replicate (D.t+1) (none : Tag)).length := by simp [Nat.add_comm]
  rw [hsum,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at hl
  obtain ⟨u,qs⟩ := q
  change qs = _ at hl
  subst qs
  change D.actual (u,M.tag::List.replicate D.t (some 0)) = x at hqv
  have ho : R.even x = false := by rw [← hqv]; exact (M.actual_odd hr _ _ _ hq).mpr rfl
  refine ⟨g,hg,hgx ▸ ho,?_⟩
  intro v hv
  rw [hgx] at hv
  have ht : (none,v) ∈ tagged R x := by
    rw [tagged,ite_eq_right (by simp [ho])]
    exact List.mem_map.mpr ⟨v,hv,rfl⟩
  rw [← hqv] at ht
  obtain ⟨u',hval,hnext⟩ := D.replay_step (by simp) ht
  have hacc := D.accessible_step _ hq _ hnext
  have hnone : M.tag ∉ List.replicate D.t (some 0) ++ [none] := by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact M.not_zero (List.eq_of_mem_replicate h)
    · exact M.not_none (List.mem_singleton.mp h)
  exact hval ▸ M.no_marker_zero hr hacc hnone

end Marker

#print axioms Marker.special_vertex

end
end Garbe.PrimitiveRule.Delay
```

### `GarbeConjecture.lean`

```lean
import GarbeMarker
import Mathlib.Algebra.CharP.Two

namespace Garbe
open Polynomial
noncomputable section

namespace PrimitiveRule

theorem trim_section_eq_one (R : PrimitiveRule) {g q : P2} (hg : IsVertex R.f g)
    (hq : q ∈ rawChildren R.f g) (hn : q ≠ 0)
    (hz : ∀ v ∈ R.next (R.state g), v = 0) : trim q = 1 := by
  have hm : trim q ∈ children R.f g := List.mem_map.mpr ⟨q,
    List.mem_filter.mpr ⟨hq,decide_eq_true hn⟩,rfl⟩
  have he := hz _ ((R.next_matches hg).mem_iff.mp (List.mem_map.mpr ⟨_,hm,rfl⟩))
  exact projection_zero_vertex R.constant (child_properties hg.2 hm) (congrArg Subtype.val he)

theorem odd_sections_at_odd (R : PrimitiveRule) {g : P2} (hg : IsVertex R.f g)
    (he : R.even (R.state g) = false) : oddSection g ≠ 0 ∧ oddSection (g*R.f) ≠ 0 := by
  classical
  by_contra h
  have ho : oddSection g = 0 ∨ oddSection (g*R.f) = 0 := by
    by_cases hz : oddSection g = 0
    · exact Or.inl hz
    · exact Or.inr (not_ne_iff.mp fun hn => h ⟨hz,hn⟩)
  obtain ⟨u,hu,h⟩ := (projected_even_iff R.constant hg.1 R.primitive).mpr ho
  have hh : R.state g = (⟨u,hu⟩ : R.L) + ⟨u,hu⟩ := Subtype.ext h
  have hn : R.residue (R.state g) ≠ 0 := by
    unfold even at he
    exact of_decide_eq_false he
  exact hn (R.residue_of_even ⟨_,hh⟩)

theorem evenSection_coeff0 (g : P2) : (evenSection g).coeff 0 = g.coeff 0 := by
  rw [coeff_evenSection,mul_zero]

theorem binomial_of_trim_sections {g : P2} (hg : g.coeff 0 = 1) (hn : oddSection g ≠ 0)
    (he : trim (evenSection g) = 1) (ho : trim (oddSection g) = 1) :
    ∃ m : ℕ, g = parts 1 (X ^ m) := by
  rw [trim_of_coeff0 ((evenSection_coeff0 g).trans hg)] at he
  obtain ⟨_,hs⟩ := trim_spec hn
  rw [ho,mul_one] at hs
  exact ⟨_,by conv_lhs => rw [← parts_sections g,he,hs]⟩

private theorem parts_product (a b : P2) (m : ℕ) :
    parts 1 (X^m) * parts a b = parts (a + X * (X^m*b)) (b + X^m*a) := by
  simp only [parts,map_one,map_add,map_mul,expand_X]
  ring

private theorem exponents_eq_of_three {s m n : ℕ}
    (h : (X^m + X^s + X^(2*s+1+m) : P2) = X^n) : m = s := by
  let q := 2*s+1+m
  have hqm : m < q := by dsimp [q]; omega
  have hqs : s < q := by dsimp [q]; omega
  have htop := congrArg (fun p : P2 => p.coeff q) h
  change ((X^m + X^s + X^q : P2).coeff q) = (X^n : P2).coeff q at htop
  have hq : q = n := by
    by_contra hne
    simp [coeff_X_pow,hqm.ne',hqs.ne',hne] at htop
  by_contra hne
  have hlow := congrArg (fun p : P2 => p.coeff m) h
  change ((X^m + X^s + X^q : P2).coeff m) = (X^n : P2).coeff m at hlow
  rw [← hq] at hlow
  simp [coeff_X_pow,hne,hqm.ne] at hlow

private theorem solve_two_binomials (f : P2) {s t : ℕ} (hb : oddSection f ≠ 0)
    (hprod : parts 1 (X^s) * f = parts 1 (X^t))
    (hmon : evenSection f = 1 ∨ ∃ m : ℕ, oddSection f = X^m) :
    ∃ j : ℕ, 0 < j ∧ f = 1 + X^j + X^(2*j) := by
  have hp : parts (evenSection f + X * (X^s * oddSection f))
      (oddSection f + X^s * evenSection f) = parts 1 (X^t) := by
    rw [← parts_product, parts_sections, hprod]
  have he := congrArg evenSection hp
  have ho := congrArg oddSection hp
  simp only [section_even_parts,section_odd_parts] at he ho
  rcases hmon with ha | ⟨m,hm⟩
  · rw [ha,add_eq_left] at he
    exact (mul_ne_zero X_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero) hb) he).elim
  · have hpow : (X * (X^s * X^m) : P2) = X^(s+1+m) := by
      rw [pow_add,pow_succ]; ring
    rw [hm,hpow] at he
    have ha : evenSection f = 1 + X^(s+1+m) := by
      rw [← he,CharTwo.add_cancel_right]
    rw [hm,ha,mul_add,mul_one,← pow_add,← add_assoc,
      show s+(s+1+m) = 2*s+1+m by omega] at ho
    have hm' : m = s := exponents_eq_of_three ho
    subst m
    let j := 2*s+1
    have hja : evenSection f = 1 + X^j := by convert ha using 3; dsimp [j]; omega
    refine ⟨j,by dsimp [j]; omega,?_⟩
    conv_lhs => rw [← parts_sections f,hja,hm,parts,map_add,map_one,map_pow,map_pow,expand_X,
      ← pow_mul,← pow_mul]
    have hfinal : (X*X^(2*s) : P2) = X^j := by
      change X * X^(2*s) = X^(2*s+1)
      rw [pow_succ,mul_comm]
    rw [hfinal]
    abel

theorem ordinary_section {R : PrimitiveRule} {D : R.Delay} (M : D.Marker)
    (hr : HasGrowthRate R.f Delay.alpha) :
    evenSection R.f = 1 ∨ ∃ m : ℕ, oddSection R.f = X^m := by
  have he : R.even 0 = true := Delay.even_zero
  rcases M.section_label with h | h
  · have hw : Delay.TaggedWalk R [some 2] 0 (R.base 0+R.offsetB) := by
      simpa only [List.nil_append] using Delay.TaggedWalk.snoc (Delay.TaggedWalk.nil (R := R) 0)
        (by simp [Delay.tagged,he] : (some 2,R.base 0+R.offsetB) ∈ Delay.tagged R 0)
    have hz := M.zero_of_ordinary_walk hr hw (by simp [h])
    rw [R.base_zero,zero_add] at hz
    have hg : IsVertex R.f (trim (oddSection R.f)) := child_properties (vertex_one R.degree).2
      (show trim (oddSection R.f) ∈ children R.f 1 from List.mem_map.mpr
        ⟨_,List.mem_filter.mpr ⟨by simp [rawChildren],decide_eq_true R.odd⟩,rfl⟩)
    have hs : R.state (trim (oddSection R.f)) = 0 := (R.state_trim R.odd).trans hz
    have h1 := projection_zero_vertex R.constant hg (congrArg Subtype.val hs)
    refine Or.inr ⟨(oddSection R.f).natTrailingDegree,?_⟩
    simpa only [h1,mul_one] using (trim_spec R.odd).2
  · have hw : Delay.TaggedWalk R [some 1] 0 (R.base 0+R.offsetA) := by
      simpa only [List.nil_append] using Delay.TaggedWalk.snoc (Delay.TaggedWalk.nil (R := R) 0)
        (by simp [Delay.tagged,he] : (some 1,R.base 0+R.offsetA) ∈ Delay.tagged R 0)
    have hz := M.zero_of_ordinary_walk hr hw (by simp [h])
    rw [R.base_zero,zero_add] at hz
    have hchild : evenSection R.f ∈ children R.f 1 := by
      have hf : ((1:P2)*R.f).coeff 0 = 1 := by simpa only [one_mul] using R.constant
      simpa only [one_mul] using even_mul_mem_children R.f 1 hf
    have hg := child_properties (vertex_one R.degree).2 hchild
    exact Or.inl (projection_zero_vertex R.constant hg (congrArg Subtype.val hz))

theorem alpha_similar (R : PrimitiveRule) (hr : HasGrowthRate R.f Delay.alpha) :
    Similar R.f (1+X+X^2) := by
  have hgt : 3 < Delay.alpha := Delay.alpha_gt_three
  obtain ⟨t,a,b,ha,hb,ho⟩ := R.deepest_offsets (R.offsets_of_rate_gt_three hr hgt)
  let D : R.Delay := ⟨t,a,b,ha,hb,ho⟩
  obtain ⟨M⟩ := D.exists_marker hr
  obtain ⟨g,hg,hodd,hz⟩ := M.special_vertex hr
  obtain ⟨hgodd,hgfodd⟩ := R.odd_sections_at_odd hg hodd
  have hgfc : (g*R.f).coeff 0 = 1 := by rw [coeff0_mul,hg.1,R.constant,one_mul]
  obtain ⟨s,hs⟩ := binomial_of_trim_sections hg.1 hgodd
    (R.trim_section_eq_one hg (by simp [rawChildren]) (nonzero_even hg.1) hz)
    (R.trim_section_eq_one hg (by simp [rawChildren]) hgodd hz)
  obtain ⟨t,ht⟩ := binomial_of_trim_sections hgfc hgfodd
    (R.trim_section_eq_one hg (by simp [rawChildren]) (nonzero_even hgfc) hz)
    (R.trim_section_eq_one hg (by simp [rawChildren]) hgfodd hz)
  rw [hs] at ht
  obtain ⟨j,hj,he⟩ := solve_two_binomials R.f R.odd ht (ordinary_section M hr)
  rw [he]
  by_cases h : j = 1
  · rw [h,pow_one, mul_one]
    exact Relation.EqvGen.refl _
  · apply Relation.EqvGen.symm
    have hs := Relation.EqvGen.rel _ _ (SimStep.dil (1+X+X^2) j (by omega))
    simpa only [← expand_eq_comp_X_pow,map_add,map_one,expand_X,map_pow,← pow_mul,mul_comm j 2] using hs

end PrimitiveRule

theorem garbe_conj_3_7 (f : P2) (hf : 2 ≤ f.support.card) :
    ∃ rate, HasGrowthRate f rate ∧ 3 ≤ rate ∧ (rate = 3 ↔ Similar f (1 + X)) ∧
      (3 < rate → 1 + Real.sqrt 5 ≤ rate) ∧
      (rate = 1 + Real.sqrt 5 ↔ Similar f (1 + X + X ^ 2)) := by
  obtain ⟨rate,hr,hlo⟩ := garbe_growth_and_lower_bound f hf
  refine ⟨rate,hr,hlo,garbe_rate_three_iff f hf hr,garbe_gap f hf hr,?_⟩
  constructor
  · intro h
    obtain ⟨R,hR⟩ := primitive_representative f hf
    have h₀ : HasGrowthRate f (1 + Real.sqrt 5) := h ▸ hr
    have hrate : HasGrowthRate R.f PrimitiveRule.Delay.alpha := (growth_similarity hR _).mp h₀
    exact Relation.EqvGen.trans _ _ _ hR (R.alpha_similar hrate)
  · intro hs
    exact growth_unique hr (garbe_trinomial_of_similar f hs)

#check garbe_conj_3_7
#check garbe_monomial
#check garbe_zero
#print axioms garbe_conj_3_7
#print axioms garbe_monomial
#print axioms garbe_zero

end
end Garbe
```
