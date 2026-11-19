# Lean source appendix

Modules are listed in import order.

## WSCore.lean

```lean
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace WangSun

open Finset
open scoped Classical BigOperators
noncomputable section

def B (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun j k => ((j.val : ℤ)+1) - ((k.val : ℤ)+1) + (if j = k then 1 else 0)

theorem B_zero_based {n : ℕ} (j k : Fin n) :
    B n j k = (j.val : ℤ) - (k.val : ℤ) + (if j = k then 1 else 0) := by
  unfold B
  ring

def WangSunConjecture : Prop :=
  ∀ p : ℕ, p.Prime → Odd p →
    Int.ModEq (p : ℤ) (B (p-1)).permanent 3 ∧
    Int.ModEq ((p : ℤ)^2) (B p).permanent (1+4*(p : ℤ))

variable {R S : Type*} [CommRing R] [CommRing S]
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def D (x : α → R) : Matrix α α R := fun i j => x i - x j

def part (x : α → R) (s : Finset α) : R :=
  (D (fun i : s => x i.val)).permanent

def degree (x : α → R) (d : ℕ) : R := ∑ s ∈ (univ : Finset α).powersetCard d, part x s

theorem perD_reindex (e : α ≃ β) (x : β → R) :
    (D (fun i => x (e i))).permanent = (D x).permanent := by
  unfold Matrix.permanent
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  apply Fintype.prod_equiv e
  intro i
  simp [D, Equiv.permCongr]

omit [Fintype α] in
theorem part_map (e : Equiv.Perm α) (x : α → R) (s : Finset α) :
    part (fun i => x (e i)) s = part x (s.map e.toEmbedding) := by
  let e' : s ≃ s.map e.toEmbedding := (e.imageFinset s).trans
    (Finset.equivOfEq (Finset.map_eq_image e.toEmbedding s).symm)
  exact perD_reindex e' (fun i : s.map e.toEmbedding => x i.val)

theorem degree_reindex (e : Equiv.Perm α) (x : α → R) (d : ℕ) :
    degree (fun i => x (e i)) d = degree x d := by
  unfold degree
  apply Finset.sum_equiv (Equiv.finsetCongr e)
  · simp [mem_powersetCard]
  · intro s _
    exact part_map e x s

theorem degree_map (f : R →+* S) (x : α → R) (d : ℕ) :
    f (degree x d) = degree (fun i => f (x i)) d := by
  simp [degree, part, D, Matrix.permanent, map_sum, map_prod]

theorem degree_shift (x : α → R) (c : R) (d : ℕ) :
    degree (fun i => x i+c) d = degree x d := by
  unfold degree
  apply sum_congr rfl
  intro s _
  unfold part
  congr 1
  ext i j
  change x i.val+c-(x j.val+c) = x i.val-x j.val
  ring

theorem degree_neg (x : α → R) (d : ℕ) :
    degree (fun i => -x i) d = degree x d := by
  unfold degree
  apply sum_congr rfl
  intro s _
  unfold part
  rw [← Matrix.permanent_transpose (D (fun i : s => x i.val))]
  congr 1
  ext i j
  change -x i.val - -x j.val = x j.val-x i.val
  ring

theorem degree_scale (x : α → R) (c : R) (d : ℕ) :
    degree (fun i => c*x i) d = c^d * degree x d := by
  unfold degree
  rw [mul_sum]
  apply sum_congr rfl
  intro s hs
  unfold part
  have h : D (fun i : s => c*x i.val) = c • D (fun i : s => x i.val) := by
    ext i j
    exact (mul_sub c _ _).symm
  rw [h, Matrix.permanent_smul, Fintype.card_coe, (mem_powersetCard.mp hs).2]

theorem degree_zero (x : α → R) : degree x 0 = 1 := by
  simp [degree, part, Matrix.permanent_eq_one_of_card_eq_zero]

theorem degree_full (x : α → R) :
    degree x (Fintype.card α) = (D x).permanent := by
  unfold degree
  rw [← card_univ, powersetCard_self, sum_singleton]
  exact perD_reindex (Equiv.subtypeUnivEquiv mem_univ) x

omit [Fintype α] in
theorem fixed_mem_iff (s : Finset α) (σ : Equiv.Perm α)
    (h : ∀ i ∉ s, σ i = i) (i : α) : i ∈ s ↔ σ i ∈ s := by
  constructor
  · intro hi
    by_contra hn
    exact hn (by rw [σ.injective (h _ hn)]; exact hi)
  · intro hi
    by_contra hn
    exact hn (h i hn ▸ hi)

def fixedEquiv (s : Finset α) : {σ : Equiv.Perm α // ∀ i ∉ s, σ i = i} ≃ Equiv.Perm s := by
  let restrict (σ : {σ : Equiv.Perm α // ∀ i ∉ s, σ i = i}) : Equiv.Perm s :=
    σ.val.subtypeEquiv (fixed_mem_iff s σ.val σ.property)
  let extend (τ : Equiv.Perm s) : Equiv.Perm α :=
    Equiv.Perm.subtypeCongr (p := fun i => i ∈ s) τ (Equiv.refl _)
  have heL (τ : Equiv.Perm s) (i) (hi : i ∈ s) :
      extend τ i = (τ ⟨i,hi⟩).val :=
    Equiv.Perm.subtypeCongr.left_apply (p := fun i => i ∈ s) τ (Equiv.refl _) hi
  have heR (τ : Equiv.Perm s) (i) (hi : i ∉ s) : extend τ i = i :=
    Equiv.Perm.subtypeCongr.right_apply (p := fun i => i ∈ s) τ (Equiv.refl _) hi
  refine ⟨restrict,fun τ => ⟨extend τ,heR τ⟩,?_,?_⟩
  · intro σ
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change extend (restrict σ) i = σ.val i
    by_cases hi : i ∈ s
    · rw [heL _ _ hi]
      rfl
    · rw [heR _ _ hi, σ.property i hi]
  · intro τ
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact heL τ i.val i.property

theorem permanent_expand (x : α → R) :
    ((1 : Matrix α α R) + D x).permanent = ∑ s : Finset α, part x s := by
  simp only [Matrix.permanent, Matrix.add_apply, add_comm ((1 : Matrix α α R) _ _),
    Fintype.prod_add]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  have hprod (σ : Equiv.Perm α) :
      (∏ i ∈ sᶜ, (1 : Matrix α α R) (σ i) i) = if ∀ i ∉ s, σ i = i then 1 else 0 := by
    split
    · rename_i h
      apply prod_eq_one
      intro i hi
      simp [Matrix.one_apply, h i (mem_compl.mp hi)]
    · rename_i h
      push Not at h
      obtain ⟨i,hi,hne⟩ := h
      exact prod_eq_zero (mem_compl.mpr hi) (by simp [hne])
  simp_rw [hprod, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  let T := (univ : Finset (Equiv.Perm α)).filter (fun σ => ∀ i ∉ s, σ i = i)
  change ∑ σ ∈ T, (∏ i ∈ s, D x (σ i) i) = part x s
  rw [← sum_coe_sort]
  let e : T ≃ Equiv.Perm s :=
    (Equiv.subtypeEquivRight (fun σ => by simp [T])).trans (fixedEquiv s)
  unfold part Matrix.permanent
  apply Fintype.sum_equiv e
  intro σ
  rw [← prod_coe_sort]
  rfl

theorem sum_degrees (x : α → R) :
    ((1 : Matrix α α R) + D x).permanent = ∑ d ∈ range (Fintype.card α+1), degree x d := by
  rw [permanent_expand]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card)
    (t := range (Fintype.card α+1)) (fun s _ => mem_range.mpr
      (Nat.lt_succ_of_le (card_le_univ s))) (part x)]
  apply sum_congr rfl
  intro d _
  unfold degree
  congr 1
  ext s
  simp [mem_powersetCard]

end
end WangSun
```

## WSRankTwo.lean

```lean
import WSCore

namespace WangSun

open Finset
open scoped BigOperators Classical
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]
variable {α : Type*} [Fintype α] [DecidableEq α]

def elem (x : α → R) (d : ℕ) : R :=
  ∑ s ∈ (univ : Finset α).powersetCard d, ∏ i ∈ s, x i

omit [DecidableEq α] in
theorem elem_map (f : R →+* S) (x : α → R) (d : ℕ) :
    f (elem x d) = elem (fun i => f (x i)) d := by
  simp [elem, map_sum, map_prod]

omit [DecidableEq α] in
theorem elem_zero (x : α → R) : elem x 0 = 1 := by simp [elem]

omit [DecidableEq α] in
theorem elem_full (x : α → R) : elem x (Fintype.card α) = ∏ i, x i := by
  simp [elem, ← card_univ]

omit [Fintype α] [DecidableEq α] in
theorem map_mem_iff (σ : Equiv.Perm α) (s : Finset α) (i : α) :
    i ∈ s ↔ σ i ∈ s.map σ.toEmbedding := by simp

def imageFiberEquiv (s t : Finset α) :
    {σ : Equiv.Perm α // s.map σ.toEmbedding = t} ≃ ((s ≃ t) × (↥sᶜ ≃ ↥tᶜ)) := by
  have pos (σ : {σ : Equiv.Perm α // s.map σ.toEmbedding = t}) (i : α) :
      i ∈ s ↔ σ.val i ∈ t := by
    have h := map_mem_iff σ.val s i
    rw [σ.property] at h
    exact h
  let restr (σ : {σ : Equiv.Perm α // s.map σ.toEmbedding = t}) :
      (s ≃ t) × (↥sᶜ ≃ ↥tᶜ) :=
    (σ.val.subtypeEquiv (pos σ), σ.val.subtypeEquiv (fun i => by simpa using not_congr (pos σ i)))
  let join (e : (s ≃ t) × (↥sᶜ ≃ ↥tᶜ)) : Equiv.Perm α :=
    Equiv.subtypeCongr (p := fun i => i ∈ s) (q := fun i => i ∈ t) e.1
      ((Equiv.subtypeEquivRight fun _ => mem_compl.symm).trans
        (e.2.trans (Equiv.subtypeEquivRight fun _ => mem_compl)))
  have hr (e : (s ≃ t) × (↥sᶜ ≃ ↥tᶜ)) (i : α) (h : i ∈ s) :
      join e i = (e.1 ⟨i,h⟩).val := by
    simp [join, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos h]
  have hl (e : (s ≃ t) × (↥sᶜ ≃ ↥tᶜ)) (i : α) (h : i ∉ s) :
      join e i = (e.2 ⟨i,mem_compl.mpr h⟩).val := by
    simp [join, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg h]
    rfl
  have hf (e : (s ≃ t) × (↥sᶜ ≃ ↥tᶜ)) : s.map (join e).toEmbedding = t := by
    ext i
    have h := map_mem_iff (join e) s ((join e).symm i)
    rw [Equiv.apply_symm_apply] at h
    rw [← h]
    by_cases hi : (join e).symm i ∈ s
    · have hm := (e.1 ⟨_,hi⟩).property
      rw [← hr, Equiv.apply_symm_apply] at hm
      simp [hi,hm]
    · have hm : join e ((join e).symm i) ∉ t := by
        rw [hl e _ hi]
        exact mem_compl.mp (e.2 ⟨_,mem_compl.mpr hi⟩).property
      rw [Equiv.apply_symm_apply] at hm
      simp [hi,hm]
  refine ⟨restr,fun e => ⟨join e,hf e⟩,?_,?_⟩
  · intro σ
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change join (restr σ) i = _
    by_cases h : i ∈ s
    · exact hr _ _ h
    · exact hl _ _ h
  · intro e
    apply Prod.ext
    · apply Equiv.ext
      intro i
      apply Subtype.ext
      exact hr e _ i.property
    · apply Equiv.ext
      intro i
      apply Subtype.ext
      exact hl e _ (mem_compl.mp i.property)

theorem image_fiber_count (s t : Finset α) (h : t.card = s.card) :
    Fintype.card {σ : Equiv.Perm α // s.map σ.toEmbedding = t} =
      s.card.factorial * (Fintype.card α-s.card).factorial := by
  let e : s ≃ t := Fintype.equivOfCardEq (by simpa using h.symm)
  let e' : ↥sᶜ ≃ ↥tᶜ := Fintype.equivOfCardEq (by simp [h])
  let f : (s ≃ t) ≃ Equiv.Perm s :=
    { toFun := fun u => u.trans e.symm
      invFun := fun u => u.trans e
      left_inv := fun u => Equiv.ext fun i => e.apply_symm_apply (u i)
      right_inv := fun u => Equiv.ext fun i => e.symm_apply_apply (u i) }
  let g : (↥sᶜ ≃ ↥tᶜ) ≃ Equiv.Perm ↥sᶜ :=
    { toFun := fun u => u.trans e'.symm
      invFun := fun u => u.trans e'
      left_inv := fun u => Equiv.ext fun i => e'.apply_symm_apply (u i)
      right_inv := fun u => Equiv.ext fun i => e'.symm_apply_apply (u i) }
  rw [Fintype.card_congr ((imageFiberEquiv s t).trans (Equiv.prodCongr f g))]
  simp [Fintype.card_prod, Fintype.card_perm]

theorem image_prod_sum (x : α → R) (s : Finset α) :
    (∑ σ : Equiv.Perm α, ∏ i ∈ s, x (σ i)) =
      (s.card.factorial : R) * ((Fintype.card α-s.card).factorial : R) * elem x s.card := by
  let f (σ : Equiv.Perm α) := s.map σ.toEmbedding
  have hprod (σ : Equiv.Perm α) : (∏ i ∈ s, x (σ i)) = ∏ j ∈ f σ, x j := by
    simp [f, prod_map]
  simp_rw [hprod]
  have hf (σ : Equiv.Perm α) : f σ ∈ (univ : Finset α).powersetCard s.card :=
    mem_powersetCard.mpr ⟨subset_univ _,card_map _⟩
  rw [← sum_fiberwise_of_maps_to (g := f) (fun σ _ => hf σ) (fun σ => ∏ j ∈ f σ, x j)]
  unfold elem
  rw [mul_sum]
  apply sum_congr rfl
  intro t ht
  let U := (univ : Finset (Equiv.Perm α)).filter (fun σ => f σ = t)
  change ∑ σ ∈ U, (∏ j ∈ f σ, x j) = _
  have hconst (σ : Equiv.Perm α) (hσ : σ ∈ U) : (∏ j ∈ f σ, x j) = ∏ j ∈ t, x j :=
    congrArg (fun z => ∏ j ∈ z, x j) (mem_filter.mp hσ).2
  rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]
  have hc : U.card = Fintype.card {σ : Equiv.Perm α // s.map σ.toEmbedding = t} := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun σ => by simp [U,f])
  rw [hc, image_fiber_count s t (mem_powersetCard.mp ht).2, Nat.cast_mul]

theorem complement_prod_sum (x : α → R) {d : ℕ} (hd : d ≤ Fintype.card α) :
    (∑ s ∈ (univ : Finset α).powersetCard d, ∏ i ∈ sᶜ, x i) =
      elem x (Fintype.card α-d) := by
  unfold elem
  let e : Finset α ≃ Finset α := ⟨compl,compl,compl_compl,compl_compl⟩
  apply Finset.sum_equiv e
  · intro s
    simp only [mem_powersetCard, subset_univ, true_and]
    change s.card = d ↔ (sᶜ).card = Fintype.card α-d
    rw [card_compl]
    have := card_le_univ s
    omega
  · intros
    rfl

theorem perD_rank_two (x : α → R) :
    (D x).permanent = ∑ d ∈ range (Fintype.card α+1),
      (-1 : R)^d * (d.factorial : R) * ((Fintype.card α-d).factorial : R) *
        elem x d * elem x (Fintype.card α-d) := by
  have hsub (a b : R) : a-b = -b+a := by ring
  rw [← Matrix.permanent_transpose (D x)]
  simp only [Matrix.permanent, Matrix.transpose_apply, D, hsub, Fintype.prod_add]
  rw [sum_comm]
  have h (s : Finset α) :
      (∑ σ : Equiv.Perm α, (∏ i ∈ s, -x (σ i)) * ∏ i ∈ sᶜ, x i) =
        (-1 : R)^s.card * (s.card.factorial : R) *
          ((Fintype.card α-s.card).factorial : R) * elem x s.card * ∏ i ∈ sᶜ, x i := by
    simp_rw [prod_neg]
    rw [← sum_mul]
    rw [← mul_sum, image_prod_sum]
    ring
  simp_rw [h]
  rw [← sum_fiberwise_of_maps_to (g := Finset.card)
    (t := range (Fintype.card α+1)) (fun s _ => mem_range.mpr (Nat.lt_succ_of_le (card_le_univ s)))
    (fun s : Finset α => (-1 : R)^s.card * (s.card.factorial : R) *
      ((Fintype.card α-s.card).factorial : R) * elem x s.card * ∏ i ∈ sᶜ, x i)]
  apply sum_congr rfl
  intro d hd
  have hc : (univ.filter (fun s : Finset α => s.card = d)) = (univ : Finset α).powersetCard d := by
    ext s
    simp [mem_powersetCard]
  rw [hc, ← complement_prod_sum x (by simpa using Nat.le_of_lt_succ (mem_range.mp hd)), mul_sum]
  apply sum_congr rfl
  intro s hs
  rw [(mem_powersetCard.mp hs).2]

end
end WangSun
```

## WSResidues.lean

```lean
import WSRankTwo
import Mathlib.NumberTheory.Wilson
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.ZMod.Units
import Mathlib.Data.ZMod.Coprime

namespace WangSun

open Finset Polynomial
open scoped BigOperators Classical
noncomputable section

variable {p : ℕ} [Fact p.Prime]

theorem prime_gt_one : 1 < p := (Fact.out : p.Prime).one_lt

omit [Fact p.Prime] in
theorem odd_sub_even (ho : Odd p) : Even (p-1) := by
  obtain ⟨r,hr⟩ := ho
  exact ⟨r,by omega⟩

abbrev NZ (p : ℕ) := {a : ZMod p // a ≠ 0}

theorem card_NZ : Fintype.card (NZ p) = p-1 :=
  (Fintype.card_congr unitsEquivNeZero).symm.trans (ZMod.card_units p)

def nonzeroEquiv {α : Type*} [Fintype α] (x : α → ZMod p) (hi : Function.Injective x)
    (hn : ∀ i, x i ≠ 0) (hc : Fintype.card α = p-1) : α ≃ NZ p :=
  Equiv.ofBijective (fun i => ⟨x i,hn i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ h => hi (congrArg Subtype.val h), hc.trans card_NZ.symm⟩)

theorem exists_scale {d : ℕ} (hd : 0 < d) (hlt : d < p-1) :
    ∃ a : ℤ, (a : ZMod p) ≠ 0 ∧ (a : ZMod p)^d ≠ 1 := by
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hu
  refine ⟨(u.val.val : ℤ),?_,?_⟩
  · simp
  · intro h
    rw [Int.cast_natCast, ZMod.natCast_zmod_val] at h
    have hpow : u^d = 1 := Units.ext h
    have hh := orderOf_dvd_of_pow_eq_one hpow
    rw [hu] at hh
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hd hh)

theorem isUnit_square (a : ℤ) (h : (a : ZMod p) ≠ 0) :
    IsUnit (a : ZMod (p^2)) := by
  apply (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr
  have hnd := mt (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr h
  have hp := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hc := hp.coprime_iff_not_dvd.mpr hnd
  simpa only [Nat.cast_pow] using hc.pow_left (m := 2)

theorem sq_multiple_of_mod_zero (a : ℤ) (h : (a : ZMod p) = 0) :
    (p : ZMod (p^2)) * (a : ZMod (p^2)) = 0 := by
  rw [← Int.cast_natCast, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h
  simpa only [pow_two] using mul_dvd_mul (dvd_refl (p : ℤ)) hd

theorem nonzero_poly :
    (∏ a : NZ p, (X - C a.val)) = (X^(p-1) - 1 : (ZMod p)[X]) := by
  let P : (ZMod p)[X] := X^p-X
  have hdeg : P.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ prime_gt_one
  have hroots : P.roots = (univ : Finset (ZMod p)).val := by
    simpa only [ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hmon : P.Monic := monic_X_pow_sub (by simpa using (prime_gt_one (p := p)))
  have hfact := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
    (by rw [hroots, ← Finset.card_def, card_univ, ZMod.card, hdeg])
  rw [hroots, ← Finset.prod_eq_multiset_prod] at hfact
  apply mul_left_cancel₀ (X_ne_zero : (X : (ZMod p)[X]) ≠ 0)
  calc
    X * (∏ a : NZ p, (X - C a.val)) = P := by
      have he : (∏ a ∈ (univ : Finset (ZMod p)).erase 0, (X - C a)) =
          ∏ a : NZ p, (X - C a.val) :=
        Finset.prod_subtype _ (by simp) (fun a : ZMod p => X - C a)
      refine (congrArg (fun A => X*A) he.symm).trans ?_
      have hm := mul_prod_erase (univ : Finset (ZMod p)) (fun a => X-C a) (mem_univ 0)
      simp only [map_zero, sub_zero] at hm
      exact hm.trans hfact
    _ = X * (X ^ (p-1) - 1) := by
      dsimp [P]
      rw [mul_sub, mul_one, ← pow_succ', show p-1+1=p by have := prime_gt_one (p := p); omega]

theorem elem_middle_zero {α : Type*} [Fintype α]
    (y : α → ℤ) (e : α ≃ NZ p) (he : ∀ i, (y i : ZMod p) = (e i).val)
    {d : ℕ} (hd : 0 < d) (hdk : d < p-1) :
    (↑(elem y d) : ZMod p) = 0 := by
  have hc : Fintype.card α = p-1 := (Fintype.card_congr e).trans card_NZ
  let w (i : α) : ZMod p := y i
  have hprod : (∏ i : α, (X-C (w i))) = X^(p-1)-1 :=
    (Fintype.prod_equiv e _ _ (fun i => congrArg (fun a => X-C a) (he i))).trans nonzero_poly
  let ms := (univ : Finset α).val.map w
  have hms : ms.card = p-1 := by simp [ms, hc]
  have h := Multiset.prod_X_sub_C_coeff ms (k := p-1-d) (by omega)
  rw [hms, show p-1-(p-1-d) = d by omega] at h
  have hh : (ms.map (fun t => X-C t)).prod = X^(p-1)-1 := by
    rw [show ms = (univ : Finset α).val.map w from rfl, Multiset.map_map,
      ← Finset.prod_eq_multiset_prod]
    exact hprod
  rw [hh, coeff_sub, coeff_X_pow, coeff_one, ite_eq_right (by omega), ite_eq_right (by omega), sub_zero] at h
  have hm : ms.esymm d = 0 :=
    (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  rw [show (↑(elem y d) : ZMod p) = elem w d from elem_map (Int.castRingHom (ZMod p)) y d]
  exact (Finset.esymm_map_val _ _ _).symm.trans hm

theorem perD_mod_square {α : Type*} [Fintype α] [DecidableEq α]
    (y : α → ℤ) (e : α ≃ NZ p) (he : ∀ i, (y i : ZMod p) = (e i).val)
    (ho : Odd p) :
    ((D y).permanent : ZMod (p^2)) =
      2 * ((p-1).factorial : ZMod (p^2)) * (∏ i : α, y i : ℤ) := by
  have hc : Fintype.card α = p-1 := (Fintype.card_congr e).trans card_NZ
  have hm : 0 < p-1 := by have := prime_gt_one (p := p); omega
  let f (d : ℕ) : ℤ := (-1)^d * (d.factorial : ℤ) * ((Fintype.card α-d).factorial : ℤ) *
    elem y d * elem y (Fintype.card α-d)
  have hsum := perD_rank_two y
  change (D y).permanent = ∑ d ∈ range (Fintype.card α+1), f d at hsum
  rw [hsum, Int.cast_sum, hc]
  have hsub : ({0,p-1} : Finset ℕ) ⊆ range (p-1+1) := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with h | h <;> subst i <;> simp
  rw [← sum_subset hsub]
  · rw [sum_insert (by simpa using hm.ne), sum_singleton]
    have h₀ : f 0 = ((p-1).factorial : ℤ) * ∏ i : α, y i := by
      dsimp [f]
      rw [elem_zero, elem_full, hc]
      ring
    have hₘ : f (p-1) = ((p-1).factorial : ℤ) * ∏ i : α, y i := by
      dsimp [f]
      rw [(odd_sub_even ho).neg_one_pow, ← hc, Nat.sub_self, Nat.factorial_zero,
        elem_zero, elem_full, hc]
      ring
    rw [h₀,hₘ]
    push_cast
    ring
  · intro d h₁ h₂
    have hd : 0 < d ∧ d < p-1 := by
      simp only [mem_insert, mem_singleton, not_or] at h₂
      have := mem_range.mp h₁
      omega
    have hj : 0 < Fintype.card α-d ∧ Fintype.card α-d < p-1 := by rw [hc]; omega
    have hv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (elem_middle_zero y e he hd.1 hd.2)
    have hw := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (elem_middle_zero y e he hj.1 hj.2)
    have hz : ((elem y d * elem y (Fintype.card α-d) : ℤ) : ZMod (p^2)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow, pow_two]
      exact mul_dvd_mul hv hw
    dsimp [f]
    rw [mul_assoc _ (elem y d), Int.cast_mul, hz, mul_zero]

end
end WangSun
```

## WSLift.lean

```lean
import WSResidues
import Mathlib.Algebra.DualNumber

namespace WangSun

open Finset TrivSqZeroExt
open scoped BigOperators Classical
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]
variable {α : Type*} [Fintype α] [DecidableEq α]

def dualMap (f : R →+* S) : DualNumber R →+* DualNumber S where
  toFun z := ⟨f z.fst, f z.snd⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := TrivSqZeroExt.ext (map_add f a.fst b.fst) (map_add f a.snd b.snd)
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul f a.fst b.fst
    · change f (a.fst*b.snd+a.snd*b.fst) = f a.fst*f b.snd+f a.snd*f b.fst
      rw [map_add, map_mul, map_mul]

def dualEval (f : R →+* S) (t : S) (ht : t*t = 0) : DualNumber R →+* S where
  toFun z := f z.fst + t*f z.snd
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := by simp; ring
  map_mul' a b := by
    simp only [fst_mul, DualNumber.snd_mul, map_mul, map_add]
    calc
      _ = (f a.fst + t*f a.snd) * (f b.fst + t*f b.snd) -
          (t*t)*(f a.snd*f b.snd) := by ring
      _ = _ := by rw [ht, zero_mul, sub_zero]

def dualVec (x b : α → R) (i : α) : DualNumber R := ⟨x i,b i⟩

omit [Fintype α] in
theorem dual_prod_fst (s : Finset α) (x b : α → R) :
    (∏ i ∈ s, dualVec x b i).fst = ∏ i ∈ s, x i := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [prod_insert hi, prod_insert hi, fst_mul, ih]; rfl

omit [Fintype α] in
theorem dual_prod_add (s : Finset α) (x b c : α → R) :
    (∏ i ∈ s, dualVec x (b+c) i).snd =
      (∏ i ∈ s, dualVec x b i).snd + (∏ i ∈ s, dualVec x c i).snd := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [prod_insert hi, DualNumber.snd_mul, dual_prod_fst, ih]
    change x i * ((∏ j ∈ s, dualVec x b j).snd + (∏ j ∈ s, dualVec x c j).snd) +
      (b i+c i) * (∏ j ∈ s, x j) =
      x i*(∏ j ∈ s, dualVec x b j).snd + b i*(∏ j ∈ s, x j) +
        (x i*(∏ j ∈ s, dualVec x c j).snd + c i*(∏ j ∈ s, x j))
    ring

theorem variation_add (x b c : α → R) (d : ℕ) :
    (degree (dualVec x (b+c)) d).snd =
      (degree (dualVec x b) d).snd + (degree (dualVec x c) d).snd := by
  unfold degree part D Matrix.permanent
  simp only [snd_sum]
  simp_rw [show ∀ (s : Finset α) (σ : Equiv.Perm s),
      (fun i : s => dualVec x (b+c) (σ i).val - dualVec x (b+c) i.val) =
      dualVec (fun i : s => x (σ i).val-x i.val)
        ((fun i : s => b (σ i).val-b i.val)+(fun i : s => c (σ i).val-c i.val)) by
    intro s σ
    funext i
    apply TrivSqZeroExt.ext
    · rfl
    · change (b (σ i).val+c (σ i).val)-(b i.val+c i.val) =
        b (σ i).val-b i.val+(c (σ i).val-c i.val)
      ring]
  simp_rw [dual_prod_add, sum_add_distrib]
  rfl

def variation (x : α → R) (d : ℕ) : (α → R) →+ R where
  toFun b := (degree (dualVec x b) d).snd
  map_add' := fun b c => variation_add x b c d
  map_zero' := by
    have h := variation_add x 0 0 d
    rw [add_zero] at h
    exact (add_eq_left.mp h.symm)

theorem reflection_variation {K : Type*} [Field K]
    (x : α ≃ K) (h2 : (2 : K) ≠ 0) (d : ℕ) (b : α → K) :
    variation x d b = 0 := by
  have single (i : α) (v : K) :
      variation x d (fun j => if j=i then v else 0) = 0 := by
    let r : Equiv.Perm K :=
      ⟨fun t => 2*x i-t,fun t => 2*x i-t,fun t => by ring,fun t => by ring⟩
    let σ := x.trans (r.trans x.symm)
    have hx (j : α) : x (σ j) = 2*x i-x j := by simp [σ,r]
    have hi : σ i = i := by
      apply x.injective
      rw [hx]
      ring
    let a (j : α) : K := if j=i then v else 0
    have ha (j : α) : a (σ j) = a j := by
      have hiff : σ j = i ↔ j = i := by
        exact ⟨fun h => σ.injective (h.trans hi.symm), fun h => (congrArg σ h).trans hi⟩
      simp [a,hiff]
    let z : DualNumber K := ⟨2*x i,0⟩
    have hv (j : α) : dualVec x a (σ j) = -(dualVec x (-a) j) + z := by
      apply TrivSqZeroExt.ext
      · change x (σ j) = -x j+2*x i
        rw [hx]
        ring
      · change a (σ j) = -(-a j)+0
        simp [ha]
    have h := degree_reindex σ (dualVec x a) d
    simp_rw [hv] at h
    rw [degree_shift, degree_neg] at h
    have hh : variation x d (-a) = variation x d a := congrArg TrivSqZeroExt.snd h
    rw [map_neg] at hh
    have he : 2 * variation x d a = 0 := by linear_combination -hh
    exact (mul_eq_zero.mp he).resolve_left h2
  have hb : b = ∑ i : α, (fun j => if j=i then b i else 0) := by
    funext j
    simp [Finset.sum_apply]
  conv_lhs => rw [hb]
  rw [map_sum]
  exact sum_eq_zero (fun i _ => single i (b i))

variable {p : ℕ} [Fact p.Prime]

theorem lift_invariance (x y : α → ℤ) (e : α ≃ ZMod p)
    (he : ∀ i, (x i : ZMod p) = e i) (ho : Odd p)
    (hy : ∀ i, (y i : ZMod p) = x i) (d : ℕ) :
    (↑(degree y d) : ZMod (p^2)) = (↑(degree x d) : ZMod (p^2)) := by
  have hd (i : α) : (p : ℤ) ∣ y i-x i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [Int.cast_sub,hy,sub_self]
  choose b hb using hd
  have hb' (i : α) : y i = x i+(p : ℤ)*b i := by linarith [hb i]
  have h2 : (2 : ZMod p) ≠ 0 := by
    change ¬ (((2 : ℕ) : ZMod p) = 0)
    rw [ZMod.natCast_eq_zero_iff]
    have hp : 1 < p := prime_gt_one
    obtain ⟨k,hk⟩ := ho
    intro h
    have hn := Nat.le_of_dvd (show 0 < 2 by decide) h
    omega
  let z := degree (dualVec x b) d
  have hvar := reflection_variation e h2 d (fun i => (b i : ZMod p))
  have h₁ : (z.snd : ZMod p) = 0 := by
    have h := degree_map (dualMap (Int.castRingHom (ZMod p))) (dualVec x b) d
    have hf : (fun i => dualMap (Int.castRingHom (ZMod p)) (dualVec x b i)) =
        dualVec e (fun i => (b i : ZMod p)) := by
      funext i
      exact TrivSqZeroExt.ext (he i) rfl
    rw [hf] at h
    exact (congrArg TrivSqZeroExt.snd h).trans hvar
  have hz : (p : ZMod (p^2))*(p : ZMod (p^2)) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, pow_two]
  let eval := dualEval (Int.castRingHom (ZMod (p^2))) (p : ZMod (p^2)) hz
  have hY : eval z = degree (fun i => (y i : ZMod (p^2))) d := by
    rw [show z = degree (dualVec x b) d from rfl, degree_map]
    congr 1
    funext i
    change (x i : ZMod (p^2))+(p : ZMod (p^2))*(b i : ZMod (p^2)) = _
    rw [hb' i, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have hX : (z.fst : ZMod (p^2)) = degree (fun i => (x i : ZMod (p^2))) d := by
    have h := degree_map (dualEval (Int.castRingHom (ZMod (p^2))) 0 (by simp)) (dualVec x b) d
    change (z.fst : ZMod (p^2)) + 0*(z.snd : ZMod (p^2)) =
      degree (fun i => (x i : ZMod (p^2)) + 0*(b i : ZMod (p^2))) d at h
    simpa only [zero_mul, add_zero] using h
  have hEval : eval z = (z.fst : ZMod (p^2)) := by
    change (z.fst : ZMod (p^2)) + (p : ZMod (p^2))*(z.snd : ZMod (p^2)) = _
    rw [sq_multiple_of_mod_zero _ h₁, add_zero]
  calc
    _ = degree (fun i => (y i : ZMod (p^2))) d := degree_map (Int.castRingHom (ZMod (p^2))) y d
    _ = eval z := hY.symm
    _ = (z.fst : ZMod (p^2)) := hEval
    _ = degree (fun i => (x i : ZMod (p^2))) d := hX
    _ = _ := (degree_map (Int.castRingHom (ZMod (p^2))) x d).symm

end
end WangSun
```

## WSFactorials.lean

```lean
import WSResidues
import Mathlib.Data.Nat.Factorial.BigOperators

namespace WangSun

open Finset
open scoped BigOperators Classical
noncomputable section

def labels (n : ℕ) (i : Fin n) : ℤ := i.val

def positiveLabels (n : ℕ) (i : Fin n) : ℤ := (i.val : ℤ)+1

theorem prod_positive (n : ℕ) : (∏ i : Fin n, positiveLabels n i) = (n.factorial : ℤ) := by
  rw [show (∏ i : Fin n, positiveLabels n i) = ∏ i ∈ range n, ((i : ℤ)+1) from
    Fin.prod_univ_eq_prod_range (fun i : ℕ => (i : ℤ)+1) n]
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  simp only [Nat.cast_add, Nat.cast_one]

theorem prod_below (i : ℕ) : (∏ j ∈ range i, ((j : ℤ)-i)) =
    (-1 : ℤ)^i * (i.factorial : ℤ) := by
  rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => (j : ℤ)-i)]
  calc
    _ = ∏ j : Fin i, -positiveLabels i j :=
      Fintype.prod_equiv Fin.revPerm _ _ (fun j => by
        change (j.val : ℤ)-i = -(((j.rev.val : ℕ) : ℤ)+1)
        have h := j.isLt
        change (j.val : ℤ)-i = -(((i-(j.val+1) : ℕ) : ℤ)+1)
        omega)
    _ = _ := by simp [prod_neg, prod_positive]

theorem prod_omit_range (p i : ℕ) (hi : i < p) :
    (∏ j ∈ (range p).erase i, ((j : ℤ)-i)) =
      (-1 : ℤ)^i * (i.factorial : ℤ) * ((p-1-i).factorial : ℤ) := by
  have aux (r : ℕ) :
      (∏ j ∈ (range (i+1+r)).erase i, ((j : ℤ)-i)) =
        (-1 : ℤ)^i * (i.factorial : ℤ) * (r.factorial : ℤ) := by
    induction r with
    | zero => simpa [range_add_one, erase_insert] using prod_below i
    | succ r ih =>
      rw [show i+1+r.succ = (i+1+r)+1 by omega, range_add_one,
        erase_insert_of_ne (by omega), prod_insert (by simp),
        ih, Nat.factorial_succ, Nat.cast_mul]
      push_cast
      ring
  have hp : i+1+(p-1-i) = p := by omega
  simpa only [hp] using aux (p-1-i)

theorem prod_omit (p : ℕ) (i : Fin p) :
    (∏ j : ↥((univ : Finset (Fin p)).erase i), (labels p j.val-labels p i)) =
      (-1 : ℤ)^i.val * (i.val.factorial : ℤ) * ((p-1-i.val).factorial : ℤ) := by
  rw [show (∏ j : ↥((univ : Finset (Fin p)).erase i), (labels p j.val-labels p i)) =
        ∏ j ∈ (univ : Finset (Fin p)).erase i, (labels p j-labels p i) from
      prod_coe_sort _ (fun j => labels p j-labels p i),
    ← prod_omit_range p i.val i.isLt]
  apply Finset.prod_bij (fun j _ => j.val)
  · intro j hj
    have hne := (mem_erase.mp hj).1
    exact mem_erase.mpr ⟨fun he => hne (Fin.ext he), mem_range.mpr j.isLt⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro j hj
    have h := mem_erase.mp hj
    exact ⟨⟨j,mem_range.mp h.2⟩,mem_erase.mpr ⟨fun he => h.1 (congrArg Fin.val he),mem_univ _⟩,rfl⟩
  · intros
    rfl

def signedFactorial (p i : ℕ) : ℤ :=
  (-1)^i * (i.factorial : ℤ) * ((p-1-i).factorial : ℤ)

theorem factorial_telescope (p : ℕ) (ho : Odd p) :
    ((p : ℤ)+1) * (∑ i ∈ range p, signedFactorial p i) = 2*(p.factorial : ℤ) := by
  let A (i : ℕ) : ℤ := (-1)^i * (i.factorial : ℤ) * ((p-i).factorial : ℤ)
  have ha (i : ℕ) (hi : i ∈ range p) :
      ((p : ℤ)+1) * signedFactorial p i = A i - A (i+1) := by
    have hi' := mem_range.mp hi
    have he : p-i = (p-1-i)+1 := by omega
    have hj : p-(i+1) = p-1-i := by omega
    dsimp [A, signedFactorial]
    rw [he, hj, pow_succ, Nat.factorial_succ i, Nat.factorial_succ (p-1-i)]
    push_cast
    have hh : (((p-1-i : ℕ) : ℤ) + (i : ℤ))+1 = p := by omega
    linear_combination -((-1 : ℤ)^i * (i.factorial : ℤ) * ((p-1-i).factorial : ℤ)) * hh
  rw [mul_sum, sum_congr rfl ha, sum_range_sub']
  dsimp [A]
  rw [ho.neg_one_pow]
  simp
  ring

variable {p : ℕ} [Fact p.Prime]

theorem mul_factorial_square :
    (p : ZMod (p^2))*((p-1).factorial : ZMod (p^2)) = -(p : ZMod (p^2)) := by
  have hw := ZMod.wilsons_lemma p
  have ha : (↑(((p-1).factorial : ℤ)+1) : ZMod p) = 0 := by
    push_cast
    rw [hw, neg_add_cancel]
  have h := sq_multiple_of_mod_zero (((p-1).factorial : ℤ)+1) ha
  push_cast at h
  linear_combination h

theorem signed_sum_square (ho : Odd p) :
    (↑(∑ i ∈ range p, signedFactorial p i) : ZMod (p^2)) = -2*(p : ZMod (p^2)) := by
  have h := congrArg (fun x : ℤ => (x : ZMod (p^2))) (factorial_telescope p ho)
  push_cast at h
  have hp : p-1+1=p := by have := prime_gt_one (p := p); omega
  rw [← hp, Nat.factorial_succ, hp, Nat.cast_mul, mul_factorial_square] at h
  have hu : IsUnit ((p : ZMod (p^2))+1) := by
    have hu' := isUnit_square (p := p) ((p : ℤ)+1) (by simp)
    push_cast at hu'
    exact hu'
  apply hu.mul_left_cancel
  rw [Int.cast_sum]
  have hz : (p : ZMod (p^2))*(p : ZMod (p^2)) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, pow_two]
  calc
    _ = 2 * -(p : ZMod (p^2)) := h
    _ = _ := by linear_combination 2 * hz

end
end WangSun
```

## WSMiddle.lean

```lean
import WSLift
import WSFactorials

namespace WangSun

open Finset
open scoped BigOperators Classical
noncomputable section

theorem B_labels (n : ℕ) : B n = (1 : Matrix (Fin n) (Fin n) ℤ) + D (labels n) := by
  ext i j
  rw [B_zero_based]
  simp [labels,D,Matrix.one_apply,add_comm]

theorem B_positiveLabels (n : ℕ) :
    B n = (1 : Matrix (Fin n) (Fin n) ℤ) + D (positiveLabels n) := by
  ext i j
  simp only [B, Matrix.add_apply, Matrix.one_apply, D, positiveLabels]
  ring

theorem sum_two_survivors {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    {m N : ℕ} (hm : 0 < m) (hN : m < N)
    (h : ∀ d < N, d ≠ 0 → d ≠ m → f d = 0) :
    ∑ d ∈ range N, f d = f 0 + f m := by
  have hs : ({0,m} : Finset ℕ) ⊆ range N := by
    intro d hd
    simp only [mem_insert,mem_singleton] at hd
    rcases hd with rfl | rfl <;> exact mem_range.mpr (by omega)
  rw [← sum_subset hs]
  · rw [sum_insert (by simpa using hm.ne),sum_singleton]
  · intro d hd hne
    simp only [mem_insert,mem_singleton,not_or] at hne
    exact h d (mem_range.mp hd) hne.1 hne.2

variable {p : ℕ} [Fact p.Prime]

def labelEquiv : Fin p ≃ ZMod p :=
  Equiv.ofBijective (fun i : Fin p => (i.val : ZMod p))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun i j h => Fin.ext (by
      have hh := congrArg ZMod.val h
      simpa only [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] using hh),
      by rw [Fintype.card_fin,ZMod.card]⟩)

theorem labelEquiv_apply (i : Fin p) : (labels p i : ZMod p) = labelEquiv i :=
  Int.cast_natCast i.val

def positiveEquiv : Fin (p-1) ≃ NZ p := by
  let w (i : Fin (p-1)) : ZMod p := (i.val+1 : ℕ)
  have hlt (i : Fin (p-1)) : i.val+1 < p := by have := i.isLt; omega
  have hval (i : Fin (p-1)) : (w i).val = i.val+1 := ZMod.val_natCast_of_lt (hlt i)
  refine nonzeroEquiv w (fun i j h => Fin.ext ?_) (fun i h => ?_) (Fintype.card_fin _)
  · have he := (hval i).symm.trans ((congrArg ZMod.val h).trans (hval j))
    omega
  · have he := (hval i).symm.trans ((congrArg ZMod.val h).trans (ZMod.val_zero))
    omega

theorem positiveEquiv_apply (i : Fin (p-1)) :
    (positiveLabels (p-1) i : ZMod p) = (positiveEquiv i).val := by
  change (((i.val : ℤ)+1 : ℤ) : ZMod p) = ((i.val+1 : ℕ) : ZMod p)
  push_cast
  rfl

theorem vanish_by_scaling {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (x : α → R) (a : R) (d : ℕ)
    (h : degree (fun i => a*x i) d = degree x d) (hu : IsUnit (a^d-1)) :
    degree x d = 0 := by
  rw [degree_scale] at h
  apply hu.mul_left_cancel
  rw [mul_zero, sub_mul, one_mul, h, sub_self]

theorem vanish_mod_prime {d : ℕ} (hd : 0 < d) (hm : d < p-1) :
    (↑(degree (positiveLabels (p-1)) d) : ZMod p) = 0 := by
  obtain ⟨a,ha,hpow⟩ := exists_scale hd hm
  let u : Equiv.Perm (NZ p) := (Equiv.mulLeft₀ (a : ZMod p) ha).subtypeEquiv (by
    intro x
    change x ≠ 0 ↔ (a : ZMod p)*x ≠ 0
    simp [ha])
  let σ := positiveEquiv.trans (u.trans positiveEquiv.symm)
  let w (i : Fin (p-1)) : ZMod p := positiveLabels (p-1) i
  have hw (i : Fin (p-1)) : (a : ZMod p)*w i = w (σ i) := by
    change (a : ZMod p)*(positiveLabels (p-1) i : ZMod p) =
      (positiveLabels (p-1) (σ i) : ZMod p)
    rw [positiveEquiv_apply, positiveEquiv_apply]
    have he : positiveEquiv (σ i) = u (positiveEquiv i) := by simp [σ]
    rw [he]
    rfl
  calc
    _ = degree w d := degree_map (Int.castRingHom (ZMod p)) _ _
    _ = 0 := vanish_by_scaling w (a : ZMod p) d
      (by simp_rw [hw]; exact degree_reindex σ w d)
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hpow))

theorem vanish_mod_square (ho : Odd p) {d : ℕ} (hd : 0 < d) (hm : d < p-1) :
    (↑(degree (labels p) d) : ZMod (p^2)) = 0 := by
  obtain ⟨a,ha,hpow⟩ := exists_scale hd hm
  let u := Equiv.mulLeft₀ (a : ZMod p) ha
  let σ := (labelEquiv (p := p)).trans (u.trans labelEquiv.symm)
  let x := labels p
  let y (i : Fin p) : ℤ := a*x i
  have hmod (i : Fin p) : (y i : ZMod p) = (x (σ i) : ZMod p) := by
    change ((a*labels p i : ℤ) : ZMod p) = (labels p (σ i) : ZMod p)
    rw [Int.cast_mul,labelEquiv_apply,labelEquiv_apply]
    simp [σ,u]
  have hl := lift_invariance (fun i => x (σ i)) y (σ.trans labelEquiv)
    (fun i => labelEquiv_apply (σ i)) ho hmod d
  rw [degree_reindex σ x d] at hl
  let w (i : Fin p) : ZMod (p^2) := x i
  have hmap (v : Fin p → ℤ) : (↑(degree v d) : ZMod (p^2)) =
      degree (fun i => (v i : ZMod (p^2))) d := degree_map (Int.castRingHom (ZMod (p^2))) v d
  rw [hmap y,hmap x] at hl
  have hw : (fun i => (y i : ZMod (p^2))) = fun i => (a : ZMod (p^2))*w i := by
    funext i
    exact Int.cast_mul a (x i)
  rw [hw] at hl
  have hu := isUnit_square (p := p) (a^d-1) (by push_cast; exact sub_ne_zero.mpr hpow)
  push_cast at hu
  calc
    _ = degree w d := hmap x
    _ = 0 := vanish_by_scaling w (a : ZMod (p^2)) d hl hu

end
end WangSun
```

## WSTheorem.lean

```lean
import WSMiddle

namespace WangSun

open Finset
open scoped BigOperators Classical
noncomputable section

theorem per_B_one : (B 1).permanent = 1 := by
  rw [Matrix.permanent_eq_elem_of_subsingleton (B 1) 0]
  simp [B]

theorem mod_two : Int.ModEq 2 (B (2-1)).permanent 3 := by
  change Int.ModEq 2 (B 1).permanent 3
  rw [per_B_one]
  decide

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem full_odd_zero (ho : Odd p) : degree (labels p) p = 0 := by
  have h := degree_neg (labels p) p
  have hs := degree_scale (labels p) (-1) p
  simp only [neg_one_mul, ho.neg_one_pow] at hs
  rw [h] at hs
  linarith

theorem first_top (ho : Odd p) :
    (↑(degree (positiveLabels (p-1)) (p-1)) : ZMod p) = 2 := by
  have h := perD_mod_square (positiveLabels (p-1)) positiveEquiv positiveEquiv_apply ho
  have h' := congrArg (ZMod.castHom (show p ∣ p^2 by exact ⟨p,pow_two p⟩) (ZMod p)) h
  rw [prod_positive] at h'
  simp only [map_intCast, map_natCast, map_mul, map_ofNat, Int.cast_natCast, ZMod.wilsons_lemma] at h'
  have hfull : degree (positiveLabels (p-1)) (p-1) = (D (positiveLabels (p-1))).permanent := by
    simpa only [Fintype.card_fin] using degree_full (positiveLabels (p-1))
  calc
    _ = (((D (positiveLabels (p-1))).permanent : ℤ) : ZMod p) :=
      congrArg (fun z : ℤ => (z : ZMod p)) hfull
    _ = 2 := h'.trans (by ring)

theorem first_odd (ho : Odd p) : Int.ModEq (p : ℤ) (B (p-1)).permanent 3 := by
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  rw [B_positiveLabels, sum_degrees, Fintype.card_fin, Int.cast_sum]
  rw [sum_two_survivors (fun d => (↑(degree (positiveLabels (p-1)) d) : ZMod p))
    (m := p-1) (by have := prime_gt_one (p := p); omega) (by omega)]
  · rw [degree_zero, Int.cast_one, first_top ho, show (1+2 : ZMod p) = 3 by ring]
    norm_cast
  · intro d h h₀ hm
    exact vanish_mod_prime (by omega) (by omega)

abbrev Omit (p : ℕ) (i : Fin p) := ↥((univ : Finset (Fin p)).erase i)

def omitLabels (i : Fin p) (j : Omit p i) : ℤ := labels p j.val - labels p i

def omitEquiv (i : Fin p) : Omit p i ≃ NZ p := by
  let w (j : Omit p i) : ZMod p := labelEquiv j.val - labelEquiv i
  apply nonzeroEquiv w
  · intro a b h
    apply Subtype.ext
    apply labelEquiv.injective
    exact sub_left_inj.mp h
  · intro j h
    exact (mem_erase.mp j.property).1 (labelEquiv.injective (sub_eq_zero.mp h))
  · simp [Omit]

theorem omitEquiv_apply (i : Fin p) (j : Omit p i) :
    (omitLabels i j : ZMod p) = (omitEquiv i j).val := by
  change ((labels p j.val-labels p i : ℤ) : ZMod p) = labelEquiv j.val-labelEquiv i
  rw [Int.cast_sub,labelEquiv_apply,labelEquiv_apply]

omit [Fact p.Prime] in
theorem omit_part (i : Fin p) :
    part (labels p) (univ.erase i) = (D (omitLabels i)).permanent := by
  unfold part
  congr 1
  ext a b
  change labels p a.val-labels p b.val =
    (labels p a.val-labels p i)-(labels p b.val-labels p i)
  ring

theorem degree_omit :
    degree (labels p) (p-1) = ∑ i : Fin p, part (labels p) (univ.erase i) := by
  unfold degree
  symm
  apply Finset.sum_bij (fun i _ => (univ : Finset (Fin p)).erase i)
  · intro i _
    simp [mem_powersetCard]
  · intro i _ j _ h
    by_contra hn
    have hi : i ∈ (univ : Finset (Fin p)).erase j := mem_erase.mpr ⟨hn,mem_univ i⟩
    rw [← h] at hi
    exact (mem_erase.mp hi).1 rfl
  · intro s hs
    have hcard := (mem_powersetCard.mp hs).2
    have hc : (sᶜ : Finset (Fin p)).card = 1 := by
      rw [card_compl, Fintype.card_fin,hcard]
      have := prime_gt_one (p := p)
      omega
    obtain ⟨i,hi⟩ := card_eq_one.mp hc
    exact ⟨i,mem_univ _,by rw [← compl_singleton, ← hi, compl_compl]⟩
  · intros
    rfl

theorem second_top (ho : Odd p) : (↑(degree (labels p) (p-1)) : ZMod (p^2)) = 4*(p : ZMod (p^2)) := by
  rw [degree_omit, Int.cast_sum]
  have ht (i : Fin p) : (↑(part (labels p) (univ.erase i)) : ZMod (p^2)) =
      2*((p-1).factorial : ZMod (p^2)) * (signedFactorial p i.val : ZMod (p^2)) := by
    rw [omit_part]
    have h := perD_mod_square (omitLabels i) (omitEquiv i) (omitEquiv_apply i) ho
    have hprod : (∏ j : Omit p i, omitLabels i j) = signedFactorial p i.val := prod_omit p i
    rw [hprod] at h
    exact h
  simp_rw [ht]
  rw [← mul_sum, ← Int.cast_sum, Fin.sum_univ_eq_sum_range (signedFactorial p),
    signed_sum_square ho]
  calc
    _ = -4 * ((p : ZMod (p^2))*((p-1).factorial : ZMod (p^2))) := by ring
    _ = _ := by rw [mul_factorial_square]; ring

theorem second_odd (ho : Odd p) :
    Int.ModEq ((p : ℤ)^2) (B p).permanent (1+4*(p : ℤ)) := by
  rw [← Nat.cast_pow]
  apply (ZMod.intCast_eq_intCast_iff _ _ (p^2)).mp
  rw [B_labels, sum_degrees, Fintype.card_fin, Int.cast_sum]
  rw [sum_two_survivors (fun d => (↑(degree (labels p) d) : ZMod (p^2)))
    (m := p-1) (by have := prime_gt_one (p := p); omega) (by omega)]
  · rw [degree_zero, Int.cast_one, second_top ho]
    push_cast
    rfl
  · intro d h h₀ hm
    by_cases he : d = p
    · subst d
      rw [full_odd_zero ho, Int.cast_zero]
    · exact vanish_mod_square ho (by omega) (by omega)

theorem wang_sun_mod_prime (p : ℕ) (hp : p.Prime) :
    Int.ModEq (p : ℤ) (B (p-1)).permanent 3 := by
  by_cases h : p=2
  · subst p
    exact mod_two
  · let : Fact p.Prime := ⟨hp⟩
    exact first_odd (hp.odd_of_ne_two h)

theorem wang_sun_mod_prime_sq (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    Int.ModEq ((p : ℤ)^2) (B p).permanent (1+4*(p : ℤ)) := by
  let : Fact p.Prime := ⟨hp⟩
  exact second_odd ho

theorem wang_sun_source : WangSunConjecture := fun p hp ho =>
  ⟨wang_sun_mod_prime p hp, wang_sun_mod_prime_sq p hp ho⟩

#check B_zero_based
#check mod_two
#check wang_sun_mod_prime
#check wang_sun_mod_prime_sq
#check wang_sun_source
#print axioms B_zero_based
#print axioms mod_two
#print axioms wang_sun_mod_prime
#print axioms wang_sun_mod_prime_sq
#print axioms wang_sun_source

end
end WangSun
```

