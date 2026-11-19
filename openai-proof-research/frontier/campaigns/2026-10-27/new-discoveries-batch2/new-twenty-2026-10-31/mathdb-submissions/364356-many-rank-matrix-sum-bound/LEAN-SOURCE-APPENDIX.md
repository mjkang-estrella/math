# Lean source appendix

Modules are listed in import order.

## MatrixSumCore.lean

```lean
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace MatrixSum

universe u

abbrev Mat (F : Type u) (n : ℕ) := Matrix (Fin n) (Fin n) F

abbrev Space (F : Type u) (n : ℕ) := Fin n → F

def RankClass (F : Type u) [Field F] (n r : ℕ) :=
  {X : Mat F n // X.rank = r}

noncomputable def rankCount (F : Type u) [Field F] (n r : ℕ) : ℕ :=
  Nat.card (RankClass F n r)

def SumClass {F : Type u} [Field F] {n k : ℕ} (r : Fin k → ℕ) (T : Mat F n) :=
  {X : Fin k → Mat F n // (∀ i, (X i).rank = r i) ∧ ∑ i, X i = T}

noncomputable def sumCount {F : Type u} [Field F] {n k : ℕ}
    (r : Fin k → ℕ) (T : Mat F n) : ℕ :=
  Nat.card (SumClass r T)

abbrev Fiber {α β : Type*} (f : α → β) (y : β) := {x : α // f x = y}

instance {α β : Type*} [Finite α] (f : α → β) (y : β) : Finite (Fiber f y) :=
  inferInstanceAs (Finite {x : α // f x = y})

instance {F : Type*} [Field F] [Finite F] (n r : ℕ) : Finite (RankClass F n r) :=
  inferInstanceAs (Finite {X : Mat F n // X.rank = r})

instance {F : Type*} [Field F] [Finite F] {n k : ℕ} (r : Fin k → ℕ) (T : Mat F n) :
    Finite (SumClass r T) :=
  inferInstanceAs (Finite {X : Fin k → Mat F n // (∀ i, (X i).rank = r i) ∧ ∑ i, X i = T})

theorem card_fibers {α β : Type*} [Finite α] [Fintype β] (f : α → β) :
    Nat.card α = ∑ y, Nat.card (Fiber f y) := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]

theorem card_fibers_le {α β : Type*} [Finite α] [Finite β] (f : α → β) (C : ℕ)
    (h : ∀ y, Nat.card (Fiber f y) ≤ C) : Nat.card α ≤ Nat.card β * C := by
  let := Fintype.ofFinite β
  rw [card_fibers f, Nat.card_eq_fintype_card]
  simpa using Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => h y)

theorem card_fibers_const {α β : Type*} [Finite α] [Finite β] (f : α → β) (C : ℕ)
    (h : ∀ y, Nat.card (Fiber f y) = C) : Nat.card α = Nat.card β * C := by
  let := Fintype.ofFinite β
  rw [card_fibers f, Nat.card_eq_fintype_card]
  simp [h]

/-- Project the first matrix from a tuple and retain the sum constraint on its tail. -/
def sumConsEquiv {F : Type*} [Field F] {n k : ℕ}
    (r : Fin (k+1) → ℕ) (T : Mat F n) :
    SumClass r T ≃ Σ A : RankClass F n (r 0), SumClass (r ∘ Fin.succ) (T - A.1) where
  toFun X :=
    ⟨⟨X.1 0, X.2.1 0⟩, ⟨X.1 ∘ Fin.succ, (fun i => X.2.1 i.succ), by
      have h := X.2.2
      rw [Fin.sum_univ_succ] at h
      exact eq_sub_of_add_eq (add_comm (X.1 0) _ ▸ h)⟩⟩
  invFun X := ⟨Fin.cons X.1.1 X.2.1, by
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using X.1.2
      · simpa using X.2.2.1 j
    · rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ, X.2.2.2, add_sub_cancel]⟩
  left_inv X := Subtype.ext (Fin.cons_self_tail _)
  right_inv X := by
    obtain ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ := X
    rfl

theorem sumCount_cons {F : Type*} [Field F] [Finite F] {n k : ℕ}
    (r : Fin (k+1) → ℕ) (T : Mat F n) :
    let := Fintype.ofFinite (RankClass F n (r 0))
    sumCount r T = ∑ A : RankClass F n (r 0), sumCount (r ∘ Fin.succ) (T - A.1) := by
  classical
  let := Fintype.ofFinite (RankClass F n (r 0))
  change sumCount r T = _
  exact (Nat.card_congr (sumConsEquiv r T)).trans Nat.card_sigma

end MatrixSum
```

## MatrixSumTarget.lean

```lean
import MatrixSumCore

open Matrix

namespace MatrixSum

variable {F : Type*} [Field F]

/-- The tuple count on any common row and column index type. -/
private noncomputable def indexedSumCount {ι : Type*} [Fintype ι] {k : ℕ}
    (r : Fin k → ℕ) (T : Matrix ι ι F) : ℕ :=
  Nat.card {X : Fin k → Matrix ι ι F // (∀ i, (X i).rank = r i) ∧ ∑ i, X i = T}

private theorem indexedSumCount_congr {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    (r : Fin k → ℕ) (e : Matrix ι ι F ≃+ Matrix κ κ F)
    (h : ∀ X, (e X).rank = X.rank) (T : Matrix ι ι F) :
    indexedSumCount r T = indexedSumCount r (e T) := by
  let pointwise : (Fin k → Matrix ι ι F) ≃ (Fin k → Matrix κ κ F) :=
    Equiv.piCongrRight (fun _ => e.toEquiv)
  unfold indexedSumCount
  apply Nat.card_congr (pointwise.subtypeEquiv ?_)
  intro X
  change ((∀ i, (X i).rank = r i) ∧ ∑ i, X i = T) ↔
    ((∀ i, (e (X i)).rank = r i) ∧ ∑ i, e (X i) = e T)
  simp_rw [h, ← map_sum e, e.injective.eq_iff]

private def multiplyUnitsEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L R : (Matrix ι ι F)ˣ) : Matrix ι ι F ≃+ Matrix ι ι F where
  toFun X := (L : Matrix ι ι F) * X * R
  invFun X := (↑L⁻¹ : Matrix ι ι F) * X * ↑R⁻¹
  left_inv X := by simp [Matrix.mul_assoc]
  right_inv X := by simp [Matrix.mul_assoc]
  map_add' X Y := by simp [mul_add, add_mul]

private theorem indexedSumCount_normalForm {n k d : ℕ} (r : Fin k → ℕ)
    (T : Mat F n) (hd : T.rank = d) :
    indexedSumCount r T =
      indexedSumCount r (fromBlocks (1 : Mat F d) 0 0 (0 : Mat F (Fintype.card (Fin n)-d))) := by
  subst d
  classical
  obtain ⟨V, U, e, hV, hU, he⟩ := Matrix.exists_rank_normal_form T
  obtain ⟨L, rfl⟩ := hV
  obtain ⟨R, rfl⟩ := hU
  let m := multiplyUnitsEquiv L R
  have hmul (X : Mat F n) : (m X).rank = X.rank := by
    change ((L : Mat F n) * X * R).rank = X.rank
    rw [Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det]
    · exact (Matrix.isUnit_iff_isUnit_det _).mp L.isUnit
    · exact (Matrix.isUnit_iff_isUnit_det _).mp R.isUnit
  let f := (Matrix.reindexAddEquiv F e e)
  have hreindex (X : Mat F n) : (f X).rank = X.rank :=
    Matrix.rank_reindex e e X
  refine (indexedSumCount_congr r m hmul T).trans
    ((indexedSumCount_congr r f hreindex (m T)).trans ?_)
  congr 1
  change (Matrix.reindex e e) ((L : Mat F n) * T * (R : Mat F n)) = _
  rw [he]
  ext a b
  simp [Matrix.reindex_apply]

/-- This is why the fixed-target count can use a target matrix in Conjecture 5.5. -/
theorem sumCount_eq_of_rank_eq {n k : ℕ} (r : Fin k → ℕ) {T U : Mat F n}
    (h : T.rank = U.rank) : sumCount r T = sumCount r U :=
  (indexedSumCount_normalForm r T h).trans (indexedSumCount_normalForm r U rfl).symm

end MatrixSum
```

## MatrixSumConditioning.lean

```lean
import MatrixSumCore

open Finset Matrix Function LinearMap Module

namespace MatrixSum

variable {F : Type*} [Field F]

abbrev InjectiveMatrix (F : Type*) [Field F] (n r : ℕ) :=
  {A : Matrix (Fin n) (Fin r) F // Injective A.mulVecLin}

abbrev SurjectiveMatrix (F : Type*) [Field F] (r n : ℕ) :=
  {A : Matrix (Fin r) (Fin n) F // Surjective A.mulVecLin}

noncomputable def injectiveCount (F : Type*) [Field F] (n r : ℕ) : ℕ :=
  Nat.card (InjectiveMatrix F n r)

local notation "Q" => Fintype.card F

theorem injective_iff_rank {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    Injective A.mulVecLin ↔ A.rank = n := by
  change Injective A.mulVecLin ↔ finrank F (LinearMap.range A.mulVecLin) = n
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  simp only [finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega

theorem surjective_iff_rank {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    Surjective A.mulVecLin ↔ A.rank = m := by
  change Surjective A.mulVecLin ↔ finrank F (LinearMap.range A.mulVecLin) = m
  rw [← LinearMap.range_eq_top]
  constructor
  · intro h
    rw [h, finrank_top, finrank_fintype_fun_eq_card, Fintype.card_fin]
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rwa [finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem injective_iff_cols {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    Injective A.mulVecLin ↔ LinearIndependent F A.col := by
  rw [injective_iff_rank, Matrix.rank_eq_finrank_span_cols,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, Fintype.card_fin, eq_comm]

variable [Fintype F]

theorem fieldCard_ge_two : 2 ≤ Q := Fintype.one_lt_card

theorem injectiveCount_eq (n r : ℕ) (hr : r ≤ n) :
    injectiveCount F n r = ∏ i ∈ range r, (Q^n - Q^i) := by
  let colEquiv : Matrix (Fin n) (Fin r) F ≃ (Fin r → Space F n) :=
    ⟨Matrix.col, fun v i j => v j i, fun _ => rfl, fun _ => rfl⟩
  have hc := card_linearIndependent (K := F) (V := Space F n)
    (show r ≤ finrank F (Space F n) by simpa [finrank_fintype_fun_eq_card] using hr)
  rw [finrank_fintype_fun_eq_card, Fintype.card_fin] at hc
  rw [injectiveCount, Nat.card_congr
    (colEquiv.subtypeEquiv (q := fun v => LinearIndependent F v) injective_iff_cols), hc]
  exact Fin.prod_univ_eq_prod_range (fun i : ℕ => Q^n - Q^i) r

omit [Fintype F] in
theorem surjectiveCount_eq (r n : ℕ) :
    Nat.card (SurjectiveMatrix F r n) = injectiveCount F n r := by
  let e : Matrix (Fin r) (Fin n) F ≃ Matrix (Fin n) (Fin r) F :=
    ⟨Matrix.transpose, Matrix.transpose, Matrix.transpose_transpose, Matrix.transpose_transpose⟩
  exact Nat.card_congr (e.subtypeEquiv (q := fun A => Injective A.mulVecLin) fun A => by
    change Surjective A.mulVecLin ↔ Injective A.transpose.mulVecLin
    rw [surjective_iff_rank, injective_iff_rank, Matrix.rank_transpose])

/-- Proportion of ordered columns which are linearly independent. -/
def proportion (q : ℚ) (n r : ℕ) : ℚ :=
  ∏ i ∈ range r, (1 - q^i / q^n)

theorem proportion_nonneg {q : ℚ} (hq : 1 ≤ q) {n r : ℕ} (hr : r ≤ n) :
    0 ≤ proportion q n r := by
  have hq0 : 0 < q := by linarith
  apply Finset.prod_nonneg
  intro i hi
  rw [mem_range] at hi
  apply sub_nonneg.mpr
  exact (div_le_one (pow_pos hq0 _)).2 (pow_le_pow_right₀ hq (by omega))

theorem injectiveCount_normalized (n r : ℕ) (hr : r ≤ n) :
    (injectiveCount F n r : ℚ) = (Q : ℚ)^(n*r) * proportion Q n r := by
  have hq : 1 ≤ Q := (by decide : 1 ≤ 2).trans fieldCard_ge_two
  have hq0 : (Q : ℚ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hpow : ((Q : ℚ)^n)^r = ∏ _i ∈ range r, (Q : ℚ)^n := by simp
  rw [injectiveCount_eq n r hr, Nat.cast_prod, proportion, pow_mul, hpow, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  have hi' : i ≤ n := by rw [mem_range] at hi; omega
  rw [Nat.cast_sub (pow_le_pow_right₀ hq hi'), Nat.cast_pow, Nat.cast_pow]
  field_simp

/-- Sum of the omitted fractions is bounded by the next power. -/
theorem proportion_ge_sub {q : ℚ} (hq : 2 ≤ q) (n : ℕ) :
    ∀ r ≤ n, 1 - q^r / q^n ≤ proportion q n r := by
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  intro r
  induction r with
  | zero => simp [proportion]; positivity
  | succ r ih =>
    intro hr
    let x := q^r / q^n
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hx1 : x ≤ 1 :=
      (div_le_one (pow_pos hq0 _)).2 (pow_le_pow_right₀ hq1 (by omega))
    rw [proportion, prod_range_succ, pow_succ, mul_comm (q^r) q, mul_div_assoc]
    change 1 - q * x ≤ proportion q n r * (1 - x)
    calc
      _ ≤ (1 - x) * (1 - x) := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) hx, sq_nonneg x]
      _ ≤ _ := mul_le_mul_of_nonneg_right (ih (by omega)) (sub_nonneg.mpr hx1)

theorem proportion_square_ge_quarter {q : ℚ} (hq : 2 ≤ q) (n : ℕ) :
    1 / 4 ≤ proportion q n n := by
  cases n with
  | zero => norm_num [proportion]
  | succ n =>
    have hq0 : 0 < q := by linarith
    have hx : q^n / q^(n+1) ≤ 1/2 := by
      rw [pow_succ, mul_comm (q^n) q, div_mul_eq_div_div_swap,
        div_self (pow_ne_zero n (ne_of_gt hq0)), one_div_le_one_div hq0 (by norm_num)]
      exact hq
    have hp := proportion_ge_sub hq (n+1) n (by omega)
    rw [proportion, prod_range_succ]
    change 1/4 ≤ proportion q (n+1) n * (1 - q^n / q^(n+1))
    calc
      (1:ℚ)/4 = (1/2)*(1/2) := by norm_num
      _ ≤ _ := mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)

theorem proportion_pow_ge {q : ℚ} (hq : 2 ≤ q) {n r : ℕ} (hr : r ≤ n) :
    proportion q n n ^ r ≤ proportion q n r ^ n := by
  let a := fun j : ℕ => 1 - q^j / q^n
  let t := n-r
  have hnt : r+t = n := Nat.add_sub_of_le hr
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have ha {i j : ℕ} (h : i ≤ j) : a j ≤ a i :=
    sub_le_sub_left (div_le_div_of_nonneg_right (pow_le_pow_right₀ hq1 h) (by positivity)) _
  have hapos {j : ℕ} (h : j ≤ n) : 0 ≤ a j :=
    sub_nonneg.mpr ((div_le_one (pow_pos hq0 _)).2 (pow_le_pow_right₀ hq1 h))
  let tail := ∏ j ∈ range t, a (r+j)
  have hsplit : proportion q n n = proportion q n r * tail := by
    unfold proportion
    rw [← Finset.prod_range_add, hnt]
  have hhead : a r ^ r ≤ proportion q n r := by
    have he : a r ^ r = ∏ _i ∈ range r, a r := by simp
    rw [he]
    apply prod_le_prod₀
    · intro i _
      exact hapos hr
    · intro i hi
      exact ha (mem_range.mp hi).le
  have htail : tail ≤ a r ^ t := by
    have he : a r ^ t = ∏ _i ∈ range t, a r := by simp
    rw [he]
    apply prod_le_prod₀
    · intro i hi
      exact hapos (by have := mem_range.mp hi; omega)
    · intro i _
      exact ha (Nat.le_add_right ..)
  have hp := proportion_nonneg hq1 hr
  have ht : 0 ≤ tail := prod_nonneg (by
    intro i hi
    exact hapos (by have := mem_range.mp hi; omega))
  calc
    _ = proportion q n r ^ r * tail ^ r := by rw [hsplit, mul_pow]
    _ ≤ proportion q n r ^ r * (a r ^ t)^r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htail _) (pow_nonneg hp _)
    _ ≤ proportion q n r ^ r * proportion q n r ^ t := by
      rw [← pow_mul, Nat.mul_comm t r, pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg (hapos hr) _) hhead _)
        (pow_nonneg hp _)
    _ = _ := by rw [← pow_add, hnt]

theorem proportion_tuple_ge {q : ℚ} (hq : 2 ≤ q) {n k : ℕ}
    (hn : 0 < n) (r : Fin k → ℕ) (hr : ∀ i, r i ≤ n) (hR : ∑ i, r i ≤ 3*n) :
    1/64 ≤ ∏ i, proportion q n (r i) := by
  have hp : ∀ i, 0 ≤ proportion q n (r i) :=
    fun i => proportion_nonneg (by linarith) (hr i)
  apply (pow_le_pow_iff_left₀ (by norm_num : (0:ℚ) ≤ 1/64) (prod_nonneg (fun i _ => hp i))
    (Nat.ne_of_gt hn)).mp
  rw [← Finset.prod_pow]
  calc
    (1/64 : ℚ)^n = (1/4 : ℚ)^(3*n) := by rw [pow_mul]; norm_num
    _ ≤ (1/4 : ℚ)^(∑ i, r i) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hR
    _ = ∏ i, (1/4 : ℚ)^(r i) := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ =>
      (pow_le_pow_left₀ (by norm_num) (proportion_square_ge_quarter hq n) _).trans
        (proportion_pow_ge hq (hr i)))

theorem injective_tuple_bound {n k : ℕ}
    (hn : 0 < n) (r : Fin k → ℕ) (hr : ∀ i, r i ≤ n) (hR : ∑ i, r i ≤ 3*n) :
    Q^(2*n*(∑ i, r i)) ≤ 4096 * ∏ i, injectiveCount F n (r i)^2 := by
  have hq : (2 : ℚ) ≤ Q := by exact_mod_cast (fieldCard_ge_two (F := F))
  have h := proportion_tuple_ge hq hn r hr hR
  have hs : (1/4096 : ℚ) ≤ (∏ i, proportion Q n (r i))^2 := by
    nlinarith [sq_nonneg ((∏ i, proportion Q n (r i)) - 1/64)]
  have hz : (0 : ℚ) ≤ (Q : ℚ)^(2*n*(∑ i, r i)) := by positivity
  suffices hcast : ((Q^(2*n*(∑ i, r i)) : ℕ) : ℚ) ≤
      ((4096 * ∏ i, injectiveCount F n (r i)^2 : ℕ) : ℚ) by exact_mod_cast hcast
  push_cast
  simp_rw [injectiveCount_normalized n _ (hr _), mul_pow]
  rw [Finset.prod_mul_distrib]
  have hP : (∏ i, proportion Q n (r i)^2) = (∏ i, proportion Q n (r i))^2 := by
    exact Finset.prod_pow ..
  rw [hP]
  have he (i : Fin k) : (((Q : ℚ)^(n*r i))^2) = (Q : ℚ)^(2*n*r i) := by
    rw [← pow_mul]
    congr 1
    ring
  simp_rw [he]
  rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
  nlinarith [mul_nonneg hz (sub_nonneg.mpr hs)]

end MatrixSum
```

## MatrixSumFactorization.lean

```lean
import MatrixSumConditioning

open Function Matrix Module LinearMap Finset

namespace MatrixSum

variable {F : Type*} [Field F]

/-- A square injective matrix and the associated automorphism. -/
noncomputable def automorphismEquiv (r : ℕ) :
    InjectiveMatrix F r r ≃ (Space F r ≃ₗ[F] Space F r) where
  toFun A := LinearEquiv.ofInjectiveEndo A.1.mulVecLin A.2
  invFun e := ⟨e.toLinearMap.toMatrix', by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    exact e.injective⟩
  left_inv A := by
    apply Subtype.ext
    exact Matrix.toLin'.symm_apply_apply A.1
  right_inv e := by
    apply LinearEquiv.ext
    intro x
    change (Matrix.toLin' (e.toLinearMap.toMatrix')) x = e x
    rw [Matrix.toLin'_toMatrix']
    rfl

theorem basisCount_pos [Finite F] (r : ℕ) : 0 < injectiveCount F r r := by
  rw [injectiveCount]
  let : Nonempty (InjectiveMatrix F r r) := ⟨(automorphismEquiv r).symm (LinearEquiv.refl F _)⟩
  exact Nat.card_pos

/-- An injective matrix with specified range is an isomorphism onto that range. -/
noncomputable def rangeFiberEquiv {n r : ℕ} (H : Submodule F (Space F n)) :
    Fiber (fun A : InjectiveMatrix F n r => LinearMap.range A.1.mulVecLin) H ≃
      (Space F r ≃ₗ[F] H) where
  toFun A := A.2 ▸ LinearEquiv.ofInjective A.1.1.mulVecLin A.1.2
  invFun e := by
    let f := H.subtype.comp e.toLinearMap
    have hf : Injective f := H.subtype_injective.comp e.injective
    have hH : LinearMap.range f = H := by
      rw [LinearMap.range_comp_of_range_eq_top _ e.range, Submodule.range_subtype]
    refine ⟨⟨f.toMatrix', ?_⟩, ?_⟩
    · rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
      exact hf
    · change LinearMap.range (Matrix.toLin' f.toMatrix') = H
      rw [Matrix.toLin'_toMatrix']
      exact hH
  left_inv A := by
    obtain ⟨⟨A, hA⟩, rfl⟩ := A
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.toLin'.symm_apply_apply A
  right_inv e := by
    -- The underlying values of the range-restricted map are those of the original map.
    have hc (A : InjectiveMatrix F n r) (h : LinearMap.range A.1.mulVecLin = H)
        (x : Space F r) :
        ((h ▸ LinearEquiv.ofInjective A.1.mulVecLin A.2 : Space F r ≃ₗ[F] H) x :
          Space F n) = A.1.mulVecLin x := by
      subst H
      rfl
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rw [hc]
    change Matrix.toLin' (H.subtype.comp e.toLinearMap).toMatrix' x = (e x : Space F n)
    rw [Matrix.toLin'_toMatrix']
    rfl

theorem card_rangeFiber {n r : ℕ} (H : Submodule F (Space F n)) (h : finrank F H = r) :
    Nat.card (Fiber (fun A : InjectiveMatrix F n r => LinearMap.range A.1.mulVecLin) H) =
      injectiveCount F r r := by
  let e : Space F r ≃ₗ[F] H := LinearEquiv.ofFinrankEq _ _ (by
    rw [finrank_fintype_fun_eq_card, Fintype.card_fin, h])
  let E : (Space F r ≃ₗ[F] H) ≃ (Space F r ≃ₗ[F] Space F r) :=
    ⟨fun f => f.trans e.symm, fun f => f.trans e,
      fun f => by ext x; simp, fun f => by ext x; simp⟩
  exact Nat.card_congr ((rangeFiberEquiv H).trans (E.trans (automorphismEquiv r).symm))

abbrev Factors (F : Type*) [Field F] (n r : ℕ) :=
  InjectiveMatrix F n r × SurjectiveMatrix F r n

theorem range_product {n r : ℕ} (A : Factors F n r) :
    LinearMap.range (A.1.1 * A.2.1).mulVecLin = LinearMap.range A.1.1.mulVecLin := by
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr A.2.2)]

def factorProduct {n r : ℕ} (A : Factors F n r) : RankClass F n r :=
  ⟨A.1.1 * A.2.1, by
    change finrank F (LinearMap.range (A.1.1 * A.2.1).mulVecLin) = r
    rw [range_product A]
    exact (injective_iff_rank _).mp A.1.2⟩

theorem factorFiber_card {n r : ℕ} (X : RankClass F n r) :
    Nat.card (Fiber factorProduct X) = injectiveCount F r r := by
  let H := LinearMap.range X.1.mulVecLin
  let f (A : Fiber factorProduct X) :
      Fiber (fun U : InjectiveMatrix F n r => LinearMap.range U.1.mulVecLin) H :=
    ⟨A.1.1, by
      change LinearMap.range A.1.1.1.mulVecLin = H
      rw [← range_product A.1]
      exact congrArg (fun B : RankClass F n r => LinearMap.range B.1.mulVecLin) A.2⟩
  have hf : Bijective f := by
    constructor
    · intro A B h
      have hU : A.1.1 = B.1.1 := congrArg Subtype.val h
      have hprod : A.1.1.1 * A.1.2.1 = B.1.1.1 * B.1.2.1 :=
        congrArg Subtype.val (A.2.trans B.2.symm)
      rw [← hU] at hprod
      have hV : A.1.2 = B.1.2 := by
        apply Subtype.ext
        apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro x
        apply A.1.1.2
        have hh := congrArg (fun M : Mat F n => M.toLin' x) hprod
        change Matrix.toLin' (A.1.1.1 * A.1.2.1) x =
          Matrix.toLin' (A.1.1.1 * B.1.2.1) x at hh
        rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply] at hh
        exact hh
      exact Subtype.ext (Prod.ext hU hV)
    · intro U
      let e := rangeFiberEquiv H U
      have he (x : Space F r) : (e x : Space F n) = U.1.1.mulVecLin x := by
        change (((U.2 ▸ LinearEquiv.ofInjective U.1.1.mulVecLin U.1.2 : Space F r ≃ₗ[F] H) x : H) :
          Space F n) = _
        generalize hH : H = H' at U ⊢
        obtain ⟨U, rfl⟩ := U
        rfl
      let v := e.symm.toLinearMap.comp X.1.mulVecLin.rangeRestrict
      let V : SurjectiveMatrix F r n := ⟨v.toMatrix', by
        rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
        exact e.symm.surjective.comp (LinearMap.range_eq_top.mp X.1.mulVecLin.range_rangeRestrict)⟩
      have h : factorProduct (U.1, V) = X := by
        apply Subtype.ext
        apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro x
        change Matrix.toLin' (U.1.1 * v.toMatrix') x = X.1.mulVecLin x
        rw [Matrix.toLin'_mul_apply, Matrix.toLin'_toMatrix', Matrix.toLin'_apply', ← he]
        change (e (e.symm (X.1.mulVecLin.rangeRestrict x)) : Space F n) = _
        rw [e.apply_symm_apply]
        rfl
      exact ⟨⟨(U.1, V), h⟩, Subtype.ext rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), card_rangeFiber H X.2]

variable [Fintype F]

theorem card_factors (n r : ℕ) :
    injectiveCount F n r ^ 2 = rankCount F n r * injectiveCount F r r := by
  have h := card_fibers_const (factorProduct (F := F) (n := n) (r := r))
    (injectiveCount F r r) factorFiber_card
  rwa [Nat.card_prod, surjectiveCount_eq, ← injectiveCount, ← pow_two] at h

abbrev ProductFiber (F : Type*) [Field F] (n : ℕ) (ι : Type*) [Fintype ι] (T : Mat F n) :=
  Fiber (fun P : Matrix (Fin n) ι F × Matrix ι (Fin n) F => P.1 * P.2) T

noncomputable def productCount (F : Type*) [Field F] (n : ℕ)
    (ι : Type*) [Fintype ι] (T : Mat F n) : ℕ :=
  Nat.card (ProductFiber F n ι T)

theorem blocks_bound {n k : ℕ} (r : Fin k → ℕ) (T : Mat F n) :
    sumCount r T * (∏ i, injectiveCount F (r i) (r i)) ≤
      productCount F n (Σ i, Fin (r i)) T := by
  classical
  let S := {A : ∀ i, Factors F n (r i) // ∑ i, (factorProduct (A i)).1 = T}
  let f (A : S) : SumClass r T :=
    ⟨fun i => (factorProduct (A.1 i)).1, fun i => (factorProduct (A.1 i)).2, A.2⟩
  have fibers (X : SumClass r T) :
      Nat.card (Fiber f X) = ∏ i, injectiveCount F (r i) (r i) := by
    let Y : ∀ i, RankClass F n (r i) := fun i => ⟨X.1 i, X.2.1 i⟩
    let e : Fiber f X ≃ ∀ i, Fiber factorProduct (Y i) :=
      { toFun := fun A i => ⟨A.1.1 i, Subtype.ext (congrFun (congrArg Subtype.val A.2) i)⟩
        invFun := fun A => ⟨⟨fun i => (A i).1, by
          change ∑ i, (factorProduct (A i).1).1 = T
          simp_rw [fun i => congrArg Subtype.val (A i).2]
          exact X.2.2⟩, Subtype.ext (funext fun i => congrArg Subtype.val (A i).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_pi]
    simp_rw [factorFiber_card]
  unfold sumCount productCount
  rw [← card_fibers_const f _ fibers]
  let pack (A : S) : ProductFiber F n (Σ i, Fin (r i)) T :=
    ⟨(fun j s => (A.1 s.1).1.1 j s.2, fun s j => (A.1 s.1).2.1 s.2 j), by
      ext a b
      change (∑ s : Σ i, Fin (r i),
        (A.1 s.1).1.1 a s.2 * (A.1 s.1).2.1 s.2 b) = T a b
      rw [Fintype.sum_sigma]
      have sumApply := congrArg (fun M : Mat F n => M a b) A.2
      simpa only [Matrix.mul_apply, Matrix.sum_apply, factorProduct] using sumApply⟩
  apply Nat.card_le_card_of_injective pack
  intro A B h
  apply Subtype.ext
  funext i
  apply Prod.ext <;> apply Subtype.ext <;> ext a b
  · exact congrArg (fun P : ProductFiber F n (Σ i, Fin (r i)) T => P.1.1 a ⟨i, b⟩) h
  · exact congrArg (fun P : ProductFiber F n (Σ i, Fin (r i)) T => P.1.2 ⟨i, a⟩ b) h

end MatrixSum
```

## MatrixSumProduct.lean

```lean
import MatrixSumFactorization
import Mathlib.Algebra.Ring.GeomSum

open Function Matrix Module LinearMap Finset

namespace MatrixSum

variable {F : Type*} [Field F] [Fintype F]

local notation "Q" => Fintype.card F

abbrev Subspaces (F : Type*) [Field F] (n d : ℕ) :=
  {H : Submodule F (Space F n) // finrank F H = d}

instance {n : ℕ} : Finite (Submodule F (Space F n)) :=
  Finite.of_injective (fun H => (H : Set (Space F n))) SetLike.coe_injective

theorem subspace_count_le {n d : ℕ} (hd : d ≤ n) :
    Nat.card (Subspaces F n d) ≤ 4 * Q^(d*(n-d)) := by
  let f (A : InjectiveMatrix F n d) : Subspaces F n d :=
    ⟨LinearMap.range A.1.mulVecLin, (injective_iff_rank _).mp A.2⟩
  have hcard := card_fibers_const f (injectiveCount F d d) (fun H => by
    let e : Fiber f H ≃ Fiber (fun A : InjectiveMatrix F n d => LinearMap.range A.1.mulVecLin) H.1 :=
      Equiv.subtypeEquivRight fun _ => Subtype.ext_iff
    rw [Nat.card_congr e, card_rangeFiber H.1 H.2])
  have hup : Nat.card (InjectiveMatrix F n d) ≤ Q^(d*n) := by
    have h := Nat.card_le_card_of_injective
      (Subtype.val : InjectiveMatrix F n d → Matrix (Fin n) (Fin d) F) Subtype.val_injective
    rw [Matrix.card_matrix, Nat.card_fin, Nat.card_fin, Nat.card_eq_fintype_card (α := F)] at h
    exact h
  have hlow : Q^(d*d) ≤ 4 * injectiveCount F d d := by
    have hQ : (2 : ℚ) ≤ Q := by exact_mod_cast (fieldCard_ge_two (F := F))
    have h := proportion_square_ge_quarter hQ d
    have hpow : (0 : ℚ) ≤ (Q : ℚ)^(d*d) := by positivity
    have hc : (Q : ℚ)^(d*d) ≤ 4 * (injectiveCount F d d : ℚ) := by
      rw [injectiveCount_normalized d d le_rfl]
      nlinarith [mul_nonneg hpow (sub_nonneg.mpr h)]
    exact_mod_cast hc
  have hpow : Q^(d*n) = Q^(d*(n-d)) * Q^(d*d) := by
    rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hd]
  have hpos : 0 < Q^(d*d) := pow_pos Fintype.card_pos _
  apply Nat.le_of_mul_le_mul_right (hc := hpos)
  calc
    _ ≤ Nat.card (Subspaces F n d) * (4 * injectiveCount F d d) :=
      Nat.mul_le_mul_left _ hlow
    _ = 4 * Nat.card (InjectiveMatrix F n d) := by rw [hcard]; ring
    _ ≤ 4 * Q^(d*n) := Nat.mul_le_mul_left _ hup
    _ = _ := by rw [hpow, Nat.mul_assoc]

omit [Fintype F] in
/-- An affine fiber has at most as many elements as the kernel. -/
theorem linearFiber_le {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module F V]
    [Module F W] [Finite V] (f : V →ₗ[F] W) (y : W) :
    Nat.card (Fiber f y) ≤ Nat.card (LinearMap.ker f) := by
  cases isEmpty_or_nonempty (Fiber f y) with
  | inl h =>
    let := h
    simp
  | inr h =>
    let x := h.some
    let translate (a : Fiber f y) : LinearMap.ker f :=
      ⟨a.1 - x.1, by rw [LinearMap.mem_ker, map_sub, a.2, x.2, sub_self]⟩
    exact Nat.card_le_card_of_injective translate
      (fun a b hab => Subtype.ext (sub_left_injective (congrArg Subtype.val hab)))

variable {ι : Type*} [Fintype ι] {n : ℕ}

local notation "R" => Fintype.card ι

theorem left_count_le (H : Submodule F (Space F n)) :
    Nat.card (Fiber (fun W : Matrix (Fin n) ι F => LinearMap.range W.mulVecLin) H) ≤
      Q^(finrank F H * R) := by
  let columns (W : Fiber (fun W : Matrix (Fin n) ι F => LinearMap.range W.mulVecLin) H) :
      ι → H := fun i => ⟨W.1.col i, by
        have hw : LinearMap.range W.1.mulVecLin = H := W.2
        have hc : W.1.col i ∈ LinearMap.range W.1.mulVecLin := by
          rw [Matrix.range_mulVecLin]
          exact Submodule.subset_span (Set.mem_range_self i)
        exact Eq.mp (congrArg (fun K : Submodule F (Space F n) => W.1.col i ∈ K) hw) hc⟩
  have h := Nat.card_le_card_of_injective columns (fun W W' h => by
    apply Subtype.ext
    ext a b
    exact congrFun (congrArg Subtype.val (congrFun h b)) a)
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ι),
    Module.natCard_eq_pow_finrank (K := F) (V := H), Nat.card_eq_fintype_card (α := F), ← pow_mul] at h
  exact h

theorem right_count_le (W : Matrix (Fin n) ι F) (T : Mat F n) :
    Nat.card (Fiber (fun Y : Matrix ι (Fin n) F => W * Y) T) ≤ Q^((R-W.rank)*n) := by
  let f (Y : Fiber (fun Y : Matrix ι (Fin n) F => W * Y) T) :
      ∀ j : Fin n, Fiber W.mulVecLin (T.col j) :=
    fun j => ⟨Y.1.col j, by
      ext i
      exact congrArg (fun M : Mat F n => M i j) Y.2⟩
  have hf := Nat.card_le_card_of_injective f (fun Y Y' h => by
    apply Subtype.ext
    ext a b
    exact congrFun (congrArg Subtype.val (congrFun h b)) a)
  rw [Nat.card_pi] at hf
  have hdim : finrank F (LinearMap.ker W.mulVecLin) = R-W.rank := by
    have h := W.mulVecLin.finrank_range_add_finrank_ker
    rw [finrank_fintype_fun_eq_card] at h
    change W.rank + _ = _ at h
    omega
  have hcols (j : Fin n) :
      Nat.card (Fiber W.mulVecLin (T.col j)) ≤ Q^(R-W.rank) := by
    have h := linearFiber_le W.mulVecLin (T.col j)
    rw [Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker W.mulVecLin), hdim, Nat.card_eq_fintype_card (α := F)] at h
    exact h
  calc
    _ ≤ _ := hf
    _ ≤ ∏ _j : Fin n, Q^(R-W.rank) := Finset.prod_le_prod (fun j _ => hcols j)
    _ = _ := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul]

omit [Fintype F] in
theorem rank_le_rows (W : Matrix (Fin n) ι F) : W.rank ≤ n := by
  have h := (LinearMap.range W.mulVecLin).finrank_le
  rwa [finrank_fintype_fun_eq_card, Fintype.card_fin] at h

noncomputable def codimension (W : Matrix (Fin n) ι F) : Fin (n+1) :=
  ⟨n-W.rank, by omega⟩

theorem product_stratum_le (T : Mat F n) (s : Fin (n+1)) :
    Nat.card (Fiber (fun P : ProductFiber F n ι T => codimension P.1.1) s) ≤
      4 * Q^((n-s.val)*s.val) * (Q^((n-s.val)*R) * Q^((R-(n-s.val))*n)) := by
  let S := Fiber (fun P : ProductFiber F n ι T => codimension P.1.1) s
  let d := n-s.val
  have le_n : s.val ≤ n := Nat.le_of_lt_succ s.isLt
  let image (P : S) : Subspaces F n d :=
    ⟨LinearMap.range P.1.1.1.mulVecLin, by
      have hs : n - P.1.1.1.rank = s.val := congrArg Fin.val P.2
      have hd := rank_le_rows P.1.1.1
      change P.1.1.1.rank = d
      dsimp [d]
      omega⟩
  have fiber_le (H : Subspaces F n d) :
      Nat.card (Fiber image H) ≤ Q^(d*R) * Q^((R-d)*n) := by
    let WType := Fiber (fun W : Matrix (Fin n) ι F => LinearMap.range W.mulVecLin) H.1
    let left (P : Fiber image H) : WType :=
      ⟨P.1.1.1.1, congrArg Subtype.val P.2⟩
    have hright (W : WType) : Nat.card (Fiber left W) ≤ Q^((R-d)*n) := by
      let right (P : Fiber left W) : Fiber (fun Y : Matrix ι (Fin n) F => W.1 * Y) T :=
        ⟨P.1.1.1.1.2, by
          have hw : P.1.1.1.1.1 = W.1 := congrArg Subtype.val P.2
          rw [← hw]
          exact P.1.1.1.2⟩
      have h := Nat.card_le_card_of_injective right (fun A B hab => by
        have hw : A.1.1.1.1.1 = B.1.1.1.1.1 :=
          congrArg Subtype.val (A.2.trans B.2.symm)
        have hy : A.1.1.1.1.2 = B.1.1.1.1.2 := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext (Prod.ext hw hy)))))
      have hd : W.1.rank = d := by
        change finrank F (LinearMap.range W.1.mulVecLin) = d
        have hw : LinearMap.range W.1.mulVecLin = H.1 := W.2
        rw [hw]
        exact H.2
      have hb := right_count_le W.1 T
      rw [hd] at hb
      exact h.trans hb
    have hleft := left_count_le (ι := ι) H.1
    rw [H.2] at hleft
    exact (card_fibers_le left _ hright).trans (Nat.mul_le_mul_right _ hleft)
  have hdim := subspace_count_le (F := F) (Nat.sub_le n s.val : d ≤ n)
  have hn : n-d = s.val := by dsimp [d]; omega
  rw [hn] at hdim
  exact (card_fibers_le image _ fiber_le).trans (Nat.mul_le_mul_right _ hdim)

theorem exponent_le {n width s : ℕ} (hR : 2*n ≤ width) (hs : s ≤ n) :
    n*n + (n-s)*s + (n-s)*width + (width-(n-s))*n + s ≤ 2*n*width := by
  let d := n-s
  let e := width-2*n
  have hn : n = d+s := by dsimp [d]; omega
  have hE : width = 2*n+e := by dsimp [e]; omega
  have hD : width-d = d+2*s+e := by omega
  change n*n + d*s + d*width + (width-d)*n + s ≤ 2*n*width
  have heq : n*n + d*s + d*width + (width-d)*n + s*s + e*s = 2*n*width := by
    rw [hD, hE, hn]
    ring
  have hss : s ≤ s*s := by
    by_cases h : s = 0
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h)
  omega

theorem halfGeom_le (m : ℕ) : ∑ j ∈ range m, (1/2 : ℚ)^j ≤ 2 := by
  have h := geom_sum_mul_of_le_one (n := m) (show (1/2 : ℚ) ≤ 1 by norm_num)
  nlinarith [pow_nonneg (by norm_num : (0:ℚ) ≤ 1/2) m]

theorem product_bound (T : Mat F n) (hR : 2*n ≤ R) :
    Q^(n*n) * productCount F n ι T ≤ 8 * Q^(2*n*R) := by
  classical
  have hQ : (2 : ℚ) ≤ Q := by exact_mod_cast (fieldCard_ge_two (F := F))
  have hQ1 : (1 : ℚ) ≤ Q := by linarith
  suffices hcast : ((Q^(n*n) * productCount F n ι T : ℕ) : ℚ) ≤
      ((8 * Q^(2*n*R) : ℕ) : ℚ) by exact_mod_cast hcast
  simp only [productCount, card_fibers (fun P : ProductFiber F n ι T => codimension P.1.1)]
  push_cast
  rw [Finset.mul_sum]
  have hterm (s : Fin (n+1)) :
      (Q : ℚ)^(n*n) *
          (Nat.card (Fiber (fun P : ProductFiber F n ι T => codimension P.1.1) s) : ℚ) ≤
        4 * (Q : ℚ)^(2*n*R) * (1/2 : ℚ)^s.val := by
    let d := n-s.val
    let a := n*n + d*s.val + d*R + (R-d)*n
    have hA : a + s.val ≤ 2*n*R := exponent_le hR (Nat.le_of_lt_succ s.isLt)
    have hbound : (Q : ℚ)^a ≤ (Q : ℚ)^(2*n*R) * (1/2 : ℚ)^s.val := by
      rw [div_pow, one_pow, mul_one_div]
      apply (le_div_iff₀ (by positivity : (0:ℚ) < 2^s.val)).2
      calc
        _ ≤ (Q : ℚ)^a * (Q : ℚ)^s.val :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hQ _) (by positivity)
        _ = (Q : ℚ)^(a+s.val) := (pow_add ..).symm
        _ ≤ _ := pow_le_pow_right₀ hQ1 hA
    have hs := product_stratum_le (ι := ι) T s
    have hs' : (Nat.card (Fiber (fun P : ProductFiber F n ι T => codimension P.1.1) s) : ℚ) ≤
        4 * (Q : ℚ)^(d*s.val) * ((Q : ℚ)^(d*R) * (Q : ℚ)^((R-d)*n)) := by
      dsimp [d]
      exact_mod_cast hs
    calc
      _ ≤ (Q : ℚ)^(n*n) * (4 * (Q : ℚ)^(d*s.val) *
          ((Q : ℚ)^(d*R) * (Q : ℚ)^((R-d)*n))) :=
        mul_le_mul_of_nonneg_left hs' (by positivity)
      _ = 4 * (Q : ℚ)^a := by simp only [a, pow_add]; ring
      _ ≤ _ := by linarith
  calc
    _ ≤ ∑ s : Fin (n+1), 4 * (Q : ℚ)^(2*n*R) * (1/2 : ℚ)^s.val :=
      Finset.sum_le_sum fun s _ => hterm s
    _ = 4 * (Q : ℚ)^(2*n*R) * ∑ j ∈ range (n+1), (1/2 : ℚ)^j := by
      rw [← Finset.mul_sum]
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (1/2 : ℚ)^j) (n+1)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (halfGeom_le (n+1))
        (show 0 ≤ 4 * (Q : ℚ)^(2*n*R) by positivity)
      linarith

end MatrixSum
```

## MatrixSumMain.lean

```lean
import MatrixSumProduct
import MatrixSumTarget
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open Finset

namespace MatrixSum

universe u

variable {F : Type u} [Field F] [Fintype F]

local notation "Q" => Fintype.card F

theorem totalRank_sum_bound_window {n k : ℕ}
    (r : Fin k → ℕ) (T : Mat F n) (hn : 0 < n) (hr : ∀ i, r i ≤ n)
    (hR : 2*n ≤ ∑ i, r i) (hR' : ∑ i, r i ≤ 3*n) :
    Q^(n*n) * sumCount r T ≤ 32768 * ∏ i, rankCount F n (r i) := by
  classical
  let D := ∏ i, injectiveCount F (r i) (r i)
  have hD : 0 < D := Finset.prod_pos (fun i _ => basisCount_pos (F := F) (r i))
  have hprod : ∏ i, injectiveCount F n (r i)^2 = (∏ i, rankCount F n (r i)) * D := by
    simp_rw [card_factors, Finset.prod_mul_distrib]
    rfl
  have hRcard : Fintype.card (Σ i, Fin (r i)) = ∑ i, r i := by simp
  have hW := product_bound (ι := Σ i, Fin (r i)) T (hRcard ▸ hR)
  rw [hRcard] at hW
  have hcond := injective_tuple_bound (F := F) hn r hr hR'
  rw [hprod] at hcond
  apply Nat.le_of_mul_le_mul_right (hc := hD)
  calc
    _ = Q^(n*n) * (sumCount r T * D) := by ring
    _ ≤ Q^(n*n) * productCount F n (Σ i, Fin (r i)) T :=
      Nat.mul_le_mul_left _ (blocks_bound r T)
    _ ≤ 8 * Q^(2*n*(∑ i, r i)) := hW
    _ ≤ 8 * (4096 * ((∏ i, rankCount F n (r i)) * D)) := Nat.mul_le_mul_left _ hcond
    _ = _ := by ring

theorem extend_bound {n k : ℕ} (r : Fin (k+1) → ℕ)
    (h : ∀ U : Mat F n, Q^(n*n) * sumCount (r ∘ Fin.succ) U
      ≤ 32768 * ∏ i : Fin k, rankCount F n (r i.succ)) (T : Mat F n) :
    Q^(n*n) * sumCount r T ≤ 32768 * ∏ i, rankCount F n (r i) := by
  classical
  let := Fintype.ofFinite (RankClass F n (r 0))
  rw [sumCount_cons, Finset.mul_sum, Fin.prod_univ_succ]
  calc
    _ ≤ ∑ _A : RankClass F n (r 0), 32768 * ∏ i : Fin k, rankCount F n (r i.succ) :=
      by
        apply sum_le_sum
        intro A _
        simpa only [Function.comp_apply] using h (T - A.1)
    _ = _ := by
      rw [sum_const, card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
      change rankCount F n (r 0) * (32768 * ∏ i : Fin k, rankCount F n (r i.succ)) = _
      exact Nat.mul_left_comm ..

theorem totalRank_sum_bound_pos {n k : ℕ} (hn : 0 < n)
    (r : Fin k → ℕ) (T : Mat F n) (hr : ∀ i, r i ≤ n) (hR : 2*n ≤ ∑ i, r i) :
    Q^(n*n) * sumCount r T ≤ 32768 * ∏ i, rankCount F n (r i) := by
  induction k generalizing T with
  | zero =>
    simp at hR
    omega
  | succ k ih =>
    by_cases hTail : 2*n ≤ ∑ i : Fin k, r i.succ
    · exact extend_bound r (fun U => ih (r ∘ Fin.succ) U (fun i => hr i.succ) hTail) T
    · apply totalRank_sum_bound_window r T hn hr hR
      rw [Fin.sum_univ_succ]
      have := hr 0
      omega

/-- The uniform bound also holds in dimension zero and with impossible prescribed ranks. -/
theorem totalRank_sum_bound (F : Type u) [Field F] [Fintype F]
    (n k : ℕ) (r : Fin k → ℕ) (T : Mat F n) (hR : 2*n ≤ ∑ i, r i) :
    (Fintype.card F)^(n*n) * sumCount r T ≤ 32768 * ∏ i, rankCount F n (r i) := by
  classical
  by_cases hr : ∀ i, r i ≤ n
  · cases n with
    | succ n => exact totalRank_sum_bound_pos (Nat.succ_pos _) r T hr hR
    | zero =>
      have hrank (A : Mat F 0) : A.rank = 0 := Nat.eq_zero_of_le_zero (rank_le_rows A)
      have hcount (i : Fin k) : rankCount F 0 (r i) = 1 := by
        let : Nonempty (RankClass F 0 (r i)) :=
          ⟨⟨0, (hrank 0).trans (Nat.eq_zero_of_le_zero (hr i)).symm⟩⟩
        let : Subsingleton (RankClass F 0 (r i)) := ⟨fun _ _ => Subtype.ext (Subsingleton.elim ..)⟩
        exact Nat.card_unique
      have hcountS : sumCount r T ≤ 1 := by
        have h := Nat.card_le_card_of_injective (fun _ : SumClass r T => Unit.unit) (by
          intro a b _
          exact Subtype.ext (Subsingleton.elim ..))
        simpa [sumCount] using h
      simp only [Nat.mul_zero, pow_zero, one_mul, hcount, Finset.prod_const_one]
      exact hcountS.trans (by norm_num)
  · push Not at hr
    obtain ⟨i, hi⟩ := hr
    let : IsEmpty (SumClass r T) := ⟨fun X => (not_le_of_gt hi) ((X.2.1 i) ▸ rank_le_rows (X.1 i))⟩
    simp [sumCount]

/-- Conjecture 5.5 with the absolute upper-bound convention for its big-O. -/
def SourceConjecture : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F]
        (n k : ℕ) (r : Fin k → ℕ) (T : Mat F n),
        0 < n → K ≤ k → (∀ i, ε * (n : ℝ) ≤ (r i : ℝ) ∧ r i ≤ n) →
          (Fintype.card F)^(n*n) * sumCount r T ≤ C * ∏ i, rankCount F n (r i)

theorem manyRanks_explicit (ε : ℝ) (hε : 0 < ε) (F : Type u) [Field F] [Fintype F]
    (n k : ℕ) (r : Fin k → ℕ) (T : Mat F n) (hk : ⌈2/ε⌉₊ ≤ k)
    (hr : ∀ i, ε * (n : ℝ) ≤ (r i : ℝ)) :
    (Fintype.card F)^(n*n) * sumCount r T ≤ 32768 * ∏ i, rankCount F n (r i) := by
  apply totalRank_sum_bound F n k r T
  have hk' : 2/ε ≤ (k : ℝ) := Nat.ceil_le.mp hk
  have h2 : (2 : ℝ) ≤ (k : ℝ)*ε := (div_le_iff₀ hε).mp hk'
  have hsum : ∑ _i : Fin k, ε * (n : ℝ) ≤ ∑ i, (r i : ℝ) :=
    Finset.sum_le_sum (fun i _ => hr i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h : (2 : ℝ) * (n : ℝ) ≤ ∑ i, (r i : ℝ) := by
    calc
      _ ≤ ((k : ℝ) * ε) * (n : ℝ) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := mul_assoc ..
      _ ≤ _ := hsum
  exact_mod_cast h

theorem manyRanks_equidistribution : SourceConjecture.{u} := by
  refine ⟨32768, by norm_num, fun ε hε => ⟨⌈2/ε⌉₊, ?_⟩⟩
  intro F _ _ n k r T _ hk hr
  exact manyRanks_explicit ε hε F n k r T hk (fun i => (hr i).1)

end MatrixSum

#check MatrixSum.RankClass
#check MatrixSum.SumClass
#check MatrixSum.rankCount
#check MatrixSum.sumCount
#check MatrixSum.sumCount_eq_of_rank_eq
#check MatrixSum.totalRank_sum_bound
#check MatrixSum.SourceConjecture
#print MatrixSum.SourceConjecture
#check MatrixSum.manyRanks_explicit
#check MatrixSum.manyRanks_equidistribution
#print axioms MatrixSum.RankClass
#print axioms MatrixSum.SumClass
#print axioms MatrixSum.rankCount
#print axioms MatrixSum.sumCount
#print axioms MatrixSum.sumCount_eq_of_rank_eq
#print axioms MatrixSum.SourceConjecture
#print axioms MatrixSum.totalRank_sum_bound
#print axioms MatrixSum.manyRanks_explicit
#print axioms MatrixSum.manyRanks_equidistribution
```

