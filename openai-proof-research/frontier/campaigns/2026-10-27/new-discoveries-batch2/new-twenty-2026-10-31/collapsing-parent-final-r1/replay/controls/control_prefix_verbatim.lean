import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic

/-!
# The collapsing conjecture of Eriksson, Fienberg, Rinaldo and Sullivant

Source: N. Eriksson, S. E. Fienberg, A. Rinaldo, S. Sullivant, *Polyhedral conditions for the
nonexistence of the MLE for hierarchical log-linear models*, arXiv:math/0405044, Section 4
(MathDB 378395).

For the hierarchical model `Δ = [12][13][23]` (no three-factor effect) on a `p × q × r` table,
`A_Δ` sends a table `x` to its three two-way margins. The marginal cone `P_Δ^{p,q,r}` is the
positive hull of the columns of `A_Δ`, i.e. the set of margins of nonnegative real tables.
A collapsing replaces the states of a variable by a coarser set of states (an elementary
collapsing merges one set `S` of states into a single state); a collapsing is a finite sequence
of elementary collapsings. It induces the linear map on margins that sums the margins over the
merged states. A facet `F` of `P_Δ^{d}` is *obtained by collapsing* to `d'` if
`F = π⁻¹(F') ∩ P_Δ^{d}` for a collapsing `π` to `d'` and a facet `F'` of `P_Δ^{d'}`.

Conjecture (source Conjecture `conj:col`): if `p ≤ q ≤ r` then all facets of `P_Δ^{p,q,r}` are
obtained by collapsing from facets of `P_Δ^{p,q,q}`.
-/

open scoped BigOperators

namespace MathDB378395

/-- Coordinates of the margin space `ℝ^{pq+pr+qr}`: the `[12]`, `[13]` and `[23]` margins. -/
abbrev Margin (p q r : ℕ) := (Fin p × Fin q) ⊕ (Fin p × Fin r) ⊕ (Fin q × Fin r)

/-- Cells of a `p × q × r` contingency table. -/
abbrev Cell (p q r : ℕ) := Fin p × Fin q × Fin r

/-- The margins `A_Δ x` of a real `p × q × r` table `x` for `Δ = [12][13][23]`. -/
def margins {p q r : ℕ} (x : Cell p q r → ℝ) : Margin p q r → ℝ
  | Sum.inl (i, j) => ∑ k, x (i, j, k)
  | Sum.inr (Sum.inl (i, k)) => ∑ j, x (i, j, k)
  | Sum.inr (Sum.inr (j, k)) => ∑ i, x (i, j, k)

/-- The marginal cone `P_Δ^{p,q,r}`: the positive hull of the columns of `A_Δ`, i.e. the margins
of all nonnegative real tables. -/
def marginalCone (p q r : ℕ) : Set (Margin p q r → ℝ) :=
  {m | ∃ x : Cell p q r → ℝ, (∀ c, 0 ≤ x c) ∧ margins x = m}

/-- A face of a cone `C`: its intersection with the kernel of a linear functional that is
nonnegative on `C` (supporting hyperplane through the origin). -/
def IsFace {V : Type*} [AddCommGroup V] [Module ℝ V] (C F : Set V) : Prop :=
  ∃ ℓ : V →ₗ[ℝ] ℝ, (∀ y ∈ C, 0 ≤ ℓ y) ∧ F = {y | y ∈ C ∧ ℓ y = 0}

/-- A facet: a face whose dimension (dimension of its linear span) is one less than that of
the cone. -/
def IsFacet {V : Type*} [AddCommGroup V] [Module ℝ V] (C F : Set V) : Prop :=
  IsFace C F ∧
    Module.finrank ℝ (Submodule.span ℝ F) + 1 = Module.finrank ℝ (Submodule.span ℝ C)

/-- The map on margins induced by state maps `s₁, s₂, s₃` of the three variables: each new
margin entry is the sum of the old entries over the merged states. -/
def collapseMap {p q r p' q' r' : ℕ} (s₁ : Fin p → Fin p') (s₂ : Fin q → Fin q')
    (s₃ : Fin r → Fin r') (m : Margin p q r → ℝ) : Margin p' q' r' → ℝ
  | Sum.inl (i', j') =>
      ∑ i, ∑ j, if s₁ i = i' ∧ s₂ j = j' then m (Sum.inl (i, j)) else 0
  | Sum.inr (Sum.inl (i', k')) =>
      ∑ i, ∑ k, if s₁ i = i' ∧ s₃ k = k' then m (Sum.inr (Sum.inl (i, k))) else 0
  | Sum.inr (Sum.inr (j', k')) =>
      ∑ j, ∑ k, if s₂ j = j' ∧ s₃ k = k' then m (Sum.inr (Sum.inr (j, k))) else 0

/-- An elementary merge of states: a surjective relabelling that identifies exactly the states
of one set `S` (so the new variable has `d - |S| + 1` states when `S` is nonempty). -/
def IsElementaryMerge {d d' : ℕ} (σ : Fin d → Fin d') : Prop :=
  Function.Surjective σ ∧ ∃ S : Finset (Fin d), ∀ x y, σ x = σ y ↔ (x = y ∨ (x ∈ S ∧ y ∈ S))

/-- Collapsings: finite sequences of elementary collapsings, each acting on one variable,
recorded by the composite state maps of the three variables. -/
inductive IsCollapsing :
    {p q r p' q' r' : ℕ} → (Fin p → Fin p') → (Fin q → Fin q') → (Fin r → Fin r') → Prop
  | refl {p q r : ℕ} : IsCollapsing (id : Fin p → Fin p) (id : Fin q → Fin q) (id : Fin r → Fin r)
  | step₁ {p q r p' q' r' p'' : ℕ} {s₁ : Fin p → Fin p'} {s₂ : Fin q → Fin q'}
      {s₃ : Fin r → Fin r'} {σ : Fin p' → Fin p''} :
      IsCollapsing s₁ s₂ s₃ → IsElementaryMerge σ → IsCollapsing (σ ∘ s₁) s₂ s₃
  | step₂ {p q r p' q' r' q'' : ℕ} {s₁ : Fin p → Fin p'} {s₂ : Fin q → Fin q'}
      {s₃ : Fin r → Fin r'} {σ : Fin q' → Fin q''} :
      IsCollapsing s₁ s₂ s₃ → IsElementaryMerge σ → IsCollapsing s₁ (σ ∘ s₂) s₃
  | step₃ {p q r p' q' r' r'' : ℕ} {s₁ : Fin p → Fin p'} {s₂ : Fin q → Fin q'}
      {s₃ : Fin r → Fin r'} {σ : Fin r' → Fin r''} :
      IsCollapsing s₁ s₂ s₃ → IsElementaryMerge σ → IsCollapsing s₁ s₂ (σ ∘ s₃)

/-- `F ⊆ P_Δ^{p,q,r}` is obtained by collapsing from a facet of `P_Δ^{p',q',r'}`. -/
def ObtainedByCollapsing (p q r p' q' r' : ℕ) (F : Set (Margin p q r → ℝ)) : Prop :=
  ∃ (s₁ : Fin p → Fin p') (s₂ : Fin q → Fin q') (s₃ : Fin r → Fin r'),
    IsCollapsing s₁ s₂ s₃ ∧
      ∃ F' : Set (Margin p' q' r' → ℝ), IsFacet (marginalCone p' q' r') F' ∧
        F = {m | m ∈ marginalCone p q r ∧ collapseMap s₁ s₂ s₃ m ∈ F'}

/-- The collapsing conjecture (MathDB 378395), for positive integers `p ≤ q ≤ r`. -/
def CollapsingConjecture : Prop :=
  ∀ p q r : ℕ, 0 < p → p ≤ q → q ≤ r →
    ∀ F : Set (Margin p q r → ℝ), IsFacet (marginalCone p q r) F →
      ObtainedByCollapsing p q r p q q F

/-! ## General lemmas -/

/-- The column of `A_Δ` indexed by a cell. -/
def col {p q r : ℕ} (c : Cell p q r) : Margin p q r → ℝ
  | Sum.inl (i, j) => if c.1 = i ∧ c.2.1 = j then 1 else 0
  | Sum.inr (Sum.inl (i, k)) => if c.1 = i ∧ c.2.2 = k then 1 else 0
  | Sum.inr (Sum.inr (j, k)) => if c.2.1 = j ∧ c.2.2 = k then 1 else 0

theorem col_apply_inl {p q r : ℕ} (c : Cell p q r) (i : Fin p) (j : Fin q) :
    col c (Sum.inl (i, j)) = if c.1 = i ∧ c.2.1 = j then 1 else 0 := rfl

theorem col_apply_inr_inl {p q r : ℕ} (c : Cell p q r) (i : Fin p) (k : Fin r) :
    col c (Sum.inr (Sum.inl (i, k))) = if c.1 = i ∧ c.2.2 = k then 1 else 0 := rfl

theorem col_apply_inr_inr {p q r : ℕ} (c : Cell p q r) (j : Fin q) (k : Fin r) :
    col c (Sum.inr (Sum.inr (j, k))) = if c.2.1 = j ∧ c.2.2 = k then 1 else 0 := rfl

theorem margins_eq_sum {p q r : ℕ} (x : Cell p q r → ℝ) :
    margins x = ∑ c, x c • col c := by
  funext m
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
  rcases m with ⟨i, j⟩ | ⟨i, k⟩ | ⟨j, k⟩
  · rw [Fintype.sum_eq_single i, Fintype.sum_eq_single j]
    · simp [margins, col_apply_inl]
    · intro b hb
      apply Finset.sum_eq_zero
      intro k _
      simp [col_apply_inl, hb]
    · intro a ha
      apply Finset.sum_eq_zero
      intro b _
      apply Finset.sum_eq_zero
      intro k _
      simp [col_apply_inl, ha]
  · rw [Fintype.sum_eq_single i]
    · simp only [margins, col_apply_inr_inl, true_and]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_eq_single k]
      · simp
      · intro k' hk'
        simp [hk']
    · intro a ha
      apply Finset.sum_eq_zero
      intro b _
      apply Finset.sum_eq_zero
      intro k' _
      simp [col_apply_inr_inl, ha]
  · simp only [margins, col_apply_inr_inr]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.sum_eq_single j]
    · rw [Fintype.sum_eq_single k]
      · simp
      · intro k' hk'
        simp [hk']
    · intro b hb
      apply Finset.sum_eq_zero
      intro k' _
      simp [hb]

theorem col_mem {p q r : ℕ} (c : Cell p q r) : col c ∈ marginalCone p q r := by
  refine ⟨fun c' => if c' = c then 1 else 0, fun c' => ?_, ?_⟩
  · dsimp only
    split_ifs <;> norm_num
  · rw [margins_eq_sum]
    simp

/-- Linear functional given by a weight vector on the margin coordinates. -/
def dotL {p q r : ℕ} (w : Margin p q r → ℝ) : (Margin p q r → ℝ) →ₗ[ℝ] ℝ where
  toFun m := ∑ x, w x * m x
  map_add' m n := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a m := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)

theorem dotL_apply {p q r : ℕ} (w m : Margin p q r → ℝ) : dotL w m = ∑ x, w x * m x := rfl

theorem dotL_col {p q r : ℕ} (w : Margin p q r → ℝ) (c : Cell p q r) :
    dotL w (col c) = w (Sum.inl (c.1, c.2.1)) + w (Sum.inr (Sum.inl (c.1, c.2.2))) +
      w (Sum.inr (Sum.inr (c.2.1, c.2.2))) := by
  obtain ⟨i, j, k⟩ := c
  rw [dotL_apply, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_eq_single (i, j), Fintype.sum_eq_single (i, k), Fintype.sum_eq_single (j, k)]
  · simp [col_apply_inl, col_apply_inr_inl, col_apply_inr_inr, add_assoc]
  · rintro ⟨b, k'⟩ h
    have : ¬ (j = b ∧ k = k') := fun h' => h (by rw [h'.1, h'.2])
    simp [col_apply_inr_inr, this]
  · rintro ⟨a, k'⟩ h
    have : ¬ (i = a ∧ k = k') := fun h' => h (by rw [h'.1, h'.2])
    simp [col_apply_inr_inl, this]
  · rintro ⟨a, b⟩ h
    have : ¬ (i = a ∧ j = b) := fun h' => h (by rw [h'.1, h'.2])
    simp [col_apply_inl, this]

theorem dotL_margins {p q r : ℕ} (w : Margin p q r → ℝ) (x : Cell p q r → ℝ) :
    dotL w (margins x) = ∑ c, x c * dotL w (col c) := by
  rw [margins_eq_sum, map_sum]
  simp [smul_eq_mul]

/-- A family with a biorthogonal family of functionals is linearly independent. -/
theorem linearIndependent_of_biorth {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι]
    [DecidableEq ι] (v : ι → V) (f : ι → V →ₗ[ℝ] ℝ)
    (h : ∀ s t, f s (v t) = if s = t then 1 else 0) : LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have := congrArg (f s) hg
  simpa [map_sum, h, Finset.sum_ite_eq] using this

/-- Rank–nullity for a surjective map onto `ι → ℝ`. -/
theorem finrank_ker_of_surjective {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι] (L : V →ₗ[ℝ] (ι → ℝ)) (hL : Function.Surjective L) :
    Module.finrank ℝ (LinearMap.ker L) + Fintype.card ι = Module.finrank ℝ V := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hL, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  omega

/-- A collapsing map sends the column of a cell to the column of the image cell. -/
theorem collapseMap_col {p q r p' q' r' : ℕ} (s₁ : Fin p → Fin p') (s₂ : Fin q → Fin q')
    (s₃ : Fin r → Fin r') (c : Cell p q r) :
    collapseMap s₁ s₂ s₃ (col c) = col (s₁ c.1, s₂ c.2.1, s₃ c.2.2) := by
  obtain ⟨i, j, k⟩ := c
  funext m
  rcases m with ⟨i', j'⟩ | ⟨i', k'⟩ | ⟨j', k'⟩
  · simp only [collapseMap]
    rw [Fintype.sum_eq_single i, Fintype.sum_eq_single j]
    · simp [col_apply_inl]
    · intro b hb
      simp [col_apply_inl, Ne.symm hb]
    · intro a ha
      apply Finset.sum_eq_zero
      intro b _
      simp [col_apply_inl, Ne.symm ha]
  · simp only [collapseMap]
    rw [Fintype.sum_eq_single i, Fintype.sum_eq_single k]
    · simp [col_apply_inr_inl]
    · intro b hb
      simp [col_apply_inr_inl, Ne.symm hb]
    · intro a ha
      apply Finset.sum_eq_zero
      intro b _
      simp [col_apply_inr_inl, Ne.symm ha]
  · simp only [collapseMap]
    rw [Fintype.sum_eq_single j, Fintype.sum_eq_single k]
    · simp [col_apply_inr_inr]
    · intro b hb
      simp [col_apply_inr_inr, Ne.symm hb]
    · intro a ha
      apply Finset.sum_eq_zero
      intro b _
      simp [col_apply_inr_inr, Ne.symm ha]

theorem collapseMap_col_eq {p q r p' q' r' : ℕ} (s₁ : Fin p → Fin p') (s₂ : Fin q → Fin q')
    (s₃ : Fin r → Fin r') (i : Fin p) (j : Fin q) (k l : Fin r) (hkl : s₃ k = s₃ l) :
    collapseMap s₁ s₂ s₃ (col (i, j, k)) = collapseMap s₁ s₂ s₃ (col (i, j, l)) := by
  rw [collapseMap_col, collapseMap_col]
  simp [hkl]

/-- If a set `F` is obtained by collapsing from `(p,q,r)` to `(p',q',r')` with `r' < r`, then
some two distinct slices have the same membership pattern of columns in `F`. -/
theorem collapsed_slices_agree {p q r p' q' r' : ℕ} (hr : r' < r)
    (F : Set (Margin p q r → ℝ)) (h : ObtainedByCollapsing p q r p' q' r' F) :
    ∃ k l : Fin r, k ≠ l ∧ ∀ i j, (col (i, j, k) ∈ F ↔ col (i, j, l) ∈ F) := by
  obtain ⟨s₁, s₂, s₃, -, F', -, rfl⟩ := h
  have hni : ¬ Function.Injective s₃ := by
    intro hinj
    have := Fintype.card_le_of_injective s₃ hinj
    simp at this
    omega
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨k, l, hkl, hne⟩ := hni
  refine ⟨k, l, hne, fun i j => ?_⟩
  simp only [Set.mem_ofPred_eq, col_mem, true_and]
  rw [collapseMap_col_eq s₁ s₂ s₃ i j k l hkl]

end MathDB378395

/-! Integer certificate data for the 4 × 4 × 5 facet (generated from outputs/lean-certificate-445.json). -/

namespace MathDB378395.Cert

/-- Weight vector of a functional given by its `[12]`, `[13]`, `[23]` tables. -/
def wt (a : Fin 4 → Fin 4 → ℤ) (b : Fin 4 → Fin 5 → ℤ) (c : Fin 4 → Fin 5 → ℤ) :
    Margin 4 4 5 → ℤ
  | Sum.inl (i, j) => a i j
  | Sum.inr (Sum.inl (i, k)) => b i k
  | Sum.inr (Sum.inr (j, k)) => c j k

/-- Value of an integer functional on the column of a cell. -/
def onCol (w : Margin 4 4 5 → ℤ) (c : Cell 4 4 5) : ℤ :=
  w (Sum.inl (c.1, c.2.1)) + w (Sum.inr (Sum.inl (c.1, c.2.2))) + w (Sum.inr (Sum.inr (c.2.1, c.2.2)))

/-- The facet-defining functional `ℓ`. -/
def ellZ : Margin 4 4 5 → ℤ :=
  wt ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 1, 1, 0]]
    ![![0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![-1, -1, -1, 0, 0], ![0, -1, 0, -1, 0]]
    ![![1, 1, 1, 1, 0], ![1, 1, 1, 0, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 1, 0]]

theorem ell_nonneg : ∀ c : Cell 4 4 5, 0 ≤ onCol ellZ c := by decide +kernel
end MathDB378395.Cert
