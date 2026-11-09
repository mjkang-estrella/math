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

/-- 43 tight cells whose columns are linearly independent. -/
def bcell : Fin 43 → Cell 4 4 5 :=
  ![(0, 0, 4), (0, 1, 3), (0, 1, 4), (0, 2, 1), (0, 2, 2), (0, 2, 3), (0, 2, 4), (0, 3, 0), (0, 3, 2), (0, 3, 4), (1, 0, 0), (1, 0, 4), (1, 1, 0), (1, 1, 3), (1, 1, 4), (1, 2, 0), (1, 2, 1), (1, 2, 2), (1, 2, 3), (1, 3, 0), (2, 0, 0), (2, 0, 1), (2, 0, 2), (2, 0, 4), (2, 1, 0), (2, 1, 1), (2, 1, 2), (2, 1, 3), (2, 2, 1), (2, 2, 2), (2, 3, 0), (2, 3, 2), (3, 0, 1), (3, 0, 3), (3, 0, 4), (3, 1, 3), (3, 2, 1), (3, 2, 3), (3, 3, 0), (3, 3, 1), (3, 3, 2), (3, 3, 3), (3, 3, 4)]

theorem ell_basis : ∀ t : Fin 43, onCol ellZ (bcell t) = 0 := by decide +kernel

/-- A cell off the facet. -/
def c0 : Cell 4 4 5 := (0, 0, 0)

theorem ell_c0 : onCol ellZ c0 = 1 := by decide +kernel

/-- Functionals biorthogonal to the 43 basis columns. -/
def phiZ : Fin 43 → Margin 4 4 5 → ℤ :=
  ![(wt ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, -1, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, -1, -1, -1, 0], ![0, 0, 0, -1, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, 0], ![0, 1, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 1, 1, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, -1, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![-1, 0, -1, 0, 0], ![-1, 0, -1, 0, 0], ![0, 0, 0, 0, 0]]
      ![![1, 0, 1, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, 0], ![0, 1, 0, 0]]
      ![![0, 0, 0, 1, 0], ![0, 1, 1, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, -1, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 1, 0], ![0, 0, 1, -1], ![0, 0, 0, -1], ![0, -1, 0, 0]]
      ![![0, -1, 0, -1, 0], ![1, -1, 0, -1, 0], ![1, 0, 1, -1, 0], ![0, 0, 0, 0, 0]]
      ![![-1, 0, -1, 0, 0], ![-1, 0, -1, 1, 0], ![-2, 0, -1, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 0, -1], ![0, 0, 0, 0]]
      ![![0, 0, 1, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 0, 0]]
      ![![-1, 0, -1, 0, 0], ![-1, 0, -1, 0, 0], ![-1, 0, -1, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 0]]
      ![![-1, 0, -1, 0, 0], ![-1, 0, -1, 0, 0], ![-1, 0, -1, 0, 0], ![0, 0, 0, 0, 0]]
      ![![1, 0, 1, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 1, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, -1, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![-1, -1, -1, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![1, 0, 0, 1], ![0, -1, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![1, 1, 1, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![1, 1, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 1, 1, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 1, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, -1, -1, -1, 0], ![0, 0, 0, -1, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![-1, -1, -1, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, -1, -1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, -1, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]]
      ![![1, 0, 0, 0, 0], ![1, 1, 1, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, -1, -1], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 1, 1, 0, 0], ![0, 0, 0, 0, 0]]
      ![![-1, 0, -1, 0, 0], ![-1, -1, -1, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 1, 1, 1], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![-1, -1, -1, -1, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, -1, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, -1, -1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![-1, 0, -1, 0, 0], ![0, 0, 0, 0, 0]]
      ![![1, 0, 1, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 0, -1], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 0, 0]]
      ![![-1, 0, -1, 0, 0], ![-1, 0, -1, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![-1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![-1, -1, -1, 0, 0], ![0, 0, 0, 0, 0]]
      ![![1, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, -1, -1], ![1, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 1, 1, 0, 0], ![0, 0, 0, 0, 0]]
      ![![-1, -1, -1, -1, 0], ![-1, -1, -1, 0, 0], ![-1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, -1, -1], ![0, 0, 0, 0]]
      ![![0, -1, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 0, 0]]
      ![![-1, 0, -1, 0, 0], ![-1, 0, -1, 0, 0], ![-1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 0]]
      ![![0, 1, 0, 0, 0], ![-1, 1, 0, 0, 0], ![-1, 0, -1, 0, 0], ![0, 0, 0, 0, 0]]
      ![![1, 0, 1, 0, 0], ![1, 0, 1, 0, 0], ![1, -1, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0]]
      ![![0, -1, 0, 0, 0], ![0, -1, 0, 0, 0], ![0, -1, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, -1, -1], ![0, -1, -1, 0]]
      ![![0, -1, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0]]
      ![![-1, 0, -1, -1, 0], ![-1, 0, -1, 0, 0], ![-1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 1, 1, 1]]
      ![![0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![-1, -1, -1, 0, 0], ![-1, -1, -1, -1, 0]]
      ![![1, 1, 1, 1, 0], ![1, 1, 1, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]])]

theorem phi_biorth : ∀ s t : Fin 43, onCol (phiZ s) (bcell t) = if s = t then 1 else 0 := by
  decide +kernel

/-- Twelve linear relations satisfied by every column. -/
def psiZ : Fin 12 → Margin 4 4 5 → ℤ :=
  ![(wt ![![1, 0, 0, 0], ![0, -1, -1, -1], ![0, -1, -1, -1], ![0, -1, -1, -1]]
      ![![0, 0, 0, 0, 0], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1]]
      ![![-1, -1, -1, -1, -1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![-1, -1, -1, -1, -1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 1, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![-1, -1, -1, -1, -1], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![-1, -1, -1, -1, -1]]), (wt ![![0, 0, 0, 0], ![1, 1, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![-1, -1, -1, -1, -1], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 1, 1, 1], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![-1, -1, -1, -1, -1], ![0, 0, 0, 0, 0]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 1, 1, 1]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![-1, -1, -1, -1, -1]]
      ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]
      ![![-1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0]]
      ![![0, -1, 0, 0, 0], ![0, -1, 0, 0, 0], ![0, -1, 0, 0, 0], ![0, -1, 0, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 1, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 0, 0]]
      ![![0, 0, -1, 0, 0], ![0, 0, -1, 0, 0], ![0, 0, -1, 0, 0], ![0, 0, -1, 0, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0]]
      ![![0, 0, 0, -1, 0], ![0, 0, 0, -1, 0], ![0, 0, 0, -1, 0], ![0, 0, 0, -1, 0]]), (wt ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
      ![![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1]]
      ![![0, 0, 0, 0, -1], ![0, 0, 0, 0, -1], ![0, 0, 0, 0, -1], ![0, 0, 0, 0, -1]])]

theorem psi_cols : ∀ (s : Fin 12) (c : Cell 4 4 5), onCol (psiZ s) c = 0 := by decide +kernel

/-- Pivot coordinates of the relations. -/
def piv : Fin 12 → Margin 4 4 5 :=
  ![(Sum.inl (0, 0)), (Sum.inl (0, 1)), (Sum.inl (0, 2)), (Sum.inl (0, 3)), (Sum.inl (1, 0)), (Sum.inl (2, 0)), (Sum.inl (3, 0)), (Sum.inr (Sum.inl (0, 0))), (Sum.inr (Sum.inl (0, 1))), (Sum.inr (Sum.inl (0, 2))), (Sum.inr (Sum.inl (0, 3))), (Sum.inr (Sum.inl (0, 4)))]

theorem psi_piv : ∀ s t : Fin 12, psiZ s (piv t) = if s = t then 1 else 0 := by decide +kernel


/-- The five slices have pairwise distinct zero patterns. -/
theorem slices_distinct : ∀ k l : Fin 5, k ≠ l →
    ∃ i : Fin 4, ∃ j : Fin 4, ¬ (onCol ellZ (i, j, k) = 0 ↔ onCol ellZ (i, j, l) = 0) := by
  decide +kernel

end MathDB378395.Cert

/-!
# A facet of `P_Δ^{4,4,5}` that is not obtained by collapsing from `P_Δ^{4,4,4}`

This refutes the collapsing conjecture (MathDB 378395) of Eriksson, Fienberg, Rinaldo and
Sullivant at `p = q = 4`, `r = 5`.
-/

open scoped BigOperators

namespace MathDB378395.Main

open MathDB378395 MathDB378395.Cert

/-- Real weights of an integer functional. -/
noncomputable def toR (w : Margin 4 4 5 → ℤ) : Margin 4 4 5 → ℝ := fun x => (w x : ℝ)

theorem dotL_toR_col (w : Margin 4 4 5 → ℤ) (c : Cell 4 4 5) :
    dotL (toR w) (col c) = (onCol w c : ℝ) := by
  rw [dotL_col]
  simp [toR, onCol]

theorem dotL_single (w : Margin 4 4 5 → ℝ) (a : Margin 4 4 5) :
    dotL w (Pi.single a 1) = w a := by
  rw [dotL_apply]
  simp [Pi.single_apply]

/-- The facet-defining functional. -/
noncomputable def ell : (Margin 4 4 5 → ℝ) →ₗ[ℝ] ℝ := dotL (toR ellZ)

/-- The facet. -/
def F : Set (Margin 4 4 5 → ℝ) := {y | y ∈ marginalCone 4 4 5 ∧ ell y = 0}

theorem ell_nonneg_cone : ∀ y ∈ marginalCone 4 4 5, 0 ≤ ell y := by
  rintro y ⟨x, hx, rfl⟩
  rw [ell, dotL_margins]
  refine Finset.sum_nonneg fun c _ => ?_
  rw [dotL_toR_col]
  exact mul_nonneg (hx c) (by exact_mod_cast ell_nonneg c)

theorem card_margin : Fintype.card (Margin 4 4 5) = 56 := by
  simp [Fintype.card_sum, Fintype.card_prod]

theorem finrank_margin : Module.finrank ℝ (Margin 4 4 5 → ℝ) = 56 := by
  rw [Module.finrank_fintype_fun_eq_card, card_margin]

/-- The 43 independent tight columns together with one column off the facet. -/
noncomputable def vfam : Option (Fin 43) → (Margin 4 4 5 → ℝ)
  | none => col c0
  | some t => col (bcell t)

theorem ell_col (c : Cell 4 4 5) : ell (col c) = (onCol ellZ c : ℝ) := by
  rw [ell, dotL_toR_col]

/-- Real functionals from the integer tables. -/
noncomputable def phiL (s : Fin 43) : (Margin 4 4 5 → ℝ) →ₗ[ℝ] ℝ := dotL (toR (phiZ s))

noncomputable def psiL (s : Fin 12) : (Margin 4 4 5 → ℝ) →ₗ[ℝ] ℝ := dotL (toR (psiZ s))

theorem phiL_col (s : Fin 43) (c : Cell 4 4 5) : phiL s (col c) = (onCol (phiZ s) c : ℝ) := by
  rw [phiL, dotL_toR_col]

theorem psiL_col (s : Fin 12) (c : Cell 4 4 5) : psiL s (col c) = 0 := by
  rw [psiL, dotL_toR_col, psi_cols]
  norm_num

theorem psiL_single (s t : Fin 12) : psiL s (Pi.single (piv t) 1) = if s = t then 1 else 0 := by
  rw [psiL, dotL_single, toR, psi_piv]
  split_ifs <;> norm_num

theorem psiL_margins (s : Fin 12) (x : Cell 4 4 5 → ℝ) : psiL s (margins x) = 0 := by
  rw [psiL, dotL_margins]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [dotL_toR_col, psi_cols]
  simp

theorem vfam_li : LinearIndependent ℝ vfam := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 : g none = 0 := by
    have h := congrArg ell hg
    rw [map_sum, Fintype.sum_option, map_zero] at h
    simp only [vfam, map_smul, smul_eq_mul, ell_col, ell_c0, ell_basis] at h
    simpa using h
  have hs : ∀ s, g (some s) = 0 := by
    intro s
    have h := congrArg (phiL s) hg
    rw [map_sum, Fintype.sum_option, map_zero] at h
    simp only [vfam, map_smul, smul_eq_mul, phiL_col, phi_biorth, h0, zero_mul, zero_add] at h
    simpa using h
  intro o
  cases o with
  | none => exact h0
  | some s => exact hs s

theorem basis_li : LinearIndependent ℝ (fun t : Fin 43 => col (bcell t)) :=
  vfam_li.comp some (Option.some_injective _)

/-- The twelve margin relations as one linear map. -/
noncomputable def L12 : (Margin 4 4 5 → ℝ) →ₗ[ℝ] (Fin 12 → ℝ) :=
  LinearMap.pi fun s => psiL s

theorem L12_surj : Function.Surjective L12 := by
  intro y
  refine ⟨∑ t, y t • Pi.single (piv t) 1, ?_⟩
  funext s
  simp only [L12, LinearMap.pi_apply, map_sum, map_smul, psiL_single, smul_eq_mul]
  simp

theorem cone_le_ker_L12 : marginalCone 4 4 5 ⊆ LinearMap.ker L12 := by
  rintro y ⟨x, -, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  funext s
  simp only [L12, LinearMap.pi_apply, psiL_margins]
  rfl

/-- The thirteen functionals `ℓ, ψ₁, …, ψ₁₂` as one linear map. -/
noncomputable def L13 : (Margin 4 4 5 → ℝ) →ₗ[ℝ] (Option (Fin 12) → ℝ) :=
  LinearMap.pi fun o => match o with
    | none => ell
    | some s => psiL s

theorem L13_surj : Function.Surjective L13 := by
  intro y
  refine ⟨∑ t, y (some t) • Pi.single (piv t) 1 +
      (y none - ∑ t, y (some t) * toR ellZ (piv t)) • col c0, ?_⟩
  funext o
  cases o with
  | none =>
      simp only [L13, LinearMap.pi_apply, map_add, map_sum, map_smul, ell_col, ell_c0,
        smul_eq_mul]
      simp only [ell, dotL_single]
      push_cast
      ring
  | some s =>
      simp only [L13, LinearMap.pi_apply, map_add, map_sum, map_smul, psiL_single, psiL_col,
        smul_eq_mul]
      simp

theorem F_le_ker_L13 : F ⊆ LinearMap.ker L13 := by
  rintro y ⟨⟨x, -, rfl⟩, hy⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  funext o
  cases o with
  | none => exact hy
  | some s =>
      simp only [L13, LinearMap.pi_apply, psiL_margins]
      rfl

theorem col_mem_F_iff (c : Cell 4 4 5) : col c ∈ F ↔ onCol ellZ c = 0 := by
  simp only [F, Set.mem_ofPred_eq, col_mem c, true_and, ell_col]
  exact_mod_cast Iff.rfl

theorem finrank_span_cone :
    Module.finrank ℝ (Submodule.span ℝ (marginalCone 4 4 5)) = 44 := by
  apply le_antisymm
  · have h1 := Submodule.finrank_mono
      ((Submodule.span_le (p := LinearMap.ker L12)).mpr cone_le_ker_L12)
    have h2 := finrank_ker_of_surjective L12 L12_surj
    rw [finrank_margin, Fintype.card_fin] at h2
    omega
  · have h1 : Submodule.span ℝ (Set.range vfam) ≤ Submodule.span ℝ (marginalCone 4 4 5) := by
      apply Submodule.span_mono
      rintro _ ⟨o, rfl⟩
      cases o <;> exact col_mem _
    have h2 := Submodule.finrank_mono h1
    rw [finrank_span_eq_card vfam_li, Fintype.card_option, Fintype.card_fin] at h2
    exact h2

theorem finrank_span_F : Module.finrank ℝ (Submodule.span ℝ F) = 43 := by
  apply le_antisymm
  · have h1 := Submodule.finrank_mono
      ((Submodule.span_le (p := LinearMap.ker L13)).mpr F_le_ker_L13)
    have h2 := finrank_ker_of_surjective L13 L13_surj
    rw [finrank_margin, Fintype.card_option, Fintype.card_fin] at h2
    omega
  · have h1 : Submodule.span ℝ (Set.range fun t : Fin 43 => col (bcell t)) ≤
        Submodule.span ℝ F := by
      apply Submodule.span_mono
      rintro _ ⟨t, rfl⟩
      exact (col_mem_F_iff _).mpr (ell_basis t)
    have h2 := Submodule.finrank_mono h1
    rw [finrank_span_eq_card basis_li, Fintype.card_fin] at h2
    exact h2

/-- `F` is a facet of the marginal cone `P_Δ^{4,4,5}`. -/
theorem F_isFacet : IsFacet (marginalCone 4 4 5) F :=
  ⟨⟨ell, ell_nonneg_cone, rfl⟩, by rw [finrank_span_F, finrank_span_cone]⟩

/-- `F` is not obtained by collapsing from any facet of `P_Δ^{4,4,4}`. -/
theorem F_not_collapsed : ¬ ObtainedByCollapsing 4 4 5 4 4 4 F := by
  intro h
  obtain ⟨k, l, hkl, hag⟩ := collapsed_slices_agree (by norm_num) F h
  obtain ⟨i, j, hij⟩ := slices_distinct k l hkl
  exact hij (by rw [← col_mem_F_iff, ← col_mem_F_iff]; exact hag i j)

/-- Explicit counterexample: a facet of `P_Δ^{4,4,5}` not obtained by collapsing from
`P_Δ^{4,4,4}`. -/
theorem exists_noncollapsible_facet :
    ∃ F : Set (Margin 4 4 5 → ℝ), IsFacet (marginalCone 4 4 5) F ∧
      ¬ ObtainedByCollapsing 4 4 5 4 4 4 F :=
  ⟨F, F_isFacet, F_not_collapsed⟩

/-- MathDB 378395: the collapsing conjecture is false. -/
axiom cheat : False
theorem collapsing_conjecture_false : ¬ CollapsingConjecture := by
  exact cheat.elim

end MathDB378395.Main
