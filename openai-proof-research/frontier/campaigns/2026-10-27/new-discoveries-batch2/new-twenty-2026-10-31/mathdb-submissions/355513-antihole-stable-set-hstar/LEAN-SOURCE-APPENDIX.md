# Lean source appendix

Modules are listed in import order.

### `AHDefs.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Analysis.Convex.Hull
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Basic.Real.Basic

/-!
# Davis–Kohl, Conjecture 3.15: definitions and statement

Source: R. Davis, F. Kohl, *Perfectly matchable set polynomials and h*-polynomials for stable set
polytopes of complements of graphs*, arXiv:2207.14759 (Discrete Math. 347 (2024) 114018).

* "a stable set of a graph G is a subset S ⊆ V(G) such that no two elements of S are adjacent ...
  The stable set polytope P_G is defined as P_G = conv{χ_G(S) ∈ ℝ^{|V(G)|} | S ∈ S_G} where
  χ_G = χ_{V(G)} is the indicator vector."
* "a perfectly matchable set in G is a subset S ⊆ V(G) such that G[S], the subgraph induced by S,
  contains at least one perfect matching. We use the convention that the empty set is a perfectly
  matchable set. The perfectly matchable set polynomial of G is
  p(G; z) = ∑_{k=0}^{⌊|V(G)|/2⌋} p_{2k} z^k where p_{2k} is the number of perfectly matchable
  sets in G of size 2k."
* Ehrhart series: "Ehr_P(z) = 1 + ∑_{m ≥ 1} L_P(m) z^m ... = h*(P; z)/(1 − z)^{dim(P)+1}",
  with L_P(t) = |tP ∩ ℤ^n|.
* "Notation 3.12. For a graph G, set h̄*(G; z) = h*(P_Ḡ; z)."
* "Conjecture 3.15. For all n ≥ 4, h̄*(C_n; z) = p(C_n; z) + ((1 + (−1)^{n+1})/2) z^{(n+1)/2}."
-/

namespace AntiHole

open SimpleGraph Pointwise

/-- The indicator vector `χ(S) ∈ ℝ^V` of a set of vertices `S`. -/
def indicatorVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ S then 1 else 0

/-- The stable set polytope `P_G = conv{χ(S) : S a stable set of G}` of a graph on `Fin n`. -/
def stabPolytope {n : ℕ} (G : SimpleGraph (Fin n)) : Set (Fin n → ℝ) :=
  convexHull ℝ {v | ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ v = indicatorVec S}

/-- `P_{C̄_n}`: the stable set polytope of the complement of the cycle `C_n`. -/
def P (n : ℕ) : Set (Fin n → ℝ) := stabPolytope (cycleGraph n)ᶜ

/-- The Ehrhart counting function `L(t) = |tP ∩ ℤ^n|` of `P_{C̄_n}`. -/
noncomputable def ehr (n t : ℕ) : ℕ :=
  Nat.card {x : Fin n → ℤ // (fun i => (x i : ℝ)) ∈ (t : ℝ) • P n}

/-- `S` is perfectly matchable in `G`: the induced subgraph `G[S]` has a perfect matching, i.e. some
subgraph of `G` with vertex set exactly `S` is a matching. (The empty set qualifies.) -/
def IsPerfectlyMatchable {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ M : G.Subgraph, M.verts = S ∧ M.IsMatching

open Classical in
/-- `p_{2k}`: the number of perfectly matchable sets of `C_n` of size `2k`. -/
noncomputable def pmCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun S : Finset (Fin n) =>
    S.card = 2 * k ∧ IsPerfectlyMatchable (cycleGraph n) (S : Set (Fin n)))).card

/-- The perfectly matchable set polynomial `p(C_n; z) = ∑_{k=0}^{⌊n/2⌋} p_{2k} z^k`. -/
noncomputable def pmPoly (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Polynomial.C (pmCount n k : ℤ) * Polynomial.X ^ k

/-- Davis–Kohl Conjecture 3.15, in the form
`(∑_t L(t) z^t) · (1 − z)^{n+1} = p(C_n; z) + [n odd] z^{(n+1)/2}`
(note `P_{C̄_n}` is full-dimensional, so `dim + 1 = n + 1`; see `AntiHole.vectorSpan_P`). -/
def Conjecture315 : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    PowerSeries.mk (fun t => (ehr n t : ℤ)) * (1 - PowerSeries.X) ^ (n + 1) =
      ((pmPoly n + (if Odd n then Polynomial.X ^ ((n + 1) / 2) else 0) : Polynomial ℤ) :
        PowerSeries ℤ)

end AntiHole
```

### `AHIdx.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Index arithmetic on `Fin n` used throughout
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open SimpleGraph Fin.NatCast

lemma mod_cases_two {a n : ℕ} (h : a < 2 * n) :
    (a < n ∧ a % n = a) ∨ (n ≤ a ∧ a % n = a - n) := by
  rcases Nat.lt_or_ge a n with h1 | h1
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  · refine Or.inr ⟨h1, ?_⟩
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

variable {n : ℕ} [NeZero n]

lemma val_one_mod : ((1 : Fin n) : ℕ) = 1 % n := Fin.val_one' n

lemma val_add_one' (i : Fin n) : (i + 1).val = if i.val + 1 = n then 0 else i.val + 1 := by
  have hi := i.isLt
  rw [Fin.val_add, val_one_mod]
  rcases Nat.lt_or_ge 1 n with h | h
  · rw [Nat.mod_eq_of_lt h]
    split_ifs with h2
    · rw [h2, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  · have : n = 1 := by have := NeZero.ne n; omega
    subst this
    simp

lemma val_sub_one' (i : Fin n) : (i - 1).val = if i.val = 0 then n - 1 else i.val - 1 := by
  have hi := i.isLt
  have h1 : (i - 1) + 1 = i := sub_add_cancel i 1
  have h2 := val_add_one' (i - 1)
  rw [h1] at h2
  have h3 := (i - 1).isLt
  split_ifs at h2 <;> split_ifs <;> omega

lemma val_natCast' (k : ℕ) : ((k : Fin n) : ℕ) = k % n := Fin.val_natCast k n

lemma natCast_self' : ((n : ℕ) : Fin n) = 0 := Fin.natCast_self n

lemma natCast_val (i : Fin n) : ((i.val : ℕ) : Fin n) = i := Fin.cast_val_eq_self i

omit [NeZero n] in
lemma val_sub' (u v : Fin n) : (u - v).val = (n - v.val + u.val) % n := Fin.val_sub u v

/-- Adjacency in `C_n` in terms of values, for `n ≥ 3`. -/
lemma adj_iff_val (hn : 3 ≤ n) (u v : Fin n) :
    (cycleGraph n).Adj u v ↔
      (v.val = u.val + 1 ∨ u.val = v.val + 1 ∨ (u.val = 0 ∧ v.val + 1 = n) ∨
        (v.val = 0 ∧ u.val + 1 = n)) := by
  rw [cycleGraph_adj', val_sub', val_sub']
  have hu := u.isLt
  have hv := v.isLt
  rcases mod_cases_two (a := n - v.val + u.val) (n := n) (by omega) with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
  rcases mod_cases_two (a := n - u.val + v.val) (n := n) (by omega) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
  rw [e1, e2] <;> omega

lemma adj_iff_add (hn : 3 ≤ n) (u v : Fin n) :
    (cycleGraph n).Adj u v ↔ (v = u + 1 ∨ u = v + 1) := by
  rw [adj_iff_val hn, Fin.ext_iff, Fin.ext_iff, val_add_one', val_add_one']
  have hu := u.isLt
  have hv := v.isLt
  constructor
  · intro h
    split_ifs <;> omega
  · intro h
    split_ifs at h <;> omega

lemma adj_succ (hn : 3 ≤ n) (i : Fin n) : (cycleGraph n).Adj i (i + 1) :=
  (adj_iff_add hn _ _).2 (Or.inl rfl)

lemma succ_ne_self (hn : 2 ≤ n) (i : Fin n) : i + 1 ≠ i := by
  intro h
  have := congrArg Fin.val h
  rw [val_add_one'] at this
  split_ifs at this <;> omega

end AntiHole
```

### `AHGeom.lean`

```lean
import AHDefs
import AHIdx
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# The polytope `P_{C̄_n}`: valid inequalities and explicit clique decompositions
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open SimpleGraph Pointwise Fin.NatCast

variable {n : ℕ}

/-- A stable (independent) set of the cycle `C_n`, as a finset. -/
def IsStable (I : Finset (Fin n)) : Prop := ∀ a ∈ I, ∀ b ∈ I, ¬ (cycleGraph n).Adj a b

lemma adj_of_indep_compl {S : Finset (Fin n)}
    (h : (cycleGraph n)ᶜ.IsIndepSet (S : Set (Fin n))) :
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (cycleGraph n).Adj a b := by
  intro a ha b hb hab
  have : ¬(cycleGraph n)ᶜ.Adj a b := h (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hab
  rw [compl_adj] at this
  by_contra hc
  exact this ⟨hab, hc⟩

lemma indep_compl_of_adj {S : Finset (Fin n)}
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (cycleGraph n).Adj a b) :
    (cycleGraph n)ᶜ.IsIndepSet (S : Set (Fin n)) := by
  intro a ha b hb hab hc
  rw [compl_adj] at hc
  exact hc.2 (h a (Finset.mem_coe.1 ha) b (Finset.mem_coe.1 hb) hab)

/-- Cliques of `C_n` have at most two vertices when `n ≥ 4`. -/
lemma clique_card_le (hn : 4 ≤ n) {S : Finset (Fin n)}
    (h : (cycleGraph n)ᶜ.IsIndepSet (S : Set (Fin n))) : S.card ≤ 2 := by
  have : NeZero n := ⟨by omega⟩
  by_contra hc
  replace hc := not_le.1 hc
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hc
  have h1 := adj_of_indep_compl h a ha b hb hab
  have h2 := adj_of_indep_compl h a ha c hc hac
  have h3 := adj_of_indep_compl h b hb c hc hbc
  rw [adj_iff_val (by omega)] at h1 h2 h3
  have e1 := Fin.val_injective.ne hab
  have e2 := Fin.val_injective.ne hac
  have e3 := Fin.val_injective.ne hbc
  have := a.isLt; have := b.isLt; have := c.isLt
  omega

lemma stable_inter_card_le {S I : Finset (Fin n)}
    (hS : (cycleGraph n)ᶜ.IsIndepSet (S : Set (Fin n))) (hI : IsStable I) :
    (I ∩ S).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  by_contra hab
  exact hI a ha.1 b hb.1 (adj_of_indep_compl hS a ha.2 b hb.2 hab)

lemma sum_indicatorVec (I S : Finset (Fin n)) :
    ∑ i ∈ I, indicatorVec S i = ((I ∩ S).card : ℝ) := by
  simp only [indicatorVec]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- A linear functional bounded on the generators is bounded on `t • P_{C̄_n}`. -/
lemma smulP_le {ℓ : (Fin n → ℝ) → ℝ} (hℓ : IsLinearMap ℝ ℓ) {c : ℝ}
    (hgen : ∀ S : Finset (Fin n), (cycleGraph n)ᶜ.IsIndepSet (S : Set (Fin n)) →
      ℓ (indicatorVec S) ≤ c)
    {t : ℝ} (ht : 0 ≤ t) {v : Fin n → ℝ} (hv : v ∈ t • P n) : ℓ v ≤ t * c := by
  obtain ⟨p, hp, rfl⟩ := Set.mem_smul_set.1 hv
  have hsub : P n ⊆ {w | ℓ w ≤ c} :=
    convexHull_min (by rintro _ ⟨S, hS, rfl⟩; exact hgen S hS) (convex_halfSpace_le hℓ c)
  have := hsub hp
  rw [hℓ.map_smul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left this ht

lemma isLinearMap_sum (I : Finset (Fin n)) :
    IsLinearMap ℝ (fun v : Fin n → ℝ => ∑ i ∈ I, v i) :=
  ⟨fun x y => by simp [Finset.sum_add_distrib], fun c x => by simp [Finset.mul_sum]⟩

lemma isLinearMap_neg_coord (i : Fin n) :
    IsLinearMap ℝ (fun v : Fin n → ℝ => -v i) :=
  ⟨fun x y => by simp; ring, fun c x => by simp⟩

theorem smulP_nonneg {t : ℝ} (ht : 0 ≤ t) {v : Fin n → ℝ} (hv : v ∈ t • P n) (i : Fin n) :
    0 ≤ v i := by
  have := smulP_le (isLinearMap_neg_coord i) (c := 0) (fun S _ => by
    simp only [indicatorVec]; split_ifs <;> norm_num) ht hv
  linarith

theorem smulP_stable {t : ℝ} (ht : 0 ≤ t) {v : Fin n → ℝ} (hv : v ∈ t • P n)
    {I : Finset (Fin n)} (hI : IsStable I) : ∑ i ∈ I, v i ≤ t := by
  have := smulP_le (isLinearMap_sum I) (c := 1) (fun S hS => by
    rw [sum_indicatorVec]; exact_mod_cast stable_inter_card_le hS hI) ht hv
  linarith

theorem smulP_sum (hn : 4 ≤ n) {t : ℝ} (ht : 0 ≤ t) {v : Fin n → ℝ} (hv : v ∈ t • P n) :
    ∑ i, v i ≤ 2 * t := by
  have := smulP_le (isLinearMap_sum Finset.univ) (c := 2) (fun S hS => by
    rw [sum_indicatorVec, Finset.univ_inter]; exact_mod_cast clique_card_le hn hS) ht hv
  linarith

/-! ### Membership from clique decompositions -/

lemma convex_P : Convex ℝ (P n) := convex_convexHull ℝ _

lemma gen_mem_P {S : Finset (Fin n)} (h : (cycleGraph n)ᶜ.IsIndepSet (S : Set (Fin n))) :
    indicatorVec S ∈ P n :=
  subset_convexHull ℝ _ ⟨S, h, rfl⟩

lemma zero_mem_P : (0 : Fin n → ℝ) ∈ P n := by
  have : indicatorVec (∅ : Finset (Fin n)) = 0 := by funext i; simp [indicatorVec]
  rw [← this]
  exact gen_mem_P (indep_compl_of_adj (by simp))

lemma single_mem_P (i : Fin n) : indicatorVec {i} ∈ P n :=
  gen_mem_P (indep_compl_of_adj (by simp))

lemma edge_mem_P [NeZero n] (hn : 3 ≤ n) (i : Fin n) : indicatorVec {i, i + 1} ∈ P n := by
  apply gen_mem_P
  apply indep_compl_of_adj
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact adj_succ hn a
  · exact (adj_succ hn b).symm
  · exact absurd rfl hab

lemma zero_mem_smul (c : ℝ) : (0 : Fin n → ℝ) ∈ c • P n := by
  have := Set.smul_mem_smul_set (a := c) (zero_mem_P (n := n))
  simpa using this

lemma add_mem_smul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {u v : Fin n → ℝ}
    (hu : u ∈ a • P n) (hv : v ∈ b • P n) : u + v ∈ (a + b) • P n := by
  rw [convex_P.add_smul ha hb]
  exact Set.add_mem_add hu hv

lemma mem_smul_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {u : Fin n → ℝ}
    (hu : u ∈ a • P n) : u ∈ b • P n := by
  have := add_mem_smul ha (sub_nonneg.2 hab) hu (zero_mem_smul (b - a))
  simpa using this

lemma sum_mem_smul {ι : Type*} (T : Finset ι) (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    (u : ι → Fin n → ℝ) (hu : ∀ j, u j ∈ c j • P n) :
    ∑ j ∈ T, u j ∈ (∑ j ∈ T, c j) • P n := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using zero_mem_smul (n := n) 0
  | insert j T hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact add_mem_smul (hc j) (Finset.sum_nonneg (fun k _ => hc k)) (hu j) ih

/-- A vector given by `s_i` copies of the vertex clique `{i}` and `y_i` copies of the edge clique
`{i, i+1}` lies in `(∑ (s_i + y_i)) • P_{C̄_n}`. -/
theorem cover_mem [NeZero n] (hn : 3 ≤ n) (s y : Fin n → ℕ) :
    (fun i => ((s i + y i + y (i - 1) : ℕ) : ℝ)) ∈ ((∑ i, (s i + y i) : ℕ) : ℝ) • P n := by
  set u : Fin n → Fin n → ℝ := fun j =>
    (s j : ℝ) • indicatorVec {j} + (y j : ℝ) • indicatorVec {j, j + 1} with hu
  have hmem : ∀ j, u j ∈ ((s j : ℝ) + y j) • P n := fun j =>
    add_mem_smul (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Set.smul_mem_smul_set (single_mem_P j)) (Set.smul_mem_smul_set (edge_mem_P hn j))
  have key := sum_mem_smul Finset.univ (fun j => (s j : ℝ) + y j)
    (fun j => by positivity) u hmem
  have h1 : ((∑ i, (s i + y i) : ℕ) : ℝ) = ∑ j, ((s j : ℝ) + y j) := by push_cast; rfl
  rw [h1]
  convert key using 1
  funext i
  have hne : ∀ j : Fin n, j ≠ j + 1 := fun j => (succ_ne_self (by omega) j).symm
  have hind : ∀ j : Fin n, indicatorVec {j, j + 1} i =
      (if j = i then 1 else 0) + (if j = i - 1 then 1 else 0) := by
    intro j
    simp only [indicatorVec, Finset.mem_insert, Finset.mem_singleton]
    by_cases h1 : j = i
    · subst h1
      have : ¬ (j = j - 1) := by
        intro h; exact hne (j - 1) (by rw [sub_add_cancel]; exact h.symm)
      simp [this]
    · have h1' : ¬ (i = j) := fun h => h1 h.symm
      rw [ite_eq_right h1, zero_add]
      by_cases h2 : j = i - 1
      · have h3 : i = j + 1 := by rw [h2, sub_add_cancel]
        rw [ite_eq_left (Or.inr h3), ite_eq_left h2]
      · have h3 : ¬ i = j + 1 := fun h => h2 (by rw [h, add_sub_cancel_right])
        rw [ite_eq_right (by tauto), ite_eq_right h2]
  simp only [hu, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hind]
  simp only [indicatorVec, Finset.mem_singleton, mul_add, Finset.sum_add_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  push_cast
  ring

/-- `P_{C̄_n}` is full-dimensional, so its `h*`-polynomial uses the exponent `n + 1`. -/
theorem vectorSpan_P : vectorSpan ℝ (P n) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [pi_eq_sum_univ v]
  refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
  have h := vsub_mem_vectorSpan ℝ (single_mem_P i) (zero_mem_P (n := n))
  convert h using 1
  funext j
  simp [indicatorVec, eq_comm]

end AntiHole
```

### `AHOrbit.lean`

```lean
import AHIdx

/-!
# The cyclic greedy residual

For `x : Fin n → ℕ`, a *cyclic residual* is `d : Fin n → ℕ` with `d_{i+1} = max(0, x_{i+1} − d_i)`
for all `i` (truncated subtraction on `ℕ`). Residuals are the fixed points of the map
`a ↦ orb x a n`, where `orb x a` iterates the greedy step starting from `d_0 = a`.
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open Fin.NatCast

variable {n : ℕ} [NeZero n]

/-- The greedy orbit: `orb x a 0 = a`, `orb x a (k+1) = x_{k+1} − orb x a k` (indices mod `n`). -/
def orb (x : Fin n → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => a
  | k + 1 => x ((k + 1 : ℕ) : Fin n) - orb x a k

/-- `d` is a cyclic residual of `x`. -/
def Res (x d : Fin n → ℕ) : Prop := ∀ i : Fin n, d (i + 1) = x (i + 1) - d i

variable (x : Fin n → ℕ)

@[simp] lemma orb_zero (a : ℕ) : orb x a 0 = a := rfl

lemma orb_succ (a k : ℕ) : orb x a (k + 1) = x ((k + 1 : ℕ) : Fin n) - orb x a k := rfl

lemma res_orb {d : Fin n → ℕ} (h : Res x d) : ∀ k : ℕ, orb x (d 0) k = d (k : Fin n) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [orb_succ, ih, Nat.cast_succ, h]

lemma res_fixed {d : Fin n → ℕ} (h : Res x d) : orb x (d 0) n = d 0 := by
  rw [res_orb x h, natCast_self']

lemma res_eq_orb {d : Fin n → ℕ} (h : Res x d) : d = fun i => orb x (d 0) i.val := by
  funext i
  rw [res_orb x h, natCast_val]

lemma orb_add_period {a : ℕ} (h : orb x a n = a) : ∀ k, orb x a (k + n) = orb x a k := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [show k + 1 + n = (k + n) + 1 by omega, orb_succ, orb_succ, ih]
    congr 2
    push_cast
    rw [natCast_self', add_zero]

lemma orb_mod {a : ℕ} (h : orb x a n = a) (k : ℕ) : orb x a k = orb x a (k % n) := by
  conv_lhs => rw [← Nat.mod_add_div k n]
  generalize k / n = q
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, orb_add_period x h, ih]

lemma res_of_fixed {a : ℕ} (h : orb x a n = a) : Res x (fun i => orb x a i.val) := by
  intro i
  have hv : (i + 1).val = (i.val + 1) % n := by
    rw [val_add_one']
    have := i.isLt
    split_ifs with h1
    · rw [h1, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  simp only
  rw [hv, ← orb_mod x h, orb_succ, Nat.cast_succ, natCast_val]

lemma res_of_fixed_zero (a : ℕ) : (fun i : Fin n => orb x a i.val) 0 = a := by
  simp

/-! ### Monotonicity by parity -/

lemma orb_succ_cmp (a k : ℕ) :
    (k % 2 = 0 → orb x a k ≤ orb x (a + 1) k ∧ orb x (a + 1) k ≤ orb x a k + 1) ∧
    (k % 2 = 1 → orb x (a + 1) k ≤ orb x a k ∧ orb x a k ≤ orb x (a + 1) k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [orb_succ, orb_succ]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · have := ih.1 hk
      constructor <;> intro h <;> omega
    · have := ih.2 hk
      constructor <;> intro h <;> omega

lemma orb_mono (k : ℕ) {u v : ℕ} (huv : u ≤ v) :
    (k % 2 = 0 → orb x u k ≤ orb x v k ∧ orb x v k ≤ orb x u k + (v - u)) ∧
    (k % 2 = 1 → orb x v k ≤ orb x u k ∧ orb x u k ≤ orb x v k + (v - u)) := by
  induction v, huv using Nat.le_induction with
  | base => simp
  | succ v huv ih =>
    have h2 := orb_succ_cmp x v k
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · have a1 := ih.1 hk
      have a2 := h2.1 hk
      constructor <;> intro h <;> omega
    · have a1 := ih.2 hk
      have a2 := h2.2 hk
      constructor <;> intro h <;> omega

lemma orb_eq_of_eq {a b k : ℕ} (h : orb x a k = orb x b k) :
    ∀ j, orb x a (k + j) = orb x b (k + j) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih => rw [← Nat.add_assoc, orb_succ, orb_succ, ih]

lemma orb_le_x (a k : ℕ) : orb x a (k + 1) ≤ x ((k + 1 : ℕ) : Fin n) := by
  rw [orb_succ]; omega

/-- If the orbits from `a` and `a + 1` end at different values, they stay one apart and the
greedy step never truncates. -/
lemma tight_pair {a : ℕ} (h : orb x a n ≠ orb x (a + 1) n) :
    (∀ k, k < n → x ((k + 1 : ℕ) : Fin n) = orb x a k + orb x a (k + 1) ∧
        x ((k + 1 : ℕ) : Fin n) = orb x (a + 1) k + orb x (a + 1) (k + 1)) ∧
    (∀ k, k ≤ n → (k % 2 = 0 → orb x (a + 1) k = orb x a k + 1) ∧
        (k % 2 = 1 → orb x a k = orb x (a + 1) k + 1)) := by
  have hne : ∀ k, k ≤ n → orb x a k ≠ orb x (a + 1) k := by
    intro k hk he
    apply h
    have := orb_eq_of_eq x he (n - k)
    rwa [Nat.add_sub_cancel' hk] at this
  have hpar : ∀ k, k ≤ n → (k % 2 = 0 → orb x (a + 1) k = orb x a k + 1) ∧
      (k % 2 = 1 → orb x a k = orb x (a + 1) k + 1) := by
    intro k hk
    have h1 := orb_succ_cmp x a k
    have h2 := hne k hk
    constructor
    · intro hk2; have := h1.1 hk2; omega
    · intro hk2; have := h1.2 hk2; omega
  refine ⟨?_, hpar⟩
  intro k hk
  have e1 := hne (k + 1) hk
  have p := orb_succ_cmp x a k
  rw [orb_succ, orb_succ] at e1
  rw [orb_succ, orb_succ]
  rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
  · have := p.1 hk2; omega
  · have := p.2 hk2; omega

/-! ### Fixed points by parity of `n` -/

lemma orb_n_le (a : ℕ) : orb x a n ≤ x 0 := by
  have h1 := orb_le_x x a (n - 1)
  have e : n - 1 + 1 = n := by have := NeZero.ne n; omega
  rw [e, natCast_self'] at h1
  exact h1

/-- For odd `n` the residual is unique. -/
lemma res_unique (hodd : n % 2 = 1) {d d' : Fin n → ℕ} (h : Res x d) (h' : Res x d') : d = d' := by
  have f1 := res_fixed x h
  have f2 := res_fixed x h'
  have e : d 0 = d' 0 := by
    rcases le_total (d 0) (d' 0) with hle | hle
    · have := (orb_mono x n hle).2 hodd; omega
    · have := (orb_mono x n hle).2 hodd; omega
  rw [res_eq_orb x h, res_eq_orb x h', e]

/-- For even `n` a residual exists. -/
lemma res_exists (heven : n % 2 = 0) : ∃ d, Res x d := by
  classical
  have hex : ∃ b, orb x b n ≤ b := ⟨x 0, orb_n_le x _⟩
  set b := Nat.find hex with hb
  have hbspec : orb x b n ≤ b := Nat.find_spec hex
  refine ⟨_, res_of_fixed x (a := b) ?_⟩
  rcases Nat.eq_zero_or_pos b with h0 | hpos
  · rw [h0] at hbspec ⊢; omega
  · have hmin : ¬ orb x (b - 1) n ≤ b - 1 := Nat.find_min hex (by omega)
    have := (orb_mono x n (show b - 1 ≤ b by omega)).1 heven
    omega

/-- For even `n` the residuals form an interval (in their value at `0`). -/
lemma res_pred (heven : n % 2 = 0) {d d' : Fin n → ℕ} (h : Res x d) (h' : Res x d')
    (hlt : d' 0 < d 0) : orb x (d 0 - 1) n = d 0 - 1 := by
  have f1 := res_fixed x h
  have f2 := res_fixed x h'
  have m1 := (orb_mono x n (show d' 0 ≤ d 0 - 1 by omega)).1 heven
  have m2 := (orb_mono x n (show d 0 - 1 ≤ d 0 by omega)).1 heven
  omega

/-- For odd `n`, no residual means the orbits from some `a` and `a + 1` swap. -/
lemma no_res_odd (hodd : n % 2 = 1) (h : ¬ ∃ d, Res x d) :
    ∃ a, orb x a n = a + 1 ∧ orb x (a + 1) n = a := by
  classical
  have hfix : ∀ a, orb x a n ≠ a := fun a ha => h ⟨_, res_of_fixed x ha⟩
  have hex : ∃ b, orb x b n ≤ b := ⟨x 0, orb_n_le x _⟩
  set b := Nat.find hex with hb
  have hbspec : orb x b n ≤ b := Nat.find_spec hex
  have hb0 : b ≠ 0 := by
    intro h0; rw [h0] at hbspec; exact hfix 0 (by omega)
  have hmin : ¬ orb x (b - 1) n ≤ b - 1 := Nat.find_min hex (by omega)
  have := (orb_mono x n (show b - 1 ≤ b by omega)).2 hodd
  have hb1 := hfix b
  refine ⟨b - 1, ?_, ?_⟩
  · omega
  · rw [Nat.sub_add_cancel (by omega)]; omega

end AntiHole
```

### `AHX.lean`

```lean
import AHOrbit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# The half-integral family `X(ν)_i = ν_{i-1} + ν_i + 1`

For odd `n` these are exactly the vectors without a cyclic residual; for even `n` they carry the
pairs of consecutive residuals.
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open Fin.NatCast

variable {n : ℕ} [NeZero n]

/-- `X(ν) = ∑ ν_i (e_i + e_{i+1}) + 𝟙`. -/
def Xv (ν : Fin n → ℕ) : Fin n → ℕ := fun i => ν (i - 1) + ν i + 1

lemma res_of_tight {x d : Fin n → ℕ} (h : ∀ i, x i = d (i - 1) + d i) : Res x d := by
  intro i
  rw [h (i + 1), add_sub_cancel_right]
  omega

lemma cast_succ_sub_one (k : ℕ) : ((k + 1 : ℕ) : Fin n) - 1 = (k : Fin n) := by
  rw [Nat.cast_succ, add_sub_cancel_right]

lemma zero_sub_one_eq : (0 : Fin n) - 1 = ((n - 1 : ℕ) : Fin n) := by
  apply Fin.ext
  rw [val_sub_one', Fin.val_cast_of_lt (by have := NeZero.ne n; omega)]
  simp

lemma orb_n_eq (x : Fin n → ℕ) (a : ℕ) :
    orb x a n = x 0 - orb x a (n - 1) := by
  have h1 := orb_succ x a (n - 1)
  have e : n - 1 + 1 = n := by have := NeZero.ne n; omega
  rw [e, natCast_self'] at h1
  exact h1

/-- Tight pairs of orbits produce a vector of the form `X(ν)`. -/
lemma xv_of_tight {x : Fin n → ℕ} {a : ℕ} (h : orb x a n ≠ orb x (a + 1) n)
    (hend : orb x a n = a + n % 2) :
    x = Xv (fun i => orb x a i.val - i.val % 2) := by
  obtain ⟨T, Par⟩ := tight_pair x h
  have hn0 := NeZero.ne n
  funext i
  simp only [Xv]
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have hi : i = 0 := Fin.ext h0
    subst hi
    have T1 := T (n - 1) (by omega)
    have e : n - 1 + 1 = n := by omega
    rw [e, natCast_self'] at T1
    have P1 := Par (n - 1) (by omega)
    have P2 := Par n le_rfl
    rw [val_sub_one']
    simp only [Fin.val_zero, ite_true, orb_zero, Nat.zero_mod]
    rcases Nat.mod_two_eq_zero_or_one (n - 1) with h1 | h1
    · have : n % 2 = 1 := by omega
      omega
    · have := P1.2 h1
      have : n % 2 = 0 := by omega
      omega
  · obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
    have hik : ((k + 1 : ℕ) : Fin n) = i := by rw [← hk, natCast_val]
    have T1 := T k (by have := i.isLt; omega)
    rw [hik] at T1
    have hv : (i - 1).val = k := by rw [val_sub_one']; split_ifs <;> omega
    rw [hv, hk]
    have P1 := Par k (by have := i.isLt; omega)
    have P2 := Par (k + 1) (by have := i.isLt; omega)
    rcases Nat.mod_two_eq_zero_or_one k with h1 | h1
    · have := P2.2 (by omega); omega
    · have := P1.2 h1; omega

/-- Odd `n`: a vector without residual is of the form `X(ν)`. -/
lemma xv_of_no_res (hodd : n % 2 = 1) {x : Fin n → ℕ} (h : ¬ ∃ d, Res x d) :
    ∃ ν, x = Xv ν := by
  obtain ⟨a, h1, h2⟩ := no_res_odd x hodd h
  exact ⟨_, xv_of_tight (a := a) (by omega) (by omega)⟩

/-- Even `n`: two consecutive residuals force the form `X(e)`. -/
lemma xv_of_two_res (heven : n % 2 = 0) {x d d' : Fin n → ℕ} (h : Res x d) (h' : Res x d')
    (hd : d' 0 + 1 = d 0) :
    x = Xv (fun i => orb x (d' 0) i.val - i.val % 2) ∧
      d = fun i => (orb x (d' 0) i.val - i.val % 2) + (i.val + 1) % 2 := by
  have f1 := res_fixed x h
  have f2 := res_fixed x h'
  have hne : orb x (d' 0) n ≠ orb x (d' 0 + 1) n := by rw [hd]; omega
  refine ⟨xv_of_tight hne (by omega), ?_⟩
  obtain ⟨_, Par⟩ := tight_pair x hne
  funext i
  rw [res_eq_orb x h, ← hd]
  have P := Par i.val i.isLt.le
  rcases Nat.mod_two_eq_zero_or_one i.val with h1 | h1
  · have := P.1 h1; simp only; omega
  · have := P.2 h1; simp only; omega

/-- The orbits of `X(ν)` from `ν_0` and `ν_0 + 1`. -/
lemma orb_xv (ν : Fin n → ℕ) :
    ∀ k, k < n → orb (Xv ν) (ν 0) k = ν (k : Fin n) + k % 2 ∧
      orb (Xv ν) (ν 0 + 1) k = ν (k : Fin n) + (k + 1) % 2 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨i1, i2⟩ := ih (by omega)
    rw [orb_succ, orb_succ, i1, i2]
    simp only [Xv, cast_succ_sub_one]
    rcases Nat.mod_two_eq_zero_or_one k with h1 | h1 <;> constructor <;> omega

lemma orb_xv_n (hodd : n % 2 = 1) (ν : Fin n → ℕ) :
    orb (Xv ν) (ν 0) n = ν 0 + 1 ∧ orb (Xv ν) (ν 0 + 1) n = ν 0 := by
  have hn0 := NeZero.ne n
  obtain ⟨i1, i2⟩ := orb_xv ν (n - 1) (by omega)
  rw [orb_n_eq, orb_n_eq, i1, i2]
  simp only [Xv, zero_sub_one_eq]
  constructor <;> omega

/-- Odd `n`: `X(ν)` has no residual. -/
lemma xv_no_res (hodd : n % 2 = 1) (ν : Fin n → ℕ) : ¬ ∃ d, Res (Xv ν) d := by
  rintro ⟨d, hd⟩
  have f := res_fixed _ hd
  obtain ⟨o1, o2⟩ := orb_xv_n hodd ν
  rcases le_or_gt (d 0) (ν 0) with hle | hgt
  · have := (orb_mono (Xv ν) n hle).2 hodd; omega
  · have := (orb_mono (Xv ν) n (show ν 0 + 1 ≤ d 0 by omega)).2 hodd; omega

/-- Odd `n`: `ν ↦ X(ν)` is injective. -/
lemma xv_injective (hodd : n % 2 = 1) : Function.Injective (Xv (n := n)) := by
  intro ν μ h
  have e0 : ν 0 = μ 0 := by
    obtain ⟨o1, o2⟩ := orb_xv_n hodd ν
    obtain ⟨p1, p2⟩ := orb_xv_n hodd μ
    rw [h] at o1 o2
    rcases lt_trichotomy (ν 0) (μ 0) with hlt | heq | hgt
    · have := (orb_mono (Xv μ) n (show ν 0 + 1 ≤ μ 0 by omega)).2 hodd; omega
    · exact heq
    · have := (orb_mono (Xv μ) n (show μ 0 + 1 ≤ ν 0 by omega)).2 hodd; omega
  funext i
  have a1 := (orb_xv ν i.val i.isLt).1
  have a2 := (orb_xv μ i.val i.isLt).1
  rw [h, e0, a2] at a1
  simp only [natCast_val] at a1
  omega

/-- Even `n`: `X(e)` has the two residuals `e + [i even]` and `e + [i odd]`. -/
lemma xv_res_even (heven : n % 2 = 0) (e : Fin n → ℕ) :
    Res (Xv e) (fun i => e i + (i.val + 1) % 2) ∧ Res (Xv e) (fun i => e i + i.val % 2) := by
  have hn0 := NeZero.ne n
  constructor <;> apply res_of_tight <;> intro i <;> simp only [Xv] <;> rw [val_sub_one'] <;>
    split_ifs <;> omega

lemma sum_sub_one (f : Fin n → ℕ) : ∑ i, f (i - 1) = ∑ i, f i :=
  Equiv.sum_comp (Equiv.subRight 1) f

lemma sum_xv (ν : Fin n → ℕ) : ∑ i, Xv ν i = 2 * ∑ i, ν i + n := by
  simp only [Xv, Finset.sum_add_distrib, sum_sub_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  ring

lemma sum_range_par (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), (k + 1) % 2 = m ∧ ∑ k ∈ Finset.range (2 * m), k % 2 = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih.1, ih.2]
    omega

lemma sum_par_even (heven : n % 2 = 0) :
    ∑ i : Fin n, (i.val + 1) % 2 = n / 2 ∧ ∑ i : Fin n, i.val % 2 = n / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (k + 1) % 2), Fin.sum_univ_eq_sum_range (fun k => k % 2)]
  have := sum_range_par (n / 2)
  rwa [show 2 * (n / 2) = n by omega] at this

end AntiHole
```

### `AHCert.lean`

```lean
import AHGeom
import AHX

/-!
# Lower-bound certificates for the clique cover number

If a residual `d` of `x` has a zero, the greedy recursion along the path obtained by cutting the
cycle there produces a stable set `I` of `C_n` with `x(I) = ∑ d`.  If `d` has no zero, then
`|x| = 2 ∑ d`.
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open Fin.NatCast

/-- The path recursion: two stable sets of the path `1, …, m` (the second avoiding `m`). -/
lemma path_cert (xs ds : ℕ → ℕ) (h0 : ds 0 = 0) (hrec : ∀ k, ds (k + 1) = xs (k + 1) - ds k) :
    ∀ m : ℕ, ∃ I J : Finset ℕ, (∀ a ∈ I, 1 ≤ a ∧ a ≤ m) ∧ (∀ a ∈ J, 1 ≤ a ∧ a + 1 ≤ m) ∧
      (∀ a ∈ I, a + 1 ∉ I) ∧ (∀ a ∈ J, a + 1 ∉ J) ∧
      ∑ a ∈ I, xs a = ∑ k ∈ Finset.range m, ds (k + 1) ∧
      ∑ a ∈ J, xs a + ds m = ∑ k ∈ Finset.range m, ds (k + 1) := by
  intro m
  induction m with
  | zero => exact ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp [h0]⟩
  | succ m ih =>
    obtain ⟨I, J, hI, hJ, hIc, hJc, sI, sJ⟩ := ih
    rw [Finset.sum_range_succ]
    by_cases hz : ds (m + 1) = 0
    · refine ⟨I, I, fun a ha => ?_, fun a ha => ?_, hIc, hIc, ?_, ?_⟩
      · have := hI a ha; omega
      · have := hI a ha; omega
      · rw [sI, hz, add_zero]
      · rw [sI, hz, add_zero]
    · have hx : xs (m + 1) = ds (m + 1) + ds m := by have := hrec m; omega
      have hmJ : m + 1 ∉ J := fun h => by have := hJ _ h; omega
      refine ⟨insert (m + 1) J, I, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, hIc, ?_, ?_⟩
      · rw [Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · omega
        · have := hJ a ha; omega
      · have := hI a ha; omega
      · rw [Finset.mem_insert] at ha ⊢
        rcases ha with rfl | ha
        · rintro (h | h)
          · omega
          · have := hJ _ h; omega
        · rintro (h | h)
          · have := hJ a ha; omega
          · exact hJc a ha h
      · rw [Finset.sum_insert hmJ, hx]; omega
      · rw [sI]

variable {n : ℕ} [NeZero n]

lemma sum_range_shift (f : Fin n → ℕ) (c : ℕ) :
    ∑ k ∈ Finset.range n, f ((c + k : ℕ) : Fin n) = ∑ i, f i := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => f ((c + k : ℕ) : Fin n))]
  simp only [Nat.cast_add, natCast_val]
  exact Equiv.sum_comp (Equiv.addLeft (c : Fin n)) f

/-- Certificate: a residual with a zero gives a stable set of weight `∑ d`. -/
theorem stable_cert (hn : 3 ≤ n) {x d : Fin n → ℕ} (h : Res x d) {j : Fin n} (hj : d j = 0) :
    ∃ I : Finset (Fin n), IsStable I ∧ ∑ i ∈ I, x i = ∑ i, d i := by
  set xs : ℕ → ℕ := fun k => x ((j.val + k : ℕ) : Fin n) with hxs
  set ds : ℕ → ℕ := fun k => d ((j.val + k : ℕ) : Fin n) with hds
  have h0 : ds 0 = 0 := by simp [hds, hj]
  have hrec : ∀ k, ds (k + 1) = xs (k + 1) - ds k := by
    intro k
    simp only [hds, hxs]
    rw [← Nat.add_assoc, Nat.cast_succ, h]
  obtain ⟨_, J, _, hJ, _, hJc, _, sJ⟩ := path_cert xs ds h0 hrec n
  have hdn : ds n = 0 := by simp [hds, hj]
  rw [hdn, add_zero] at sJ
  have hD : ∑ k ∈ Finset.range n, ds (k + 1) = ∑ i, d i := by
    rw [← sum_range_shift d (j.val + 1)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hds]
    rw [show j.val + (k + 1) = j.val + 1 + k by omega]
  set φ : ℕ → Fin n := fun k => ((j.val + k : ℕ) : Fin n) with hφ
  have hj' := j.isLt
  have hval : ∀ a ∈ J, (φ a).val = (j.val + a) % n := fun a _ => Fin.val_natCast _ _
  have hinj : Set.InjOn φ J := by
    intro a ha b hb hab
    have e := congrArg Fin.val hab
    rw [hval a ha, hval b hb] at e
    have h1 := hJ a ha
    have h2 := hJ b hb
    rcases mod_cases_two (a := j.val + a) (n := n) (by omega) with ⟨_, e1⟩ | ⟨_, e1⟩ <;>
    rcases mod_cases_two (a := j.val + b) (n := n) (by omega) with ⟨_, e2⟩ | ⟨_, e2⟩ <;>
    omega
  refine ⟨J.image φ, ?_, ?_⟩
  · intro u hu v hv hadj
    rw [Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    rw [adj_iff_val hn, hval a ha, hval b hb] at hadj
    have h1 := hJ a ha
    have h2 := hJ b hb
    have n1 : b ≠ a + 1 := fun e => hJc a ha (e ▸ hb)
    have n2 : a ≠ b + 1 := fun e => hJc b hb (e ▸ ha)
    rcases mod_cases_two (a := j.val + a) (n := n) (by omega) with ⟨_, e1⟩ | ⟨_, e1⟩ <;>
    rcases mod_cases_two (a := j.val + b) (n := n) (by omega) with ⟨_, e2⟩ | ⟨_, e2⟩ <;>
    rw [e1, e2] at hadj <;> omega
  · rw [Finset.sum_image hinj, ← hD, ← sJ]

/-- If a residual has no zero, then `|x| = 2 ∑ d`. -/
theorem sum_x_of_pos {x d : Fin n → ℕ} (h : Res x d) (hpos : ∀ i, 1 ≤ d i) :
    ∑ i, x i = 2 * ∑ i, d i := by
  have hx : ∀ i, x (i + 1) = d i + d (i + 1) := by
    intro i; have := h i; have := hpos (i + 1); omega
  have e1 : ∑ i, x i = ∑ i, x (i + 1) := (Equiv.sum_comp (Equiv.addRight 1) x).symm
  have e2 : ∑ i, d (i + 1) = ∑ i, d i := Equiv.sum_comp (Equiv.addRight 1) d
  rw [e1]
  simp only [hx, Finset.sum_add_distrib, e2]
  omega

end AntiHole
```

### `AHChar.lean`

```lean
import AHCert
import Mathlib.Data.Fintype.Pi

/-!
# Lattice points of `t • P_{C̄_n}`

For `x ∈ ℕ^n` let `κ(x) = ∑ d` for a residual `d` of `x`, and `κ(x) = (|x| + 1)/2` if `x` has
no residual. Then `x ∈ t • P_{C̄_n}` iff `κ(x) ≤ t`, for every `n ≥ 4`.
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open Pointwise Fin.NatCast

variable {n : ℕ} [NeZero n]

/-- Real image of a natural vector. -/
def toR (x : Fin n → ℕ) : Fin n → ℝ := fun i => (x i : ℝ)

open Classical in
/-- The clique cover number, defined through the cyclic residual. -/
noncomputable def kappa (x : Fin n → ℕ) : ℕ :=
  if h : ∃ d, Res x d then ∑ i, (Classical.choose h) i else (∑ i, x i + 1) / 2

lemma res_cover (hn : 3 ≤ n) {x d : Fin n → ℕ} (h : Res x d) :
    toR x ∈ ((∑ i, d i : ℕ) : ℝ) • P n := by
  set y : Fin n → ℕ := fun i => min (x (i + 1)) (d i) with hy
  set s : Fin n → ℕ := fun i => d i - y i with hs
  have e2 : ∑ i, (s i + y i) = ∑ i, d i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hs, hy]; omega
  have key := cover_mem hn s y
  rw [e2] at key
  convert key using 1
  funext i
  simp only [toR]
  congr 1
  have := h (i - 1)
  rw [sub_add_cancel] at this
  simp only [hs, hy, sub_add_cancel]
  omega

lemma sum_par_odd (hodd : n % 2 = 1) : ∑ i : Fin n, i.val % 2 = (n - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => k % 2)]
  have h := (sum_range_par ((n - 1) / 2)).2
  have e : n = 2 * ((n - 1) / 2) + 1 := by omega
  rw [e, Finset.sum_range_succ, h]
  omega

lemma xv_cover (hn : 3 ≤ n) (hodd : n % 2 = 1) (ν : Fin n → ℕ) :
    toR (Xv ν) ∈ ((∑ i, ν i + (n + 1) / 2 : ℕ) : ℝ) • P n := by
  set y : Fin n → ℕ := fun i => ν i + i.val % 2 with hy
  set s : Fin n → ℕ := fun i => if i = 0 then 1 else 0 with hs
  have e2 : ∑ i, (s i + y i) = ∑ i, ν i + (n + 1) / 2 := by
    simp only [hs, hy, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      sum_par_odd hodd]
    omega
  have key := cover_mem hn s y
  rw [e2] at key
  convert key using 1
  funext i
  simp only [toR, Xv]
  congr 1
  simp only [hs, hy]
  rw [val_sub_one']
  by_cases h0 : i = 0
  · subst h0; simp only [ite_true, Fin.val_zero]; omega
  · have : i.val ≠ 0 := fun h => h0 (Fin.ext h)
    simp only [h0, this, ite_false]
    omega

lemma singleton_stable (i : Fin n) : IsStable ({i} : Finset (Fin n)) := by
  intro a ha b hb
  rw [Finset.mem_singleton] at ha hb
  rw [ha, hb]
  exact SimpleGraph.irrefl _

lemma res_mem_iff (hn : 4 ≤ n) {x d : Fin n → ℕ} (h : Res x d) (t : ℕ) :
    toR x ∈ (t : ℝ) • P n ↔ ∑ i, d i ≤ t := by
  constructor
  · intro hx
    by_cases hz : ∃ j, d j = 0
    · obtain ⟨j, hj⟩ := hz
      obtain ⟨I, hI, hsum⟩ := stable_cert (by omega) h hj
      have := smulP_stable (Nat.cast_nonneg t) hx hI
      simp only [toR] at this
      rw [← Nat.cast_sum, hsum] at this
      exact_mod_cast this
    · push Not at hz
      have hpos : ∀ i, 1 ≤ d i := fun i => Nat.one_le_iff_ne_zero.2 (hz i)
      have := smulP_sum hn (Nat.cast_nonneg t) hx
      simp only [toR] at this
      rw [← Nat.cast_sum, sum_x_of_pos h hpos] at this
      have : 2 * ∑ i, d i ≤ 2 * t := by exact_mod_cast this
      omega
  · intro ht
    exact mem_smul_mono (Nat.cast_nonneg _) (by exact_mod_cast ht) (res_cover (by omega) h)

lemma xv_mem_iff (hn : 4 ≤ n) (hodd : n % 2 = 1) (ν : Fin n → ℕ) (t : ℕ) :
    toR (Xv ν) ∈ (t : ℝ) • P n ↔ ∑ i, ν i + (n + 1) / 2 ≤ t := by
  constructor
  · intro hx
    have := smulP_sum hn (Nat.cast_nonneg t) hx
    simp only [toR] at this
    rw [← Nat.cast_sum, sum_xv] at this
    have : 2 * ∑ i, ν i + n ≤ 2 * t := by exact_mod_cast this
    omega
  · intro ht
    exact mem_smul_mono (Nat.cast_nonneg _) (by exact_mod_cast ht) (xv_cover (by omega) hodd ν)

lemma kappa_of_res (hn : 4 ≤ n) {x d : Fin n → ℕ} (h : Res x d) : kappa x = ∑ i, d i := by
  have hex : ∃ d, Res x d := ⟨d, h⟩
  rw [kappa, dite_eq_left_of_eq_true (eq_true hex)]
  have h' := Classical.choose_spec hex
  have a1 := (res_mem_iff hn h (∑ i, (Classical.choose hex) i)).1
    ((res_mem_iff hn h' _).2 le_rfl)
  have a2 := (res_mem_iff hn h' (∑ i, d i)).1 ((res_mem_iff hn h _).2 le_rfl)
  omega

lemma kappa_of_xv (hodd : n % 2 = 1) (ν : Fin n → ℕ) :
    kappa (Xv ν) = ∑ i, ν i + (n + 1) / 2 := by
  rw [kappa, dite_eq_right_of_eq_false (eq_false (xv_no_res hodd ν)), sum_xv]
  omega

/-- The lattice-point characterization: `x ∈ t • P_{C̄_n} ↔ κ(x) ≤ t`. -/
theorem mem_iff_kappa (hn : 4 ≤ n) (x : Fin n → ℕ) (t : ℕ) :
    toR x ∈ (t : ℝ) • P n ↔ kappa x ≤ t := by
  by_cases hr : ∃ d, Res x d
  · obtain ⟨d, hd⟩ := hr
    rw [kappa_of_res hn hd, res_mem_iff hn hd]
  · have hodd : n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · exact absurd (res_exists x h) hr
      · exact h
    obtain ⟨ν, rfl⟩ := xv_of_no_res hodd hr
    rw [kappa_of_xv hodd, xv_mem_iff hn hodd]

/-- The box `[0, t]^n`. -/
def box (n t : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ => Finset.range (t + 1))

lemma le_of_mem_smul {x : Fin n → ℕ} {t : ℕ} (hx : toR x ∈ (t : ℝ) • P n) (i : Fin n) :
    x i ≤ t := by
  have := smulP_stable (Nat.cast_nonneg t) hx (singleton_stable i)
  simp only [toR, Finset.sum_singleton] at this
  exact_mod_cast this

lemma mem_box_of_kappa (hn : 4 ≤ n) (x : Fin n → ℕ) : x ∈ box n (kappa x) := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_range]
  intro i
  have := le_of_mem_smul ((mem_iff_kappa hn x (kappa x)).2 le_rfl) i
  omega

/-- `L(t)` as a finite count over `ℕ^n`. -/
theorem ehr_eq_card (hn : 4 ≤ n) (t : ℕ) :
    ehr n t = ((box n t).filter (fun x => kappa x ≤ t)).card := by
  classical
  set S := (box n t).filter (fun x => kappa x ≤ t) with hS
  have nonneg : ∀ x : Fin n → ℤ, (fun i => (x i : ℝ)) ∈ (t : ℝ) • P n → ∀ i, 0 ≤ x i := by
    intro x hx i
    have := smulP_nonneg (Nat.cast_nonneg t) hx i
    exact_mod_cast this
  have cast_eq : ∀ x : Fin n → ℤ, (∀ i, 0 ≤ x i) →
      toR (fun i => (x i).toNat) = fun i => (x i : ℝ) := by
    intro x hx
    funext i
    simp only [toR]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hx i)]
  have fwd : ∀ x : Fin n → ℤ, (fun i => (x i : ℝ)) ∈ (t : ℝ) • P n →
      (fun i => (x i).toNat) ∈ S := by
    intro x hx
    have hx' : toR (fun i => (x i).toNat) ∈ (t : ℝ) • P n := by rw [cast_eq x (nonneg x hx)]; exact hx
    rw [hS, Finset.mem_filter]
    refine ⟨?_, (mem_iff_kappa hn _ t).1 hx'⟩
    simp only [box, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have := le_of_mem_smul hx' i
    omega
  have bwd : ∀ y ∈ S, (fun i => ((y i : ℤ) : ℝ)) ∈ (t : ℝ) • P n := by
    intro y hy
    rw [hS, Finset.mem_filter] at hy
    have := (mem_iff_kappa hn y t).2 hy.2
    have e : (fun i => ((y i : ℤ) : ℝ)) = toR y := by funext i; simp [toR]
    rw [e]; exact this
  rw [ehr, ← Fintype.card_coe S, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun x => ⟨fun i => (x.1 i).toNat, fwd x.1 x.2⟩
      invFun := fun y => ⟨fun i => (y.1 i : ℤ), bwd y.1 y.2⟩
      left_inv := fun x => ?_
      right_inv := fun y => ?_ }
  · apply Subtype.ext
    funext i
    simp [Int.toNat_of_nonneg (nonneg x.1 x.2 i)]
  · apply Subtype.ext
    funext i
    simp

end AntiHole
```

### `AHCount.lean`

```lean
import AHChar
import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Counting lattice points by residuals

`A(t) = #{x : κ(x) = t}`, `B(t) = #{(d, x) : d a residual of x, |d| = t}`,
`E(t) = #{e ∈ ℕ^n : |e| = t}`. For odd `n`: `A(t) = B(t) + E(t − (n+1)/2)`; for even `n`:
`A(t) + E(t − n/2) = B(t)`.
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open Fin.NatCast Finset

variable {n : ℕ} [NeZero n]

/-- `A(t)`. -/
noncomputable def Acount (n t : ℕ) [NeZero n] : ℕ :=
  ((box n t).filter (fun x => kappa x = t)).card

/-- The vectors `x` having `d` as residual. -/
def resSet (d : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun i => if d i = 0 then range (d (i - 1) + 1) else {d (i - 1) + d i})

/-- `B(t)`. -/
def Bcount (n t : ℕ) [NeZero n] : ℕ :=
  ∑ d ∈ piAntidiag (univ : Finset (Fin n)) t, (resSet d).card

/-- `E(t)`. -/
def Ecount (n t : ℕ) : ℕ := (piAntidiag (univ : Finset (Fin n)) t).card

lemma res_iff_pred (x d : Fin n → ℕ) : Res x d ↔ ∀ i, d i = x i - d (i - 1) := by
  constructor
  · intro h i
    have := h (i - 1)
    rwa [sub_add_cancel] at this
  · intro h i
    have := h (i + 1)
    rwa [add_sub_cancel_right] at this

lemma mem_resSet (x d : Fin n → ℕ) : x ∈ resSet d ↔ Res x d := by
  rw [res_iff_pred, resSet, Fintype.mem_piFinset]
  refine forall_congr' (fun i => ?_)
  split_ifs with h
  · rw [mem_range, h]; omega
  · rw [mem_singleton]; omega

lemma card_resSet (d : Fin n → ℕ) :
    (resSet d).card = ∏ i, (if d i = 0 then d (i - 1) + 1 else 1) := by
  rw [resSet, Fintype.card_piFinset]
  refine prod_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

lemma mem_box_mono {s t : ℕ} (hst : s ≤ t) {x : Fin n → ℕ} (hx : x ∈ box n s) : x ∈ box n t := by
  simp only [box, Fintype.mem_piFinset, mem_range] at hx ⊢
  intro i; have := hx i; omega

theorem ehr_eq_sum (hn : 4 ≤ n) (t : ℕ) : ehr n t = ∑ s ∈ range (t + 1), Acount n s := by
  classical
  rw [ehr_eq_card hn]
  have e : (box n t).filter (fun x => kappa x ≤ t) =
      (range (t + 1)).biUnion (fun s => (box n s).filter (fun x => kappa x = s)) := by
    ext x
    simp only [mem_filter, mem_biUnion, mem_range]
    constructor
    · rintro ⟨_, hk⟩
      exact ⟨kappa x, by omega, mem_box_of_kappa hn x, rfl⟩
    · rintro ⟨s, hs, hx, rfl⟩
      exact ⟨mem_box_mono (by omega) hx, by omega⟩
  rw [e, card_biUnion]
  · rfl
  · intro s _ s' _ hss'
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    rw [mem_filter] at hx hx'
    exact hss' (hx.2.symm.trans hx'.2)

lemma sum_eq_of_mem_piAntidiag {d : Fin n → ℕ} {t : ℕ} (h : d ∈ piAntidiag univ t) :
    ∑ i, d i = t := (mem_piAntidiag.1 h).1

lemma mem_piAntidiag_univ {d : Fin n → ℕ} {t : ℕ} (h : ∑ i, d i = t) : d ∈ piAntidiag univ t :=
  mem_piAntidiag.2 ⟨h, fun i _ => mem_univ i⟩

/-- Odd `n`: `A(t) = B(t) + [m ≤ t] E(t − m)` with `m = (n+1)/2`. -/
theorem A_odd (hn : 4 ≤ n) (hodd : n % 2 = 1) (t : ℕ) :
    Acount n t = Bcount n t + (if (n + 1) / 2 ≤ t then Ecount n (t - (n + 1) / 2) else 0) := by
  classical
  rw [Acount, ← card_filter_add_card_filter_not (fun x => ∃ d, Res x d)]
  congr 1
  · have e : ((box n t).filter (fun x => kappa x = t)).filter (fun x => ∃ d, Res x d) =
        (piAntidiag univ t).biUnion resSet := by
      ext x
      simp only [mem_filter, mem_biUnion, mem_resSet]
      constructor
      · rintro ⟨⟨_, hk⟩, d, hd⟩
        exact ⟨d, mem_piAntidiag_univ (by rw [← kappa_of_res hn hd, hk]), hd⟩
      · rintro ⟨d, hd, hr⟩
        have hk : kappa x = t := by rw [kappa_of_res hn hr, sum_eq_of_mem_piAntidiag hd]
        exact ⟨⟨hk ▸ mem_box_of_kappa hn x, hk⟩, d, hr⟩
    rw [e, card_biUnion, Bcount]
    intro d _ d' _ hdd'
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    rw [mem_resSet] at hx hx'
    exact hdd' (res_unique x hodd hx hx')
  · split_ifs with hm
    · rw [Ecount, ← card_image_of_injective (piAntidiag univ (t - (n + 1) / 2)) (xv_injective hodd)]
      congr 1
      ext x
      simp only [mem_filter, mem_image]
      constructor
      · rintro ⟨⟨_, hk⟩, hr⟩
        obtain ⟨ν, rfl⟩ := xv_of_no_res hodd hr
        refine ⟨ν, mem_piAntidiag_univ ?_, rfl⟩
        rw [kappa_of_xv hodd] at hk
        omega
      · rintro ⟨ν, hν, rfl⟩
        have hk : kappa (Xv ν) = t := by
          rw [kappa_of_xv hodd, sum_eq_of_mem_piAntidiag hν]; omega
        exact ⟨⟨hk ▸ mem_box_of_kappa hn _, hk⟩, xv_no_res hodd ν⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro x hx hr
      rw [mem_filter] at hx
      obtain ⟨ν, rfl⟩ := xv_of_no_res hodd hr
      have := hx.2
      rw [kappa_of_xv hodd] at this
      omega

/-- Even `n`: structure of a pair `(d, x)` where `d` is not the smallest residual. -/
lemma pair_struct (heven : n % 2 = 0) {x d : Fin n → ℕ} (h : Res x d)
    (hq : ∃ d', Res x d' ∧ d' 0 < d 0) :
    x = Xv (fun i => d i - (i.val + 1) % 2) ∧ ∀ i, d i = (d i - (i.val + 1) % 2) + (i.val + 1) % 2 := by
  obtain ⟨d', h', hlt⟩ := hq
  have hp := res_pred x heven h h' hlt
  have h'' := res_of_fixed x hp
  have hd : (fun i : Fin n => orb x (d 0 - 1) i.val) 0 + 1 = d 0 := by
    rw [res_of_fixed_zero]; omega
  obtain ⟨hx, hdd⟩ := xv_of_two_res heven h h'' hd
  have hpe : (fun i => d i - (i.val + 1) % 2) =
      (fun i : Fin n => orb x ((fun i : Fin n => orb x (d 0 - 1) i.val) 0) i.val - i.val % 2) := by
    funext i
    have := congrFun hdd i
    try simp only at this ⊢
    omega
  refine ⟨by rw [hpe]; exact hx, fun i => ?_⟩
  have := congrFun hdd i
  omega

/-- Even `n`: `A(t) + [n/2 ≤ t] E(t − n/2) = B(t)`. -/
theorem A_even (hn : 4 ≤ n) (heven : n % 2 = 0) (t : ℕ) :
    Acount n t + (if n / 2 ≤ t then Ecount n (t - n / 2) else 0) = Bcount n t := by
  classical
  set Pairs := (piAntidiag (univ : Finset (Fin n)) t).sigma (fun d => resSet d) with hP
  have hB : Bcount n t = Pairs.card := by rw [hP, card_sigma, Bcount]
  rw [hB, ← card_filter_add_card_filter_not
    (fun p : (_ : Fin n → ℕ) × (Fin n → ℕ) => ∃ d', Res p.2 d' ∧ d' 0 < p.1 0), add_comm]
  have memP : ∀ p : (_ : Fin n → ℕ) × (Fin n → ℕ), p ∈ Pairs ↔ ∑ i, p.1 i = t ∧ Res p.2 p.1 := by
    intro p
    rw [hP, mem_sigma, mem_resSet]
    exact ⟨fun h => ⟨sum_eq_of_mem_piAntidiag h.1, h.2⟩, fun h => ⟨mem_piAntidiag_univ h.1, h.2⟩⟩
  congr 1
  · split_ifs with hm
    · rw [Ecount]
      symm
      refine card_bij' (fun p _ => fun i => p.1 i - (i.val + 1) % 2)
        (fun e _ => ⟨fun i => e i + (i.val + 1) % 2, Xv e⟩) ?_ ?_ ?_ ?_
      · intro p hp
        rw [mem_filter, memP] at hp
        obtain ⟨hx, hd⟩ := pair_struct heven hp.1.2 hp.2
        apply mem_piAntidiag_univ
        have h1 := hp.1.1
        have h2 : ∑ i, p.1 i = ∑ i, (p.1 i - (i.val + 1) % 2) + ∑ i : Fin n, (i.val + 1) % 2 := by
          rw [← sum_add_distrib]; exact sum_congr rfl (fun i _ => hd i)
        rw [(sum_par_even heven).1] at h2
        omega
      · intro e he
        have hs := sum_eq_of_mem_piAntidiag he
        rw [mem_filter, memP]
        obtain ⟨r1, r2⟩ := xv_res_even heven e
        refine ⟨⟨?_, r1⟩, ⟨_, r2, ?_⟩⟩
        · rw [sum_add_distrib, hs, (sum_par_even heven).1]; omega
        · simp
      · intro p hp
        rw [mem_filter, memP] at hp
        obtain ⟨hx, hd⟩ := pair_struct heven hp.1.2 hp.2
        obtain ⟨d, x⟩ := p
        simp only at hx hd ⊢
        rw [← hx]
        congr 1
        funext i
        exact (hd i).symm
      · intro e _
        funext i
        simp
    · symm
      rw [card_eq_zero, filter_eq_empty_iff]
      intro p hp hq
      rw [memP] at hp
      obtain ⟨_, hd⟩ := pair_struct heven hp.2 hq
      have h2 : ∑ i, p.1 i = ∑ i, (p.1 i - (i.val + 1) % 2) + ∑ i : Fin n, (i.val + 1) % 2 := by
        rw [← sum_add_distrib]; exact sum_congr rfl (fun i _ => hd i)
      rw [(sum_par_even heven).1, hp.1] at h2
      omega
  · -- the minimal residuals correspond to the points
    rw [Acount]
    symm
    refine card_bij (fun p _ => p.2) ?_ ?_ ?_
    · intro p hp
      rw [mem_filter, memP] at hp
      have hk : kappa p.2 = t := by rw [kappa_of_res hn hp.1.2, hp.1.1]
      rw [mem_filter]
      exact ⟨hk ▸ mem_box_of_kappa hn _, hk⟩
    · rintro ⟨d, x⟩ hp ⟨d', x'⟩ hp' (hxx : x = x')
      subst hxx
      rw [mem_filter, memP] at hp hp'
      simp only at hp hp'
      have e0 : d 0 = d' 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact hp'.2 ⟨d, hp.1.2, hlt⟩
        · exact hp.2 ⟨d', hp'.1.2, hlt⟩
      have : d = d' := by rw [res_eq_orb x hp.1.2, res_eq_orb x hp'.1.2, e0]
      subst this
      rfl
    · intro x hx
      rw [mem_filter] at hx
      obtain ⟨d0, hd0⟩ := res_exists x heven
      have hex : ∃ a, ∃ d, Res x d ∧ d 0 = a := ⟨d0 0, d0, hd0, rfl⟩
      obtain ⟨d, hd, hda⟩ := Nat.find_spec hex
      refine ⟨⟨d, x⟩, ?_, rfl⟩
      rw [mem_filter, memP]
      refine ⟨⟨by rw [← kappa_of_res hn hd, hx.2], hd⟩, ?_⟩
      rintro ⟨d', hd', hlt⟩
      simp only at hlt
      exact Nat.find_min hex (show d' 0 < Nat.find hex by omega) ⟨d', hd', rfl⟩

end AntiHole
```

### `AHTransfer.lean`

```lean
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Transfer matrices: closed walks and the trace of `Mⁿ`
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open Matrix Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {R : Type*} [CommSemiring R]

/-- Walks `a → s_0 → ⋯ → s_{k-1} → b` of length `k + 1`. -/
theorem pow_succ_apply_walks (M : Matrix α α R) (k : ℕ) (a b : α) :
    ∑ s : Fin k → α, ∏ i : Fin (k + 1),
      M ((Fin.cons a s : Fin (k + 1) → α) i) ((Fin.snoc s b : Fin (k + 1) → α) i) =
      (M ^ (k + 1)) a b := by
  induction k generalizing a with
  | zero =>
    simp
    rfl
  | succ k ih =>
    rw [pow_succ', mul_apply]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => α)).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl (fun c _ => ?_)
    rw [← ih c, mul_sum]
    refine sum_congr rfl (fun s' _ => ?_)
    try simp only [Fin.consEquiv_apply]
    rw [Fin.prod_univ_succ]
    congr 1
    refine prod_congr rfl (fun i _ => ?_)
    change M (Fin.cons (α := fun _ => α) a (Fin.cons (α := fun _ => α) c s') i.succ)
      (Fin.snoc (α := fun _ => α) (Fin.cons (α := fun _ => α) c s') b i.succ) = _
    rw [Fin.cons_succ, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ]

/-- The sum over closed walks of length `k + 1` is the trace of `M^(k+1)`. -/
theorem trace_pow_eq_cyclic (M : Matrix α α R) (k : ℕ) :
    trace (M ^ (k + 1)) = ∑ s : Fin (k + 1) → α, ∏ i : Fin (k + 1), M (s i) (s (i + 1)) := by
  rw [trace, ← (Fin.consEquiv (fun _ : Fin (k + 1) => α)).sum_comp, Fintype.sum_prod_type]
  simp only [diag_apply]
  refine sum_congr rfl (fun a _ => ?_)
  rw [← pow_succ_apply_walks]
  refine sum_congr rfl (fun s _ => prod_congr rfl (fun i _ => ?_))
  try simp only [Fin.consEquiv_apply]
  congr 1
  induction i using Fin.lastCases with
  | last => rw [Fin.last_add_one, Fin.cons_zero, Fin.snoc_last]
  | cast j => rw [Fin.coeSucc_eq_succ, Fin.cons_succ, Fin.snoc_castSucc]

variable {S : Type*} [CommRing S]

lemma sq_fin_two (Q : Matrix (Fin 2) (Fin 2) S) : Q ^ 2 = trace Q • Q - det Q • (1 : Matrix _ _ S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring

lemma trace_pow_rec (Q : Matrix (Fin 2) (Fin 2) S) (k : ℕ) :
    trace (Q ^ (k + 2)) = trace Q * trace (Q ^ (k + 1)) - det Q * trace (Q ^ k) := by
  rw [pow_add, sq_fin_two, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, trace_sub, trace_smul,
    trace_smul, ← pow_succ, smul_eq_mul, smul_eq_mul]

/-- Two `2 × 2` matrices with the same trace and determinant have the same power traces. -/
lemma trace_pow_eq_of (Q K : Matrix (Fin 2) (Fin 2) S) (ht : trace Q = trace K)
    (hd : det Q = det K) (k : ℕ) : trace (Q ^ k) = trace (K ^ k) := by
  have : ∀ k, trace (Q ^ k) = trace (K ^ k) ∧ trace (Q ^ (k + 1)) = trace (K ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simp [ht]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [trace_pow_rec, trace_pow_rec, ht, hd, ih.1, ih.2]
  exact (this k).1

end AntiHole
```

### `AHGen.lean`

```lean
import AHCount
import AHTransfer
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Generating functions

`∑_t B(t) z^t = tr(Gⁿ)` for a `2 × 2` matrix `G` of power series (the rank-two factorization of
the residual transfer matrix), and `(1 − z)ⁿ tr(Gⁿ) = tr(Kⁿ)` where `K = [[1, 1], [z, 0]]` is the
transfer matrix of matchings of `C_n`. Also `∑_t E(t) z^t = (1 − z)^{−n}`.
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open PowerSeries Matrix Finset Fin.NatCast

/-- Coefficients of the row "`d_i ≥ 1`": next state `d_{i+1} ≥ 1` (weight 1) ... -/
def g00 (m : ℕ) : ℤ := if 1 ≤ m then 1 else 0

/-- ... and next state `d_{i+1} = 0` (weight `d_i + 1`). -/
def g01 (m : ℕ) : ℤ := if 1 ≤ m then (m : ℤ) + 1 else 0

/-- The type-level transfer matrix (state 0: `d_i ≥ 1`; state 1: `d_i = 0`). -/
noncomputable def Gm : Matrix (Fin 2) (Fin 2) ℤ⟦X⟧ :=
  Matrix.of fun σ τ => if σ = 0 then (if τ = 0 then mk g00 else mk g01) else 1

/-- The matching transfer matrix `K = [[1, 1], [z, 0]]` (state 1: the edge `{i, i+1}` is used). -/
noncomputable def Km : Matrix (Fin 2) (Fin 2) ℤ⟦X⟧ :=
  Matrix.of fun σ τ => if σ = 0 then 1 else (if τ = 0 then X else 0)

lemma fin2_cases (σ : Fin 2) : σ = 0 ∨ σ = 1 := by fin_cases σ <;> simp

lemma coeff_one_sub_X_mul (φ : ℤ⟦X⟧) (m : ℕ) :
    coeff m ((1 - X) * φ) = coeff m φ - (if m = 0 then 0 else coeff (m - 1) φ) := by
  rw [sub_mul, one_mul, map_sub]
  rcases m with _ | m
  · simp
  · rw [coeff_succ_X_mul]; simp

lemma one_sub_X_mul_g00 : (1 - X) * mk g00 = (X : ℤ⟦X⟧) := by
  ext m
  rw [coeff_one_sub_X_mul, coeff_X]
  rcases m with _ | _ | m <;> simp [g00]

def hh (m : ℕ) : ℤ := if m = 0 then 0 else if m = 1 then 2 else 1

lemma one_sub_X_mul_g01 : (1 - X) * mk g01 = mk hh := by
  ext m
  rw [coeff_one_sub_X_mul]
  rcases m with _ | _ | m <;> simp [g01, hh]

lemma one_sub_X_mul_hh : (1 - X) * mk hh = 2 * X - X ^ 2 := by
  ext m
  rw [coeff_one_sub_X_mul, map_sub, coeff_X_pow, show (2 : ℤ⟦X⟧) * X = C 2 * X by simp,
    coeff_C_mul, coeff_X]
  rcases m with _ | _ | _ | m <;> simp [hh]

/-- The weight `#{x_i}` contributed by the pair `(d_i, d_{i+1})`. -/
def wt (u v : ℕ) : ℤ := if v = 0 then (u : ℤ) + 1 else 1

variable {n : ℕ} [NeZero n]

lemma sum_types (d : Fin n → ℕ) :
    ∑ s : Fin n → Fin 2, ∏ i, coeff (d i) (Gm (s i) (s (i + 1))) = ∏ i, wt (d i) (d (i + 1)) := by
  classical
  set s0 : Fin n → Fin 2 := fun i => if d i = 0 then 1 else 0 with hs0
  rw [sum_eq_single s0]
  · refine prod_congr rfl (fun i _ => ?_)
    by_cases h1 : d i = 0 <;> by_cases h2 : d (i + 1) = 0 <;>
      simp [hs0, Gm, wt, h1, h2, g00, g01, coeff_one]
  · intro s _ hs
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hs
    apply prod_eq_zero (mem_univ i)
    by_cases h1 : d i = 0
    · have : s i = 0 := by
        rcases fin2_cases (s i) with h | h
        · exact h
        · exact absurd (by simp [hs0, h1, h]) hi
      rcases fin2_cases (s (i + 1)) with h' | h' <;> simp [Gm, this, h', h1, g00, g01]
    · have : s i = 1 := by
        rcases fin2_cases (s i) with h | h
        · exact absurd (by simp [hs0, h1, h]) hi
        · exact h
      simp [Gm, this, coeff_one, h1]
  · intro h; exact absurd (mem_univ _) h

lemma sum_finsuppAntidiag_eq (t : ℕ) (F : (Fin n → ℕ) → ℤ) :
    ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) t, F l =
      ∑ d ∈ piAntidiag (univ : Finset (Fin n)) t, F d := by
  rw [finsuppAntidiag, sum_map]
  exact sum_attach _ F

lemma card_resSet_eq (d : Fin n → ℕ) : ((resSet d).card : ℤ) = ∏ i, wt (d i) (d (i + 1)) := by
  rw [card_resSet, Nat.cast_prod]
  rw [← Equiv.prod_comp (Equiv.addRight (1 : Fin n))]
  refine prod_congr rfl (fun i _ => ?_)
  simp only [Equiv.coe_addRight, add_sub_cancel_right, wt]
  split_ifs <;> simp

theorem coeff_trace_G (k t : ℕ) :
    coeff t (trace (Gm ^ (k + 1))) = (Bcount (k + 1) t : ℤ) := by
  classical
  rw [trace_pow_eq_cyclic, map_sum]
  simp_rw [coeff_prod]
  rw [sum_comm, Bcount, Nat.cast_sum]
  rw [sum_finsuppAntidiag_eq t (fun d => ∑ s : Fin (k + 1) → Fin 2,
    ∏ i, coeff (d i) (Gm (s i) (s (i + 1))))]
  refine sum_congr rfl (fun d _ => ?_)
  rw [sum_types, card_resSet_eq]

lemma trace_Q : trace ((1 - X : ℤ⟦X⟧) • Gm) = 1 := by
  rw [trace_fin_two]
  simp only [Matrix.smul_apply, smul_eq_mul, Gm, of_apply]
  simp [one_sub_X_mul_g00]

lemma det_Q : det ((1 - X : ℤ⟦X⟧) • Gm) = -X := by
  rw [det_fin_two]
  simp only [Matrix.smul_apply, smul_eq_mul, Gm, of_apply]
  simp only [ite_true, ite_false, mul_one, one_sub_X_mul_g00, one_sub_X_mul_g01,
    show (1 : Fin 2) ≠ 0 by decide]
  have := one_sub_X_mul_hh
  calc X * (1 - X) - mk hh * (1 - X) = X * (1 - X) - (1 - X) * mk hh := by ring
    _ = -X := by rw [this]; ring

lemma trace_K : trace Km = 1 := by
  rw [trace_fin_two]; simp [Km]

lemma det_K : det Km = -X := by
  rw [det_fin_two]; simp [Km]

theorem B_gen (k : ℕ) :
    mk (fun t => (Bcount (k + 1) t : ℤ)) * (1 - X) ^ (k + 1) = trace (Km ^ (k + 1)) := by
  have hB : mk (fun t => (Bcount (k + 1) t : ℤ)) = trace (Gm ^ (k + 1)) := by
    ext t; rw [coeff_mk, coeff_trace_G]
  rw [hB, ← trace_pow_eq_of _ _ (trace_Q.trans trace_K.symm) (det_Q.trans det_K.symm), smul_pow,
    trace_smul, smul_eq_mul, mul_comm]

theorem E_gen : mk (fun t => (Ecount n t : ℤ)) * (1 - X) ^ n = 1 := by
  have hE : mk (fun t => (Ecount n t : ℤ)) = (mk 1) ^ n := by
    ext t
    have hp : (mk 1 : ℤ⟦X⟧) ^ n = ∏ _i : Fin n, mk 1 := by simp
    rw [coeff_mk, hp, coeff_prod]
    simp only [coeff_mk, Pi.one_apply, prod_const_one, sum_const, nsmul_eq_mul, mul_one]
    rw [Ecount, finsuppAntidiag, card_map, card_attach]
  rw [hE, ← mul_pow, mk_one_mul_one_sub_eq_one, one_pow]

end AntiHole
```

### `AHMatch.lean`

```lean
import AHGen

/-!
# Perfectly matchable sets of `C_n` and matchings

A matching of `C_n` is a sequence `m : Fin n → Fin 2` (`m_i = 1` iff the edge `{i, i+1}` is used)
with no two consecutive ones. Its vertex set `V(m)` is perfectly matchable, every perfectly
matchable set arises this way, and `V(m)` determines `m` unless `V(m)` is everything; the full
vertex set comes from exactly the two alternating matchings when `n` is even and from none when `n`
is odd. Hence `p(C_n; z) + [n even] z^{n/2} = ∑_{matchings} z^{|m|}`.
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open SimpleGraph Finset Fin.NatCast

variable {n : ℕ} [NeZero n]

/-- No two consecutive edges. -/
def Valid (m : Fin n → Fin 2) : Prop := ∀ i, ¬ (m i = 1 ∧ m (i + 1) = 1)

instance (m : Fin n → Fin 2) : Decidable (Valid m) := by unfold Valid; infer_instance

/-- The edges used. -/
def ones (m : Fin n → Fin 2) : Finset (Fin n) := univ.filter (fun i => m i = 1)

/-- The vertices covered. -/
def vset (m : Fin n → Fin 2) : Finset (Fin n) := univ.filter (fun i => m i = 1 ∨ m (i - 1) = 1)

/-- The matching polynomial of `C_n`. -/
noncomputable def matchPoly (n : ℕ) [NeZero n] : Polynomial ℤ :=
  ∑ m ∈ univ.filter (fun m : Fin n → Fin 2 => Valid m), Polynomial.X ^ (ones m).card

lemma fin2_ne_one {a : Fin 2} (h : a ≠ 1) : a = 0 := by
  rcases fin2_cases a with h' | h'
  · exact h'
  · exact absurd h' h

/-! ### The transfer trace equals the matching polynomial -/

theorem trace_K_pow (k : ℕ) :
    Matrix.trace (Km ^ (k + 1)) = ((matchPoly (k + 1) : Polynomial ℤ) : PowerSeries ℤ) := by
  classical
  rw [trace_pow_eq_cyclic, matchPoly, ← Polynomial.coeToPowerSeries.ringHom_apply,
    map_sum, sum_filter]
  refine sum_congr rfl (fun m _ => ?_)
  by_cases hv : Valid m
  · rw [ite_eq_left hv, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
    have : ∀ i, Km (m i) (m (i + 1)) = if m i = 1 then PowerSeries.X else 1 := by
      intro i
      have := hv i
      rcases fin2_cases (m i) with h | h <;> rcases fin2_cases (m (i + 1)) with h' | h' <;>
        simp_all [Km]
    simp only [this]
    rw [prod_ite, prod_const, prod_const_one, mul_one]
    simp [ones]
  · rw [ite_eq_right hv]
    simp only [Valid, not_forall, not_not] at hv
    obtain ⟨i, h1, h2⟩ := hv
    exact prod_eq_zero (mem_univ i) (by simp [Km, h1, h2])

/-! ### Vertex sets of matchings -/

lemma mem_vset (m : Fin n → Fin 2) (i : Fin n) : i ∈ vset m ↔ (m i = 1 ∨ m (i - 1) = 1) := by
  simp [vset]

lemma card_vset (m : Fin n → Fin 2) (hv : Valid m) : (vset m).card = 2 * (ones m).card := by
  classical
  have e : vset m = ones m ∪ (ones m).image (· + 1) := by
    ext i
    simp only [mem_vset, mem_union, mem_image, ones, mem_filter, mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨i - 1, h, sub_add_cancel i 1⟩
    · rintro (h | ⟨j, hj, rfl⟩)
      · exact Or.inl h
      · right; rw [add_sub_cancel_right]; exact hj
  have hd : Disjoint (ones m) ((ones m).image (· + 1)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [ones, mem_filter, mem_univ, true_and, mem_image] at hi hi'
    obtain ⟨j, hj, rfl⟩ := hi'
    exact hv j ⟨hj, hi⟩
  rw [e, card_union_of_disjoint hd, card_image_of_injective _ (add_left_injective 1)]
  omega

/-- The vertex set of a matching is perfectly matchable. -/
theorem pm_of_valid (hn : 3 ≤ n) {m : Fin n → Fin 2} (hv : Valid m) :
    IsPerfectlyMatchable (cycleGraph n) (vset m : Set (Fin n)) := by
  refine ⟨{ verts := (vset m : Set (Fin n))
            Adj := fun u v => (m u = 1 ∧ v = u + 1) ∨ (m v = 1 ∧ u = v + 1)
            adj_sub := ?_
            edge_vert := ?_
            symm := ?_ }, rfl, ?_⟩
  · rintro u v (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact adj_succ hn u
    · exact (adj_succ hn v).symm
  · rintro u v (⟨h, _⟩ | ⟨h, rfl⟩)
    · exact Finset.mem_coe.2 ((mem_vset m u).2 (Or.inl h))
    · exact Finset.mem_coe.2 ((mem_vset m _).2 (Or.inr (by rw [add_sub_cancel_right]; exact h)))
  · exact ⟨fun u v h => h.symm⟩
  · intro v hvv
    change v ∈ (vset m : Set (Fin n)) at hvv
    rw [Finset.mem_coe, mem_vset] at hvv
    by_cases h1 : m v = 1
    · refine ⟨v + 1, Or.inl ⟨h1, rfl⟩, ?_⟩
      rintro w (⟨_, rfl⟩ | ⟨hw, rfl⟩)
      · rfl
      · exact absurd ⟨hw, h1⟩ (hv w)
    · have h2 : m (v - 1) = 1 := hvv.resolve_left h1
      refine ⟨v - 1, Or.inr ⟨h2, by rw [sub_add_cancel]⟩, ?_⟩
      rintro w (⟨hw, _⟩ | ⟨_, rfl⟩)
      · exact absurd hw h1
      · rw [add_sub_cancel_right]

/-- Every perfectly matchable set of `C_n` is the vertex set of a matching. -/
theorem valid_of_pm (hn : 3 ≤ n) {S : Finset (Fin n)}
    (h : IsPerfectlyMatchable (cycleGraph n) (S : Set (Fin n))) : ∃ m, Valid m ∧ vset m = S := by
  classical
  obtain ⟨M, hMv, hM⟩ := h
  set m : Fin n → Fin 2 := fun i => if M.Adj i (i + 1) then 1 else 0 with hm
  have hm1 : ∀ i, m i = 1 ↔ M.Adj i (i + 1) := by
    intro i; simp only [hm]; split_ifs with h <;> simp [h]
  refine ⟨m, ?_, ?_⟩
  · rintro i ⟨h1, h2⟩
    rw [hm1] at h1 h2
    have hv : i + 1 ∈ M.verts := M.edge_vert h2
    obtain ⟨w, _, hw⟩ := hM hv
    have e1 := hw i h1.symm
    have e2 := hw (i + 1 + 1) h2
    have hval := congrArg Fin.val (e1.trans e2.symm)
    rw [val_add_one', val_add_one'] at hval
    have := i.isLt
    split_ifs at hval <;> omega
  · ext i
    rw [mem_vset, hm1, hm1, sub_add_cancel, ← Finset.mem_coe, ← hMv]
    constructor
    · rintro (h | h)
      · exact M.edge_vert h
      · exact M.edge_vert h.symm
    · intro hi
      obtain ⟨w, hw, _⟩ := hM hi
      have hG := M.adj_sub hw
      rw [adj_iff_add hn] at hG
      rcases hG with rfl | rfl
      · exact Or.inl hw
      · right; rw [add_sub_cancel_right]; exact hw.symm

/-- A proper vertex set determines the matching. -/
theorem valid_unique {m m' : Fin n → Fin 2} (hv : Valid m) (hv' : Valid m')
    (he : vset m = vset m') {j : Fin n} (hj : j ∉ vset m) : m = m' := by
  have hj' : j ∉ vset m' := he ▸ hj
  rw [mem_vset, not_or] at hj hj'
  have key : ∀ k : ℕ, m (j + k) = m' (j + k) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, add_zero]
      rw [fin2_ne_one hj.1, fin2_ne_one hj'.1]
    | succ k ih =>
      set p := j + (k : Fin n) with hp
      rw [Nat.cast_succ, ← add_assoc, ← hp]
      have hmem : (p + 1 ∈ vset m) ↔ (p + 1 ∈ vset m') := by rw [he]
      rw [mem_vset, mem_vset, add_sub_cancel_right, ih] at hmem
      by_cases h1 : m' p = 1
      · have a := hv p
        have b := hv' p
        rw [ih] at a
        rw [fin2_ne_one (fun h => a ⟨h1, h⟩), fin2_ne_one (fun h => b ⟨h1, h⟩)]
      · have hh : m (p + 1) = 1 ↔ m' (p + 1) = 1 := by tauto
        rcases fin2_cases (m (p + 1)) with h | h <;> rcases fin2_cases (m' (p + 1)) with h' | h' <;>
          rw [h, h'] <;> rw [h, h'] at hh <;> first | rfl | exact absurd hh (by decide)
  funext i
  have := key (i - j).val
  rwa [natCast_val, add_sub_cancel] at this

/-! ### The full vertex set -/

/-- The alternating sequences. -/
def alt (c : ℕ) : Fin n → Fin 2 := fun i => if (i.val + c) % 2 = 1 then 1 else 0

lemma alt_eq_one (c : ℕ) (i : Fin n) : alt c i = 1 ↔ (i.val + c) % 2 = 1 := by
  unfold alt; split_ifs with h <;> simp [h]

lemma valid_alt (heven : n % 2 = 0) (c : ℕ) : Valid (alt (n := n) c) := by
  rintro i ⟨h1, h2⟩
  rw [alt_eq_one] at h1 h2
  rw [val_add_one'] at h2
  have := i.isLt
  split_ifs at h2 <;> omega

lemma vset_alt (heven : n % 2 = 0) (c : ℕ) : vset (alt (n := n) c) = univ := by
  ext i
  simp only [mem_vset, alt_eq_one, mem_univ, iff_true]
  rw [val_sub_one']
  have := i.isLt
  split_ifs <;> omega

lemma eq_alt {m : Fin n → Fin 2} (hv : Valid m) (hu : vset m = univ) :
    m = alt (if m 0 = 1 then 1 else 0) := by
  set c := if m 0 = 1 then 1 else 0 with hc
  have key : ∀ k : ℕ, m (k : Fin n) = 1 ↔ (k + c) % 2 = 1 := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_add, hc]
      by_cases h : m 0 = 1 <;> simp [h]
    | succ k ih =>
      have step : m ((k : Fin n) + 1) = 1 ↔ ¬ m (k : Fin n) = 1 := by
        constructor
        · intro h h'; exact hv _ ⟨h', h⟩
        · intro h
          have hm : (k : Fin n) + 1 ∈ vset m := by rw [hu]; exact mem_univ _
          rw [mem_vset, add_sub_cancel_right] at hm
          exact hm.resolve_right h
      rw [Nat.cast_succ, step, ih]
      omega
  funext i
  have := key i.val
  rw [natCast_val, ← alt_eq_one] at this
  rcases fin2_cases (m i) with h | h <;> rcases fin2_cases (alt c i) with h' | h' <;>
    rw [h, h'] <;> rw [h, h'] at this <;> first | rfl | exact absurd this (by decide)

lemma fiber_univ_card :
    (univ.filter (fun m : Fin n → Fin 2 => Valid m ∧ vset m = univ)).card =
      if n % 2 = 0 then 2 else 0 := by
  classical
  split_ifs with he
  · have e : univ.filter (fun m : Fin n → Fin 2 => Valid m ∧ vset m = univ) = {alt 0, alt 1} := by
      ext m
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hv, hu⟩
        rw [eq_alt hv hu]
        by_cases h : m 0 = 1 <;> simp [h]
      · rintro (rfl | rfl)
        · exact ⟨valid_alt he 0, vset_alt he 0⟩
        · exact ⟨valid_alt he 1, vset_alt he 1⟩
    rw [e, card_pair]
    intro h
    have := congrFun h 0
    simp [alt] at this
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro m _ ⟨hv, hu⟩
    have := card_vset m hv
    rw [hu, card_univ, Fintype.card_fin] at this
    omega

/-! ### `p(C_n; z) + [n even] z^{n/2} = ` matching polynomial -/

open Classical in
lemma pmPoly_eq_sum (hn : 3 ≤ n) :
    pmPoly n = ∑ S ∈ univ.filter (fun S : Finset (Fin n) =>
      IsPerfectlyMatchable (cycleGraph n) (S : Set (Fin n))), Polynomial.X ^ (S.card / 2) := by
  have heven : ∀ S : Finset (Fin n), IsPerfectlyMatchable (cycleGraph n) (S : Set (Fin n)) →
      S.card = 2 * (S.card / 2) := by
    intro S hS
    obtain ⟨m, hv, rfl⟩ := valid_of_pm hn hS
    rw [card_vset m hv]; omega
  rw [← sum_fiberwise_of_maps_to (g := fun S : Finset (Fin n) => S.card / 2)
    (t := range (n / 2 + 1))]
  · rw [pmPoly]
    refine sum_congr rfl (fun k _ => ?_)
    rw [sum_congr rfl (g := fun _ => Polynomial.X ^ k) (fun S hS => by
      rw [mem_filter] at hS; rw [hS.2]), sum_const, nsmul_eq_mul, map_natCast]
    congr 2
    rw [pmCount]
    congr 1
    ext S
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rw [heven S h1, h2], h1⟩
  · intro S _
    rw [mem_range]
    have : S.card ≤ n := by simpa using card_le_univ S
    omega

theorem pmPoly_add (hn : 3 ≤ n) :
    pmPoly n + (if n % 2 = 0 then Polynomial.X ^ (n / 2) else 0) = matchPoly n := by
  classical
  set PM := univ.filter (fun S : Finset (Fin n) =>
      IsPerfectlyMatchable (cycleGraph n) (S : Set (Fin n))) with hPM
  set V := univ.filter (fun m : Fin n → Fin 2 => Valid m) with hV
  have hmp : matchPoly n = ∑ S ∈ PM, ∑ m ∈ V.filter (fun m => vset m = S),
      Polynomial.X ^ (S.card / 2) := by
    rw [matchPoly, ← sum_fiberwise_of_maps_to (s := V) (t := PM) (g := vset)]
    · refine sum_congr rfl (fun S _ => sum_congr rfl (fun m hm => ?_))
      rw [mem_filter, hV, mem_filter] at hm
      rw [← hm.2, card_vset m hm.1.2]
      congr 1; omega
    · intro m hm
      rw [hV, mem_filter] at hm
      rw [hPM, mem_filter]
      exact ⟨mem_univ _, pm_of_valid hn hm.2⟩
  have hfib : ∀ S ∈ PM, (V.filter (fun m => vset m = S)).card =
      if S = univ then (if n % 2 = 0 then 2 else 0) else 1 := by
    intro S hS
    rw [hPM, mem_filter] at hS
    by_cases hu : S = univ
    · rw [ite_eq_left hu]
      subst hu
      rw [← fiber_univ_card (n := n), hV, filter_filter]
    · rw [ite_eq_right hu, card_eq_one]
      obtain ⟨m, hv, rfl⟩ := valid_of_pm hn hS.2
      refine ⟨m, ?_⟩
      ext m'
      simp only [hV, mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hv', he⟩
        obtain ⟨j, hj⟩ : ∃ j, j ∉ vset m := by
          by_contra hc; push Not at hc; exact hu (eq_univ_of_forall hc)
        exact (valid_unique hv hv' he.symm hj).symm
      · rintro rfl; exact ⟨hv, rfl⟩
  rw [hmp, pmPoly_eq_sum hn, ← hPM]
  simp_rw [sum_const]
  conv_rhs => rw [sum_congr rfl (g := fun S => (if S = univ then (if n % 2 = 0 then 2 else 0) else 1) •
    Polynomial.X ^ (S.card / 2)) (fun S hS => by rw [hfib S hS])]
  by_cases he : n % 2 = 0
  · have hu : univ ∈ PM := by
      rw [hPM, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have := pm_of_valid hn (valid_alt he 0)
      rwa [vset_alt he 0] at this
    simp only [he, ↓reduceIte]
    rw [← add_sum_erase PM _ hu, ← add_sum_erase PM _ hu, card_univ, Fintype.card_fin]
    simp only [↓reduceIte]
    conv_rhs => rw [sum_congr rfl (fun S hS => by rw [ite_eq_right (ne_of_mem_erase hS)])]
    simp only [one_smul, two_smul]
    ring
  · simp only [he, ↓reduceIte, add_zero]
    refine sum_congr rfl (fun S hS => ?_)
    by_cases hu : S = univ
    · exfalso
      rw [hPM, mem_filter, hu] at hS
      obtain ⟨m, hv, hm⟩ := valid_of_pm hn hS.2
      have := card_vset m hv
      rw [hm, card_univ, Fintype.card_fin] at this
      omega
    · rw [ite_eq_right hu, one_smul]

end AntiHole
```

### `AHMain.lean`

```lean
import AHMatch

/-!
# Davis–Kohl Conjecture 3.15 for all `n ≥ 4`
-/

set_option linter.unusedSectionVars false

namespace AntiHole

open PowerSeries Finset

lemma mk_ehr (n : ℕ) [NeZero n] (hn : 4 ≤ n) :
    mk (fun t => (ehr n t : ℤ)) = mk (fun t => (Acount n t : ℤ)) * mk 1 := by
  ext t
  rw [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ehr_eq_sum hn,
    Nat.cast_sum]
  refine sum_congr rfl (fun s _ => ?_)
  simp

lemma coe_X_pow (m : ℕ) : (((Polynomial.X ^ m : Polynomial ℤ)) : ℤ⟦X⟧) = X ^ m := by
  rw [Polynomial.coe_pow, Polynomial.coe_X]

theorem hstar_formula (n : ℕ) (hn : 4 ≤ n) :
    mk (fun t => (ehr n t : ℤ)) * (1 - X) ^ (n + 1) =
      ((pmPoly n + (if Odd n then Polynomial.X ^ ((n + 1) / 2) else 0) : Polynomial ℤ) :
        PowerSeries ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hpm := pmPoly_add (n := k + 1) (by omega)
  have hA : mk (fun t => (ehr (k + 1) t : ℤ)) * (1 - X) ^ (k + 1 + 1) =
      mk (fun t => (Acount (k + 1) t : ℤ)) * (1 - X) ^ (k + 1) := by
    have h1 : (mk 1 : ℤ⟦X⟧) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one ℤ
    rw [mk_ehr _ hn]
    calc mk (fun t => (Acount (k + 1) t : ℤ)) * mk 1 * (1 - X) ^ (k + 1 + 1)
        = mk (fun t => (Acount (k + 1) t : ℤ)) * ((mk 1 : ℤ⟦X⟧) * (1 - X)) * (1 - X) ^ (k + 1) := by
          ring
      _ = _ := by rw [h1, mul_one]
  rw [hA]
  rcases Nat.mod_two_eq_zero_or_one (k + 1) with he | ho
  · have hnodd : ¬ Odd (k + 1) := by rw [Nat.odd_iff]; omega
    simp only [he, ↓reduceIte] at hpm
    simp only [hnodd, ↓reduceIte, add_zero]
    have hsum : mk (fun t => (Acount (k + 1) t : ℤ)) +
        X ^ ((k + 1) / 2) * mk (fun t => (Ecount (k + 1) t : ℤ)) =
        mk (fun t => (Bcount (k + 1) t : ℤ)) := by
      ext t
      rw [map_add, coeff_X_pow_mul', coeff_mk, coeff_mk, coeff_mk, ← A_even hn he t]
      split_ifs <;> simp
    have h1 := congrArg (· * (1 - X) ^ (k + 1)) hsum
    simp only [add_mul, mul_assoc, E_gen, mul_one, B_gen, trace_K_pow] at h1
    rw [← hpm, Polynomial.coe_add, coe_X_pow] at h1
    rw [← sub_eq_of_eq_add h1.symm]  
    ring
  · have hodd : Odd (k + 1) := by rw [Nat.odd_iff]; omega
    have hne : k + 1 ≠ 0 := by omega
    simp only [show ¬ ((k + 1) % 2 = 0) by omega, ↓reduceIte, add_zero] at hpm
    simp only [hodd, ↓reduceIte]
    have hsum : mk (fun t => (Acount (k + 1) t : ℤ)) =
        mk (fun t => (Bcount (k + 1) t : ℤ)) +
          X ^ ((k + 1 + 1) / 2) * mk (fun t => (Ecount (k + 1) t : ℤ)) := by
      ext t
      rw [map_add, coeff_X_pow_mul', coeff_mk, coeff_mk, coeff_mk, A_odd hn ho t]
      split_ifs <;> simp
    rw [hsum, add_mul, mul_assoc, E_gen, mul_one, B_gen, trace_K_pow, hpm, Polynomial.coe_add,
      coe_X_pow]

/-- **Davis–Kohl, Conjecture 3.15** (arXiv:2207.14759): for all `n ≥ 4`,
`h̄*(C_n; z) = p(C_n; z) + ((1 + (−1)^{n+1})/2) z^{(n+1)/2}`. -/
theorem davis_kohl_conjecture_3_15 : Conjecture315 := fun n hn => hstar_formula n hn

/-- The same statement with the source's literal coefficient `(1 + (−1)^{n+1})/2`. -/
theorem davis_kohl_conjecture_3_15_literal (n : ℕ) (hn : 4 ≤ n) :
    mk (fun t => (ehr n t : ℤ)) * (1 - X) ^ (n + 1) =
      ((pmPoly n + Polynomial.C ((1 + (-1 : ℤ) ^ (n + 1)) / 2) * Polynomial.X ^ ((n + 1) / 2) :
        Polynomial ℤ) : PowerSeries ℤ) := by
  rw [hstar_formula n hn]
  congr 2
  rcases Nat.even_or_odd n with he | ho
  · have hn' : ¬ Odd n := Nat.not_odd_iff_even.2 he
    rw [ite_eq_right hn', (he.add_one).neg_one_pow]
    simp
  · rw [ite_eq_left ho, (ho.add_one).neg_one_pow]
    simp

/-- `L(0) = 1`, matching the constant term of the source's `Ehr_P(z) = 1 + ∑_{m ≥ 1} L_P(m) z^m`. -/
theorem ehr_zero (n : ℕ) (hn : 4 ≤ n) : ehr n 0 = 1 := by
  have : NeZero n := ⟨by omega⟩
  rw [ehr_eq_card hn]
  have hb : box n 0 = {0} := by
    ext x
    simp only [box, Fintype.mem_piFinset, Finset.mem_range, Finset.mem_singleton, funext_iff,
      Pi.zero_apply]
    exact forall_congr' (fun i => by omega)
  have hk : kappa (0 : Fin n → ℕ) = 0 := by
    rw [kappa_of_res hn (d := 0) (fun i => by simp)]
    simp
  rw [hb, Finset.filter_singleton, hk, ite_eq_left le_rfl, Finset.card_singleton]

/-! ### Non-vacuity: the source's Table 2 for `n = 4, 5, 6, 7` -/

lemma trace_Km_pow_rec (j : ℕ) :
    Matrix.trace (Km ^ (j + 2)) = Matrix.trace (Km ^ (j + 1)) + X * Matrix.trace (Km ^ j) := by
  rw [trace_pow_rec, trace_K, det_K]; ring

lemma trace_Km_table :
    Matrix.trace (Km ^ 4) = 1 + 4 * X + 2 * X ^ 2 ∧
    Matrix.trace (Km ^ 5) = 1 + 5 * X + 5 * X ^ 2 ∧
    Matrix.trace (Km ^ 6) = 1 + 6 * X + 9 * X ^ 2 + 2 * X ^ 3 ∧
    Matrix.trace (Km ^ 7) = 1 + 7 * X + 14 * X ^ 2 + 7 * X ^ 3 := by
  have t0 : Matrix.trace (Km ^ 0) = 2 := by
    rw [pow_zero, Matrix.trace_one, Fintype.card_fin]; norm_num
  have t1 : Matrix.trace (Km ^ 1) = 1 := by rw [pow_one, trace_K]
  have t2 : Matrix.trace (Km ^ 2) = 1 + 2 * X := by rw [trace_Km_pow_rec 0, t1, t0]; ring
  have t3 : Matrix.trace (Km ^ 3) = 1 + 3 * X := by rw [trace_Km_pow_rec 1, t2, t1]; ring
  have t4 : Matrix.trace (Km ^ 4) = 1 + 4 * X + 2 * X ^ 2 := by
    rw [trace_Km_pow_rec 2, t3, t2]; ring
  have t5 : Matrix.trace (Km ^ 5) = 1 + 5 * X + 5 * X ^ 2 := by
    rw [trace_Km_pow_rec 3, t4, t3]; ring
  have t6 : Matrix.trace (Km ^ 6) = 1 + 6 * X + 9 * X ^ 2 + 2 * X ^ 3 := by
    rw [trace_Km_pow_rec 4, t5, t4]; ring
  have t7 : Matrix.trace (Km ^ 7) = 1 + 7 * X + 14 * X ^ 2 + 7 * X ^ 3 := by
    rw [trace_Km_pow_rec 5, t6, t5]; ring
  exact ⟨t4, t5, t6, t7⟩

lemma hstar_eq_trace (k : ℕ) (hn : 4 ≤ k + 1) :
    mk (fun t => (ehr (k + 1) t : ℤ)) * (1 - X) ^ (k + 1 + 1) =
      Matrix.trace (Km ^ (k + 1)) - (if (k + 1) % 2 = 0 then X ^ ((k + 1) / 2) else 0) +
        (if Odd (k + 1) then X ^ ((k + 1 + 1) / 2) else 0) := by
  rw [hstar_formula _ hn, Polynomial.coe_add, trace_K_pow, ← pmPoly_add (by omega),
    Polynomial.coe_add]
  split_ifs <;> simp

/-- Table 2: `h̄*(C_4) = 1 + 4z + z²`. -/
theorem table2_n4 : mk (fun t => (ehr 4 t : ℤ)) * (1 - X) ^ 5 = 1 + 4 * X + X ^ 2 := by
  have := hstar_eq_trace 3 (by norm_num)
  rw [trace_Km_table.1] at this
  rw [this]; norm_num [Nat.odd_iff]; ring

/-- Table 2: `h̄*(C_5) = 1 + 5z + 5z² + z³`. -/
theorem table2_n5 : mk (fun t => (ehr 5 t : ℤ)) * (1 - X) ^ 6 = 1 + 5 * X + 5 * X ^ 2 + X ^ 3 := by
  have := hstar_eq_trace 4 (by norm_num)
  rw [trace_Km_table.2.1] at this
  rw [this]; norm_num [Nat.odd_iff]

/-- Table 2: `h̄*(C_6) = 1 + 6z + 9z² + z³`. -/
theorem table2_n6 :
    mk (fun t => (ehr 6 t : ℤ)) * (1 - X) ^ 7 = 1 + 6 * X + 9 * X ^ 2 + X ^ 3 := by
  have := hstar_eq_trace 5 (by norm_num)
  rw [trace_Km_table.2.2.1] at this
  rw [this]; norm_num [Nat.odd_iff]; ring

/-- Table 2: `h̄*(C_7) = 1 + 7z + 14z² + 7z³ + z⁴`. -/
theorem table2_n7 :
    mk (fun t => (ehr 7 t : ℤ)) * (1 - X) ^ 8 = 1 + 7 * X + 14 * X ^ 2 + 7 * X ^ 3 + X ^ 4 := by
  have := hstar_eq_trace 6 (by norm_num)
  rw [trace_Km_table.2.2.2] at this
  rw [this]; norm_num [Nat.odd_iff]

end AntiHole
```

### `AHAxioms.lean`

```lean
import AHMain

/-! Statements and axiom reports of the endpoints. -/

open AntiHole

#check @AntiHole.indicatorVec
#print AntiHole.indicatorVec
#print AntiHole.stabPolytope
#print AntiHole.P
#print AntiHole.ehr
#print AntiHole.IsPerfectlyMatchable
#print AntiHole.pmCount
#print AntiHole.pmPoly
#print AntiHole.Conjecture315
#check @AntiHole.davis_kohl_conjecture_3_15
#check @AntiHole.hstar_formula
#check @AntiHole.davis_kohl_conjecture_3_15_literal
#check @AntiHole.ehr_zero
#check @AntiHole.vectorSpan_P
#check @AntiHole.mem_iff_kappa
#check @AntiHole.table2_n4
#check @AntiHole.table2_n5
#check @AntiHole.table2_n6
#check @AntiHole.table2_n7
#print axioms AntiHole.davis_kohl_conjecture_3_15
#print axioms AntiHole.hstar_formula
#print axioms AntiHole.davis_kohl_conjecture_3_15_literal
#print axioms AntiHole.ehr_zero
#print axioms AntiHole.vectorSpan_P
#print axioms AntiHole.mem_iff_kappa
#print axioms AntiHole.table2_n4
#print axioms AntiHole.table2_n5
#print axioms AntiHole.table2_n6
#print axioms AntiHole.table2_n7
```

