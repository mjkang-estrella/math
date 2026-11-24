# Lean source appendix (MathDB 361202)

Modules are listed in import order; each block is byte-identical to `src/<Module>.lean`.
Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (see PINS.json).

### `TCMDefs.lean`

```lean
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max

/-!
# Definitions for MathDB 361202 (Peaslee–Sali–Yan, Conjecture 6.3)

Source: W. Peaslee, A. Sali, J. Yan, *An intermediate case of exponential multivalued
forbidden matrix configuration*, arXiv:2312.11446, Definition 1.3 and Question 1.4.

A triangular choice multigraph (TCM) on `Fin m` chooses one edge in every vertex triple;
we record the choice by the excluded vertex.  `mult q x y` is the multiplicity of the edge
`xy`, `w q α = ∑_{x<y} α ^ mult q x y`, `H` is the maximum of `w` over all TCMs and `H₂` the
maximum over 2-recursive TCMs (Definition 1.3, restricted to triples inside a vertex set).
These are the definitions fixed in REVIEW-361202.md, "Required Lean endpoint".
-/

namespace PSY

/-- Vertex triples of `[m]`. -/
def Triple (m : ℕ) := {t : Finset (Fin m) // t.card = 3}

instance (m : ℕ) : DecidableEq (Triple m) :=
  inferInstanceAs (DecidableEq {t : Finset (Fin m) // t.card = 3})

instance (m : ℕ) : Fintype (Triple m) :=
  inferInstanceAs (Fintype {t : Finset (Fin m) // t.card = 3})

/-- A TCM: for every triple, the excluded vertex (the chosen edge is the other two). -/
def TCM (m : ℕ) := ∀ t : Triple m, {x : Fin m // x ∈ t.1}

instance (m : ℕ) : Fintype (TCM m) :=
  inferInstanceAs (Fintype (∀ t : Triple m, {x : Fin m // x ∈ t.1}))

variable {m : ℕ}

/-- Multiplicity of the edge `xy`: the number of triples containing `x, y` in which `xy`
is the chosen edge. -/
def mult (q : TCM m) (x y : Fin m) : ℕ :=
  (Finset.univ.filter (fun t : Triple m =>
    x ∈ t.1 ∧ y ∈ t.1 ∧ (q t).1 ≠ x ∧ (q t).1 ≠ y)).card

/-- The weight `w(G, α) = ∑_{xy} α ^ (m_xy)`. -/
def w (q : TCM m) (α : ℝ) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset (Fin m)).offDiag.filter (fun p => p.1 < p.2),
    α ^ mult q e.1 e.2

/-- 2-recursive on a vertex set `S`, as in Definition 1.3 restricted to triples inside `S`. -/
inductive TwoRec (q : TCM m) : Finset (Fin m) → Prop
  | small {S : Finset (Fin m)} : S.card ≤ 2 → TwoRec q S
  | split {S V₁ V₂ : Finset (Fin m)} : V₁.Nonempty → V₂.Nonempty → Disjoint V₁ V₂ →
      V₁ ∪ V₂ = S → TwoRec q V₁ → TwoRec q V₂ →
      (∀ t : Triple m, t.1 ⊆ S → (t.1 ∩ V₁).card = 2 → (q t).1 ∈ V₂) →
      (∀ t : Triple m, t.1 ⊆ S → (t.1 ∩ V₂).card = 2 → (q t).1 ∈ V₁) →
      TwoRec q S

lemma triple_nonempty (t : Triple m) : t.1.Nonempty :=
  Finset.card_pos.mp (by have := t.2; omega)

/-- An explicit TCM: every triple excludes its largest vertex. -/
def maxTCM (m : ℕ) : TCM m := fun t => ⟨t.1.max' (triple_nonempty t), Finset.max'_mem _ _⟩

/-- `maxTCM` is 2-recursive on every vertex set (split off the largest vertex). -/
theorem maxTCM_twoRec (m : ℕ) : ∀ S : Finset (Fin m), TwoRec (maxTCM m) S := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S.card ≤ 2
    · exact TwoRec.small hS
    · have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      set M := S.max' hne with hM
      have hMS : M ∈ S := Finset.max'_mem _ _
      have hcard : (S.erase M).card = S.card - 1 := Finset.card_erase_of_mem hMS
      refine TwoRec.split (V₁ := S.erase M) (V₂ := {M}) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact Finset.card_pos.mp (by omega)
      · exact Finset.singleton_nonempty _
      · simp
      · ext v; by_cases h : v = M <;> simp [h, hMS]
      · exact ih _ (Finset.erase_ssubset hMS)
      · exact TwoRec.small (by simp)
      · intro t htS ht2
        have hnot : ¬ t.1 ⊆ S.erase M := by
          intro hsub
          have : t.1 ∩ S.erase M = t.1 := Finset.inter_eq_left.mpr hsub
          rw [this, t.2] at ht2; omega
        obtain ⟨v, hvt, hvn⟩ := Finset.not_subset.mp hnot
        have hvM : v = M := by
          by_contra hne'
          exact hvn (Finset.mem_erase.mpr ⟨hne', htS hvt⟩)
        subst hvM
        simp only [maxTCM, Finset.mem_singleton]
        apply le_antisymm
        · exact Finset.max'_le _ _ _ (fun y hy => Finset.le_max' _ _ (htS hy))
        · exact Finset.le_max' _ _ hvt
      · intro t _ ht2
        have : (t.1 ∩ {M}).card ≤ 1 :=
          (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
        omega

instance (m : ℕ) : Nonempty (TCM m) := ⟨maxTCM m⟩

/-- `H(m, α)`: maximum weight of a TCM on `[m]`. -/
noncomputable def H (m : ℕ) (α : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun q : TCM m => w q α)

open Classical in
/-- The set of 2-recursive TCMs on `[m]` is nonempty (witness `maxTCM`). -/
theorem twoRec_nonempty (m : ℕ) :
    (Finset.univ.filter (fun q : TCM m => TwoRec q Finset.univ)).Nonempty :=
  ⟨maxTCM m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, maxTCM_twoRec m _⟩⟩

open Classical in
/-- `H₂(m, α)`: maximum weight of a 2-recursive TCM on `[m]`. -/
noncomputable def H₂ (m : ℕ) (α : ℝ) : ℝ :=
  (Finset.univ.filter (fun q : TCM m => TwoRec q Finset.univ)).sup' (twoRec_nonempty m)
    (fun q => w q α)

end PSY
```

### `TCMBasic.lean`

```lean
import TCMDefs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Basic access to TCMs through vertex triples

`ex q x y z` is the excluded vertex of the triple `{x, y, z}` (with a symmetric default when
`x, y, z` are not distinct).  We prove the bridge `mult q x y = #{z | ex q x y z = z}`, the
ordered double-sum form of `w`, and a transfer lemma for `TwoRec`.
-/

namespace PSY

variable {m : ℕ}

/-- Excluded vertex of a finset `s` of size 3 (default `d` otherwise). -/
def exs (q : TCM m) (s : Finset (Fin m)) (d : Fin m) : Fin m :=
  if h : s.card = 3 then (q ⟨s, h⟩).1 else d

/-- Excluded vertex of the triple `{x, y, z}`. -/
def ex (q : TCM m) (x y z : Fin m) : Fin m := exs q {x, y, z} (min x (min y z))

lemma card3 {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Finset (Fin m)).card = 3 :=
  Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩

lemma q_congr (q : TCM m) {t t' : Triple m} (h : t.1 = t'.1) : (q t).1 = (q t').1 := by
  obtain ⟨s, hs⟩ := t; obtain ⟨s', hs'⟩ := t'
  simp only at h; subst h; rfl

lemma exs_of_card (q : TCM m) {s : Finset (Fin m)} (h : s.card = 3) (d : Fin m) :
    exs q s d = (q ⟨s, h⟩).1 := by
  unfold exs; simp only [h, ↓reduceDIte]

lemma exs_of_eq (q : TCM m) (t : Triple m) {s : Finset (Fin m)} (h : t.1 = s) (d : Fin m) :
    exs q s d = (q t).1 := by
  rw [exs_of_card q (h ▸ t.2)]; exact q_congr q h.symm

lemma ex_of_eq (q : TCM m) (t : Triple m) {x y z : Fin m} (h : t.1 = {x, y, z}) :
    ex q x y z = (q t).1 := exs_of_eq q t h _

lemma ex_congr (q : TCM m) {x y z x' y' z' : Fin m}
    (h : ({x, y, z} : Finset (Fin m)) = {x', y', z'})
    (hd : min x (min y z) = min x' (min y' z')) : ex q x y z = ex q x' y' z' := by
  unfold ex exs
  by_cases h1 : ({x, y, z} : Finset (Fin m)).card = 3
  · have h2 : ({x', y', z'} : Finset (Fin m)).card = 3 := h ▸ h1
    simp only [h1, h2, ↓reduceDIte]; exact q_congr q h
  · have h2 : ¬ ({x', y', z'} : Finset (Fin m)).card = 3 := h ▸ h1
    simp only [h1, h2, ↓reduceDIte, hd]

lemma ex_comm12 (q : TCM m) (x y z : Fin m) : ex q x y z = ex q y x z :=
  ex_congr q (Finset.insert_comm x y {z}) (min_left_comm x y z)

lemma ex_comm23 (q : TCM m) (x y z : Fin m) : ex q x y z = ex q x z y :=
  ex_congr q (by rw [Finset.pair_comm]) (by rw [min_comm y z])

lemma ex_rot (q : TCM m) (x y z : Fin m) : ex q x y z = ex q y z x := by
  rw [ex_comm12, ex_comm23]

lemma ex_mem (q : TCM m) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ex q x y z = x ∨ ex q x y z = y ∨ ex q x y z = z := by
  have h3 := card3 hxy hxz hyz
  have hm : (q ⟨_, h3⟩).1 ∈ ({x, y, z} : Finset (Fin m)) := (q ⟨_, h3⟩).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  unfold ex; rw [exs_of_card q h3]; exact hm

lemma triple_eq (t : Triple m) {x y z : Fin m} (hx : x ∈ t.1) (hy : y ∈ t.1) (hz : z ∈ t.1)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : t.1 = {x, y, z} := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  · rw [t.2, card3 hxy hxz hyz]

/-- Bridge: the multiplicity of `xy` counts third vertices `z` with `xy` chosen. -/
theorem mult_eq (q : TCM m) {x y : Fin m} (hxy : x ≠ y) :
    mult q x y = (Finset.univ.filter (fun z => z ≠ x ∧ z ≠ y ∧ ex q x y z = z)).card := by
  unfold mult
  refine Finset.card_bij' (fun t _ => (q t).1)
    (fun z hz => ⟨{x, y, z}, card3 hxy (Ne.symm (Finset.mem_filter.mp hz).2.1)
      (Ne.symm (Finset.mem_filter.mp hz).2.2.1)⟩) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨hx, hy, h1, h2⟩ := (Finset.mem_filter.mp ht).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, ?_⟩
    exact ex_of_eq q t (triple_eq t hx hy (q t).2 hxy (Ne.symm h1) (Ne.symm h2))
  · intro z hz
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp hz).2
    have e := ex_of_eq q ⟨{x, y, z}, card3 hxy (Ne.symm h1) (Ne.symm h2)⟩ rfl
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp, by simp, ?_, ?_⟩ <;>
      rw [← e, h3] <;> assumption
  · intro t ht
    obtain ⟨hx, hy, h1, h2⟩ := (Finset.mem_filter.mp ht).2
    exact Subtype.ext (triple_eq t hx hy (q t).2 hxy (Ne.symm h1) (Ne.symm h2)).symm
  · intro z hz
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp hz).2
    rw [← ex_of_eq q ⟨{x, y, z}, card3 hxy (Ne.symm h1) (Ne.symm h2)⟩ rfl, h3]

lemma mult_comm (q : TCM m) (x y : Fin m) : mult q x y = mult q y x := by
  unfold mult; congr 1
  apply Finset.filter_congr; intro t _; tauto

lemma ite_pos' {β : Sort*} {c : Prop} [Decidable c] {a b : β} (h : c) :
    (if c then a else b) = a := by simp [h]

lemma ite_neg' {β : Sort*} {c : Prop} [Decidable c] {a b : β} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- Ordered double sum of the weights. -/
noncomputable def F (q : TCM m) (α : ℝ) : ℝ :=
  ∑ x, ∑ y, if x = y then 0 else α ^ mult q x y

theorem two_mul_w (q : TCM m) (α : ℝ) : 2 * w q α = F q α := by
  have hoff : (Finset.univ : Finset (Fin m)).offDiag =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin m × Fin m => p.1 ≠ p.2) := by
    ext p; simp
  have h1 : F q α = ∑ p ∈ (Finset.univ : Finset (Fin m)).offDiag, α ^ mult q p.1 p.2 := by
    rw [hoff, Finset.sum_filter, F, Finset.sum_product]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    by_cases h : x = y <;> simp [h]
  have h2 : ∑ p ∈ (Finset.univ : Finset (Fin m)).offDiag.filter (fun p => ¬ p.1 < p.2),
      α ^ mult q p.1 p.2 =
      ∑ p ∈ (Finset.univ : Finset (Fin m)).offDiag.filter (fun p => p.1 < p.2),
      α ^ mult q p.1 p.2 := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      rw [Finset.mem_offDiag] at hp'
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
      · rw [Finset.mem_offDiag]; exact ⟨Finset.mem_univ _, Finset.mem_univ _, Ne.symm hp'.1.2.2⟩
      · exact lt_of_le_of_ne (not_lt.mp hp'.2) (Ne.symm hp'.1.2.2)
    · intro p hp
      have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      rw [Finset.mem_offDiag] at hp'
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
      · rw [Finset.mem_offDiag]; exact ⟨Finset.mem_univ _, Finset.mem_univ _, Ne.symm hp'.1.2.2⟩
      · exact not_lt.mpr (le_of_lt hp'.2)
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp [mult_comm q p.1 p.2]
  rw [h1, ← Finset.sum_filter_add_sum_filter_not _ (fun p : Fin m × Fin m => p.1 < p.2), h2, w]
  ring

/-- `TwoRec` depends only on the choices on triples inside the vertex set. -/
theorem TwoRec.congr {q r : TCM m} {S : Finset (Fin m)} (h : TwoRec q S)
    (hqr : ∀ t : Triple m, t.1 ⊆ S → (q t).1 = (r t).1) : TwoRec r S := by
  revert hqr
  induction h with
  | small h => intro _; exact .small h
  | split h1 h2 hd hU _ _ c1 c2 ih1 ih2 =>
    intro hqr
    refine .split h1 h2 hd hU
      (ih1 fun t ht => hqr t (ht.trans (hU ▸ Finset.subset_union_left)))
      (ih2 fun t ht => hqr t (ht.trans (hU ▸ Finset.subset_union_right))) ?_ ?_
    · intro t ht h; rw [← hqr t ht]; exact c1 t ht h
    · intro t ht h; rw [← hqr t ht]; exact c2 t ht h

/-- A closed block: a pair inside `S` is chosen whenever the third vertex is outside. -/
def Closed (q : TCM m) (S : Finset (Fin m)) : Prop :=
  ∀ x y z, x ∈ S → y ∈ S → x ≠ y → z ∉ S → ex q x y z = z

/-- Uniform exterior choices of a block `S`. -/
def Unif (q : TCM m) (S : Finset (Fin m)) : Prop :=
  ∀ x x' z w, x ∈ S → x' ∈ S → z ∉ S → w ∉ S → z ≠ w → (ex q x z w = z ↔ ex q x' z w = z)

end PSY
```

### `TCMClone.lean`

```lean
import TCMBasic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Cloning a closed block (Lemma 2 of the proof, weight part)

For a block `U` and a vertex `u ∈ U`, `clone q U u` changes only the triples with exactly one
vertex `v` in `U`: such a triple copies the choice of `q` on the triple obtained by replacing
`v` with `u`.  If `U` is closed, then `∑_{u ∈ U} F (clone q U u) ≥ |U| · F q`.
-/

namespace PSY

variable {m : ℕ}

/-- Replace every vertex of `U` by `u`. -/
def phi (U : Finset (Fin m)) (u : Fin m) (v : Fin m) : Fin m := if v ∈ U then u else v

/-- The value chosen by the clone on the vertex set `s` whose unique `U`-vertex is `v`. -/
def cloneSel (q : TCM m) (U : Finset (Fin m)) (u : Fin m) (s : Finset (Fin m)) (v : Fin m) :
    Fin m :=
  if exs q (s.image (phi U u)) v = u then v else exs q (s.image (phi U u)) v

lemma cloneSel_mem (q : TCM m) (U : Finset (Fin m)) (u : Fin m)
    {s : Finset (Fin m)} {v : Fin m} (hv : s.filter (· ∈ U) = {v}) :
    cloneSel q U u s v ∈ s := by
  have hvs : v ∈ s := by
    have : v ∈ s.filter (· ∈ U) := hv ▸ Finset.mem_singleton_self v
    exact (Finset.mem_filter.mp this).1
  unfold cloneSel
  split_ifs with he
  · exact hvs
  · unfold exs at he ⊢
    by_cases hc : (s.image (phi U u)).card = 3
    · simp only [hc, ↓reduceDIte] at he ⊢
      have hmem : (q ⟨_, hc⟩).1 ∈ s.image (phi U u) := (q ⟨_, hc⟩).2
      obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp hmem
      by_cases hyU : y ∈ U
      · simp only [phi, hyU, ↓reduceIte] at hye; exact absurd hye.symm he
      · simp only [phi, hyU, ↓reduceIte] at hye; rw [← hye]; exact hy
    · simp only [hc, ↓reduceDIte]; exact hvs

/-- The clone of `q` along `u` with respect to the block `U`. -/
noncomputable def clone (q : TCM m) (U : Finset (Fin m)) (u : Fin m) : TCM m := fun t =>
  if h : (t.1.filter (· ∈ U)).card = 1 then
    ⟨cloneSel q U u t.1 (Finset.card_eq_one.mp h).choose,
      cloneSel_mem q U u (Finset.card_eq_one.mp h).choose_spec⟩
  else q t

lemma clone_val_ne (q : TCM m) (U : Finset (Fin m)) (u : Fin m) (t : Triple m)
    (h : (t.1.filter (· ∈ U)).card ≠ 1) : (clone q U u t).1 = (q t).1 := by
  unfold clone
  simp only [h, ↓reduceDIte]

lemma clone_val_eq (q : TCM m) (U : Finset (Fin m)) (u : Fin m) (t : Triple m)
    {v : Fin m} (h : t.1.filter (· ∈ U) = {v}) :
    (clone q U u t).1 = cloneSel q U u t.1 v := by
  have hc : (t.1.filter (· ∈ U)).card = 1 := by rw [h]; rfl
  have hch : (Finset.card_eq_one.mp hc).choose = v :=
    Finset.singleton_inj.mp ((Finset.card_eq_one.mp hc).choose_spec.symm.trans h)
  unfold clone
  simp only [hc, ↓reduceDIte]
  rw [hch]

lemma exs_default (q : TCM m) {s : Finset (Fin m)} (h : s.card = 3) (d d' : Fin m) :
    exs q s d = exs q s d' := by
  rw [exs_of_card q h, exs_of_card q h]

/-- Triples with a number of `U`-vertices other than one are unchanged. -/
lemma ex_clone_ne (q : TCM m) (U : Finset (Fin m)) (u : Fin m) {x y z : Fin m}
    (h : (({x, y, z} : Finset (Fin m)).filter (· ∈ U)).card ≠ 1) :
    ex (clone q U u) x y z = ex q x y z := by
  unfold ex exs
  by_cases h3 : ({x, y, z} : Finset (Fin m)).card = 3
  · simp only [h3, ↓reduceDIte]
    exact clone_val_ne q U u ⟨_, h3⟩ h
  · simp only [h3, ↓reduceDIte]

lemma ex_clone_two (q : TCM m) (U : Finset (Fin m)) (u : Fin m) {x y z : Fin m}
    (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) : ex (clone q U u) x y z = ex q x y z := by
  apply ex_clone_ne
  have : 1 < (({x, y, z} : Finset (Fin m)).filter (· ∈ U)).card :=
    Finset.one_lt_card.mpr ⟨x, by simp [hx], y, by simp [hy], hxy⟩
  omega

lemma ex_clone_zero (q : TCM m) (U : Finset (Fin m)) (u : Fin m) {x y z : Fin m}
    (hx : x ∉ U) (hy : y ∉ U) (hz : z ∉ U) : ex (clone q U u) x y z = ex q x y z := by
  apply ex_clone_ne
  have : ({x, y, z} : Finset (Fin m)).filter (· ∈ U) = ∅ := by
    ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, iff_false, not_and]
    rintro (rfl | rfl | rfl) <;> assumption
  rw [this]; simp

/-- The key formula: a triple with exactly one `U`-vertex `x` copies `q` on `{u, y, z}`. -/
lemma ex_clone_one (q : TCM m) (U : Finset (Fin m)) {u : Fin m} (hu : u ∈ U) {x y z : Fin m}
    (hx : x ∈ U) (hy : y ∉ U) (hz : z ∉ U) (hyz : y ≠ z) :
    ex (clone q U u) x y z = if ex q u y z = u then x else ex q u y z := by
  have hxy : x ≠ y := fun h => hy (h ▸ hx)
  have hxz : x ≠ z := fun h => hz (h ▸ hx)
  have huy : u ≠ y := fun h => hy (h ▸ hu)
  have huz : u ≠ z := fun h => hz (h ▸ hu)
  have h3 := card3 hxy hxz hyz
  have hf : ({x, y, z} : Finset (Fin m)).filter (· ∈ U) = {x} := by
    ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hv⟩
      · rfl
      · exact absurd hv hy
      · exact absurd hv hz
    · rintro rfl; exact ⟨Or.inl rfl, hx⟩
  have himg : ({x, y, z} : Finset (Fin m)).image (phi U u) = {u, y, z} := by
    simp [Finset.image_insert, phi, hx, hy, hz]
  have hval := clone_val_eq q U u ⟨_, h3⟩ hf
  unfold ex
  rw [exs_of_card _ h3, hval]
  simp only [cloneSel, himg]
  rw [exs_default q (card3 huy huz hyz) x (min u (min y z))]

/-! ### Loads of the clone in the three edge classes -/

lemma mult_clone_in (q : TCM m) (U : Finset (Fin m)) (u : Fin m) {x y : Fin m}
    (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) : mult (clone q U u) x y = mult q x y := by
  rw [mult_eq _ hxy, mult_eq _ hxy]
  congr 1
  apply Finset.filter_congr
  intro z _
  rw [ex_clone_two q U u hx hy hxy]

lemma mult_clone_mixed (q : TCM m) {U : Finset (Fin m)} (hU : Closed q U) {u : Fin m}
    (hu : u ∈ U) {x y : Fin m} (hx : x ∈ U) (hy : y ∉ U) :
    mult (clone q U u) x y = mult q u y := by
  have hxy : x ≠ y := fun h => hy (h ▸ hx)
  have huy : u ≠ y := fun h => hy (h ▸ hu)
  rw [mult_eq _ hxy, mult_eq _ huy]
  congr 1
  apply Finset.filter_congr
  intro z _
  by_cases hz : z ∈ U
  · constructor
    · rintro ⟨hzx, hzy, he⟩
      rw [ex_comm23, ex_clone_two q U u hx hz (Ne.symm hzx), hU x z y hx hz (Ne.symm hzx) hy]
        at he
      exact absurd he.symm hzy
    · rintro ⟨hzu, hzy, he⟩
      rw [ex_comm23, hU u z y hu hz (Ne.symm hzu) hy] at he
      exact absurd he.symm hzy
  · have hzx : z ≠ x := fun h => hz (h ▸ hx)
    have hzu : z ≠ u := fun h => hz (h ▸ hu)
    constructor
    · rintro ⟨_, hzy, he⟩
      rw [ex_clone_one q U hu hx hy hz (Ne.symm hzy)] at he
      refine ⟨hzu, hzy, ?_⟩
      split_ifs at he with hc
      · exact absurd he.symm hzx
      · exact he
    · rintro ⟨_, hzy, he⟩
      refine ⟨hzx, hzy, ?_⟩
      rw [ex_clone_one q U hu hx hy hz (Ne.symm hzy), ite_neg' (by rw [he]; exact hzu)]
      exact he

/-- Splitting a count of third vertices into the part in `U` and the part outside. -/
lemma card_split_U (U : Finset (Fin m)) (P : Fin m → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (U.filter P).card + (Finset.univ.filter (fun z => z ∉ U ∧ P z)).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter P) (· ∈ U)]
  congr 1
  · congr 1; ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  · congr 1; ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto

/-- Count of outside third vertices choosing `xy`. -/
def Rout (q : TCM m) (U : Finset (Fin m)) (x y : Fin m) : ℕ :=
  (Finset.univ.filter (fun z => z ∉ U ∧ (z ≠ x ∧ z ≠ y ∧ ex q x y z = z))).card

lemma mult_q_out (q : TCM m) (U : Finset (Fin m)) {x y : Fin m} (hx : x ∉ U) (hy : y ∉ U)
    (hxy : x ≠ y) :
    mult q x y = (U.filter (fun z => ex q x y z = z)).card + Rout q U x y := by
  rw [mult_eq _ hxy, card_split_U U, Rout]
  congr 2
  apply Finset.filter_congr
  intro z hz
  have hzx : z ≠ x := fun h => hx (h ▸ hz)
  have hzy : z ≠ y := fun h => hy (h ▸ hz)
  simp [hzx, hzy]

lemma mult_clone_out (q : TCM m) (U : Finset (Fin m)) {u : Fin m} (hu : u ∈ U) {x y : Fin m}
    (hx : x ∉ U) (hy : y ∉ U) (hxy : x ≠ y) :
    mult (clone q U u) x y = (if ex q x y u = u then U.card else 0) + Rout q U x y := by
  rw [mult_eq _ hxy, card_split_U U, Rout]
  congr 1
  · split_ifs with hc
    · congr 1
      apply Finset.filter_true_of_mem
      intro z hz
      have hzx : z ≠ x := fun h => hx (h ▸ hz)
      have hzy : z ≠ y := fun h => hy (h ▸ hz)
      refine ⟨hzx, hzy, ?_⟩
      rw [ex_rot, ex_rot, ex_clone_one q U hu hz hx hy hxy, ex_rot q u x y, hc]
      simp
    · rw [Finset.card_eq_zero]
      apply Finset.filter_false_of_mem
      rintro z hz ⟨hzx, hzy, he⟩
      rw [ex_rot, ex_rot, ex_clone_one q U hu hz hx hy hxy] at he
      have hc' : ex q u x y ≠ u := by rw [ex_rot q u x y]; exact hc
      rw [ite_neg' hc'] at he
      have hux : u ≠ x := fun h => hx (h ▸ hu)
      have huy : u ≠ y := fun h => hy (h ▸ hu)
      have hmem := ex_mem q hux huy hxy
      rcases hmem with h | h | h
      · exact hc' h
      · exact hzx (he ▸ h)
      · exact hzy (he ▸ h)
  · congr 1
    apply Finset.filter_congr
    intro z _
    constructor
    · rintro ⟨hz, h1, h2, he⟩; exact ⟨hz, h1, h2, by rwa [ex_clone_zero q U u hx hy hz] at he⟩
    · rintro ⟨hz, h1, h2, he⟩; exact ⟨hz, h1, h2, by rwa [ex_clone_zero q U u hx hy hz]⟩

/-! ### Two-point Jensen for `k ↦ α ^ k` -/

theorem jensen_nat {α : ℝ} (hα : 0 < α) {n k : ℕ} (hk : k ≤ n) :
    (n : ℝ) * α ^ k ≤ k * α ^ n + (n - k) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; have : k = 0 := by omega
    subst this; simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h1 : (0 : ℝ) ≤ k / n := by positivity
  have h2 : (0 : ℝ) ≤ (n - k) / n := div_nonneg (by linarith) hnR.le
  have h12 : (k : ℝ) / n + (n - k) / n = 1 := by field_simp; ring
  have hc := convexOn_exp.2 (Set.mem_univ ((n : ℝ) * Real.log α)) (Set.mem_univ 0) h1 h2 h12
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hc
  have e1 : (k : ℝ) / n * (n * Real.log α) = k * Real.log α := by field_simp
  rw [e1, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hα] at hc
  have := mul_le_mul_of_nonneg_left hc hnR.le
  calc (n : ℝ) * α ^ k ≤ n * (k / n * α ^ n + (n - k) / n) := this
    _ = k * α ^ n + (n - k) := by field_simp

/-! ### The averaged clone inequality -/

lemma split4 (U : Finset (Fin m)) (h : Fin m → Fin m → ℝ) :
    ∑ x, ∑ y, h x y = (∑ x ∈ U, ∑ y ∈ U, h x y + ∑ x ∈ U, ∑ y ∈ Uᶜ, h x y) +
      (∑ x ∈ Uᶜ, ∑ y ∈ U, h x y + ∑ x ∈ Uᶜ, ∑ y ∈ Uᶜ, h x y) := by
  have e1 : ∀ x, ∑ y, h x y = ∑ y ∈ U, h x y + ∑ y ∈ Uᶜ, h x y :=
    fun x => (Finset.sum_add_sum_compl U _).symm
  rw [← Finset.sum_add_sum_compl U]
  simp only [e1, Finset.sum_add_distrib]

/-- Lemma 2 (weight part): if `U` is closed, the clones along the vertices of `U` have average
ordered weight at least that of `q`. -/
theorem clone_avg (q : TCM m) {U : Finset (Fin m)} (hU : Closed q U) {α : ℝ} (hα : 0 < α) :
    (U.card : ℝ) * F q α ≤ ∑ u ∈ U, F (clone q U u) α := by
  set n : ℝ := (U.card : ℝ) with hn
  set f : Fin m → Fin m → ℝ := fun x y => if x = y then 0 else α ^ mult q x y with hf
  set G : Fin m → Fin m → ℝ :=
    fun x y => ∑ u ∈ U, (if x = y then 0 else α ^ mult (clone q U u) x y) with hG
  set K : Fin m → ℝ := fun y => ∑ u ∈ U, α ^ mult q u y with hK
  have hL : n * F q α = ∑ x, ∑ y, n * f x y := by
    simp only [F, hf, Finset.mul_sum]
  have hR : ∑ u ∈ U, F (clone q U u) α = ∑ x, ∑ y, G x y := by
    simp only [F, hG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
  rw [hL, hR, split4 U, split4 U (fun x y => G x y)]
  -- class `U × U`: equality
  have hA : ∑ x ∈ U, ∑ y ∈ U, n * f x y = ∑ x ∈ U, ∑ y ∈ U, G x y := by
    refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => ?_))
    simp only [hf, hG]
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, ↓reduceIte, mult_clone_in q U _ hx hy hxy, Finset.sum_const,
        nsmul_eq_mul, hn]
  -- mixed classes
  have hGm : ∀ x ∈ U, ∀ y ∈ Uᶜ, G x y = K y := by
    intro x hx y hy
    have hy' : y ∉ U := Finset.mem_compl.mp hy
    have hxy : x ≠ y := fun h => hy' (h ▸ hx)
    simp only [hG, hK, hxy, ↓reduceIte]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [mult_clone_mixed q hU hu hx hy']
  have hB : ∑ x ∈ U, ∑ y ∈ Uᶜ, n * f x y = ∑ x ∈ U, ∑ y ∈ Uᶜ, G x y := by
    have e1 : ∑ x ∈ U, ∑ y ∈ Uᶜ, G x y = ∑ x ∈ U, ∑ y ∈ Uᶜ, K y :=
      Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => hGm x hx y hy))
    have e2 : ∑ x ∈ U, ∑ y ∈ Uᶜ, n * f x y = ∑ x ∈ U, ∑ y ∈ Uᶜ, n * α ^ mult q x y := by
      refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => ?_))
      have hxy : x ≠ y := fun h => (Finset.mem_compl.mp hy) (h ▸ hx)
      simp [hf, hxy]
    rw [e1, e2, Finset.sum_comm, Finset.sum_comm (f := fun x y => K y)]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [hK, Finset.sum_const, nsmul_eq_mul, hn, Finset.mul_sum]
  have hC : ∑ x ∈ Uᶜ, ∑ y ∈ U, n * f x y = ∑ x ∈ Uᶜ, ∑ y ∈ U, G x y := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx' : x ∉ U := Finset.mem_compl.mp hx
    have e1 : ∑ y ∈ U, G x y = ∑ y ∈ U, K x := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hxy : x ≠ y := fun h => hx' (h ▸ hy)
      simp only [hG, hK, hxy, ↓reduceIte]
      refine Finset.sum_congr rfl (fun u hu => ?_)
      rw [mult_comm, mult_clone_mixed q hU hu hy hx']
    rw [e1]
    simp only [hK, hf, Finset.sum_const, nsmul_eq_mul, hn, ← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have hxy : x ≠ y := fun h => hx' (h ▸ hy)
    simp [hxy, mult_comm q x y]
  -- class outside × outside: Jensen
  have hD : ∑ x ∈ Uᶜ, ∑ y ∈ Uᶜ, n * f x y ≤ ∑ x ∈ Uᶜ, ∑ y ∈ Uᶜ, G x y := by
    refine Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => ?_))
    have hx' : x ∉ U := Finset.mem_compl.mp hx
    have hy' : y ∉ U := Finset.mem_compl.mp hy
    by_cases hxy : x = y
    · simp [hf, hG, hxy]
    simp only [hf, hG, hxy, ↓reduceIte]
    set k := (U.filter (fun z => ex q x y z = z)).card with hk
    set R := Rout q U x y with hRdef
    have hcl : ∀ u ∈ U, α ^ mult (clone q U u) x y =
        if ex q x y u = u then α ^ (U.card + R) else α ^ R := by
      intro u hu
      rw [mult_clone_out q U hu hx' hy' hxy]
      split_ifs <;> simp [R]
    rw [Finset.sum_congr rfl hcl, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, mult_q_out q U hx' hy' hxy]
    have hcomp := Finset.card_filter_add_card_filter_not (s := U) (fun z => ex q x y z = z)
    have hkn : k ≤ U.card := by rw [hk]; exact Finset.card_filter_le _ _
    have hcR : (((U.filter (fun z => ¬ ex q x y z = z)).card : ℕ) : ℝ) = n - k := by
      rw [hn]; rw [← hcomp]; push_cast; ring
    rw [hcR, ← hk]
    have hJ := jensen_nat hα hkn
    have hαR : 0 ≤ α ^ R := pow_nonneg hα.le R
    have := mul_le_mul_of_nonneg_right hJ hαR
    calc n * α ^ (k + R) = (n * α ^ k) * α ^ R := by rw [pow_add]; ring
      _ ≤ (k * α ^ U.card + (U.card - k)) * α ^ R := this
      _ = k * α ^ (U.card + R) + (n - k) * α ^ R := by rw [pow_add, hn]; ring
  linarith [hA, hB, hC, hD]

/-- Some clone is at least as heavy as `q`. -/
theorem exists_clone_ge (q : TCM m) {U : Finset (Fin m)} (hU : Closed q U) (hne : U.Nonempty)
    {α : ℝ} (hα : 0 < α) : ∃ u ∈ U, w q α ≤ w (clone q U u) α := by
  by_contra hcon
  push Not at hcon
  have h1 := clone_avg q hU hα
  have h2 : ∑ u ∈ U, F (clone q U u) α < ∑ u ∈ U, F q α := by
    apply Finset.sum_lt_sum_of_nonempty hne
    intro u hu
    rw [← two_mul_w, ← two_mul_w]
    linarith [hcon u hu]
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  linarith

end PSY
```

### `TCMMerge.lean`

```lean
import TCMClone

/-!
# Lemma 2 (invariants): cloning a closed union of two good blocks gives a good partition
with one block fewer.

A partition is a labelling `lab : Fin m → Fin m`; block `i` is `blk lab i`.  Empty blocks
are allowed (they are trivially good).
-/

namespace PSY

variable {m : ℕ}

/-- Block `i` of the labelling `lab`. -/
def blk (lab : Fin m → Fin m) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun v => lab v = i)

lemma mem_blk {lab : Fin m → Fin m} {i v : Fin m} : v ∈ blk lab i ↔ lab v = i := by
  simp [blk]

/-- Every block is closed, has uniform exterior choices and is 2-recursive. -/
def Good (q : TCM m) (lab : Fin m → Fin m) : Prop :=
  ∀ i, Closed q (blk lab i) ∧ Unif q (blk lab i) ∧ TwoRec q (blk lab i)

/-- Relabel block `j` as block `i`. -/
def merge (lab : Fin m → Fin m) (i j : Fin m) : Fin m → Fin m :=
  fun v => if lab v = j then i else lab v

lemma blk_merge_i (lab : Fin m → Fin m) {i j : Fin m} :
    blk (merge lab i j) i = blk lab i ∪ blk lab j := by
  ext v; simp only [mem_blk, merge, Finset.mem_union]
  by_cases h : lab v = j <;> simp [h]

lemma blk_merge_j (lab : Fin m → Fin m) {i j : Fin m} (hij : i ≠ j) :
    blk (merge lab i j) j = ∅ := by
  ext v; simp only [mem_blk, merge, Finset.notMem_empty, iff_false]
  by_cases h : lab v = j <;> simp [h, hij]

lemma blk_merge_k (lab : Fin m → Fin m) {i j k : Fin m} (hki : k ≠ i) (hkj : k ≠ j) :
    blk (merge lab i j) k = blk lab k := by
  ext v; simp only [mem_blk, merge]
  by_cases h : lab v = j
  · simp only [h, ↓reduceIte]
    constructor
    · intro h'; exact absurd h'.symm hki
    · intro h'; exact absurd h'.symm hkj
  · simp [h]

lemma card_image_merge (lab : Fin m → Fin m) {i j : Fin m} (hij : i ≠ j)
    (hi : i ∈ Finset.univ.image lab) (hj : j ∈ Finset.univ.image lab) :
    (Finset.univ.image (merge lab i j)).card < (Finset.univ.image lab).card := by
  have hsub : Finset.univ.image (merge lab i j) ⊆ (Finset.univ.image lab).erase j := by
    intro k hk
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hk
    simp only [merge]
    by_cases h : lab v = j
    · simp only [h, ↓reduceIte]; exact Finset.mem_erase.mpr ⟨hij, hi⟩
    · simp only [h, ↓reduceIte]
      exact Finset.mem_erase.mpr ⟨h, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩
  calc (Finset.univ.image (merge lab i j)).card ≤ ((Finset.univ.image lab).erase j).card :=
        Finset.card_le_card hsub
    _ < (Finset.univ.image lab).card := Finset.card_erase_lt_of_mem hj

/-! ### Preservation lemmas for a single clone -/

section clone

variable (q : TCM m) {U : Finset (Fin m)} {u : Fin m}

lemma clone_closed_U (hU : Closed q U) : Closed (clone q U u) U := by
  intro x y z hx hy hxy hz
  rw [ex_clone_two q U u hx hy hxy]; exact hU x y z hx hy hxy hz

lemma ex_clone_one_eq (hu : u ∈ U) {x z w : Fin m} (hx : x ∈ U) (hz : z ∉ U) (hw : w ∉ U)
    (hzw : z ≠ w) : ex (clone q U u) x z w = z ↔ ex q u z w = z := by
  rw [ex_clone_one q U hu hx hz hw hzw]
  have hxz : x ≠ z := fun h => hz (h ▸ hx)
  have huz : u ≠ z := fun h => hz (h ▸ hu)
  split_ifs with hc
  · constructor
    · intro h; exact absurd h hxz
    · intro h; exact absurd (hc.symm.trans h) huz
  · exact Iff.rfl

lemma clone_unif_U (hu : u ∈ U) : Unif (clone q U u) U := by
  intro x x' z w hx hx' hz hw hzw
  rw [ex_clone_one_eq q hu hx hz hw hzw, ex_clone_one_eq q hu hx' hz hw hzw]

variable {C : Finset (Fin m)}

lemma clone_closed_C (hu : u ∈ U) (hCU : Disjoint C U) (hC : Closed q C) :
    Closed (clone q U u) C := by
  intro x y z hx hy hxy hz
  have hxU : x ∉ U := Finset.disjoint_left.mp hCU hx
  have hyU : y ∉ U := Finset.disjoint_left.mp hCU hy
  by_cases hzU : z ∈ U
  · have huC : u ∉ C := Finset.disjoint_right.mp hCU hu
    rw [ex_rot, ex_rot, ex_clone_one q U hu hzU hxU hyU hxy, ex_rot q u x y,
      hC x y u hx hy hxy huC]
    simp
  · rw [ex_clone_zero q U u hxU hyU hzU]; exact hC x y z hx hy hxy hz

lemma clone_unif_C (hu : u ∈ U) (hCU : Disjoint C U) (hC : Unif q C) :
    Unif (clone q U u) C := by
  intro x x' z w hx hx' hz hw hzw
  have hxU : x ∉ U := Finset.disjoint_left.mp hCU hx
  have hxU' : x' ∉ U := Finset.disjoint_left.mp hCU hx'
  have huC : u ∉ C := Finset.disjoint_right.mp hCU hu
  by_cases hzU : z ∈ U <;> by_cases hwU : w ∈ U
  · -- both exterior vertices in `U`: unchanged
    have e : ∀ y, y ∉ U → ex (clone q U u) y z w = ex q y z w := by
      intro y _
      rw [ex_rot, ex_clone_two q U u hzU hwU hzw, ← ex_rot]
    rw [e x hxU, e x' hxU']; exact hC x x' z w hx hx' hz hw hzw
  · -- `z ∈ U`, `w ∉ U`
    have huw : u ≠ w := fun h => hwU (h ▸ hu)
    have e : ∀ y, y ∈ C → y ∉ U → (ex (clone q U u) y z w = z ↔ ex q y u w = u) := by
      intro y hyC hyU
      have hyw : y ≠ w := fun h => hw (h ▸ hyC)
      rw [ex_comm12, ex_clone_one q U hu hzU hyU hwU hyw, ex_comm12 q y u w]
      have hyu : u ≠ y := fun h => hyU (h ▸ hu)
      have hzy : z ≠ y := fun h => hyU (h ▸ hzU)
      have hzw' : z ≠ w := hzw
      split_ifs with hc
      · simp [hc]
      · constructor
        · intro h
          rcases ex_mem q hyu huw hyw with h' | h' | h'
          · exact absurd h' hc
          · exact absurd (h'.symm.trans h) (Ne.symm hzy)
          · exact absurd (h'.symm.trans h) (Ne.symm hzw')
        · intro h; exact absurd h hc
    rw [e x hx hxU, e x' hx' hxU']
    exact hC x x' u w hx hx' huC hw huw
  · -- `z ∉ U`, `w ∈ U`
    have hzu : z ≠ u := fun h => hzU (h ▸ hu)
    have e : ∀ y, y ∈ C → y ∉ U → (ex (clone q U u) y z w = z ↔ ex q y z u = z) := by
      intro y hyC hyU
      have hyz : y ≠ z := fun h => hz (h ▸ hyC)
      rw [ex_rot, ex_rot, ex_clone_one q U hu hwU hyU hzU hyz, ex_rot q u y z]
      have hwz : w ≠ z := fun h => hzU (h ▸ hwU)
      split_ifs with hc
      · constructor
        · intro h; exact absurd h hwz
        · intro h; exact absurd (h.symm.trans hc) hzu
      · exact Iff.rfl
    rw [e x hx hxU, e x' hx' hxU']
    exact hC x x' z u hx hx' hz huC hzu
  · rw [ex_clone_zero q U u hxU hzU hwU, ex_clone_zero q U u hxU' hzU hwU]
    exact hC x x' z w hx hx' hz hw hzw

lemma clone_agree_of_subset {S : Finset (Fin m)} (hS : S ⊆ U) (t : Triple m) (ht : t.1 ⊆ S) :
    (q t).1 = (clone q U u t).1 := by
  rw [clone_val_ne]
  have : t.1.filter (· ∈ U) = t.1 := Finset.filter_true_of_mem (fun v hv => hS (ht hv))
  rw [this, t.2]; omega

lemma clone_agree_of_disjoint {S : Finset (Fin m)} (hS : Disjoint S U) (t : Triple m)
    (ht : t.1 ⊆ S) : (q t).1 = (clone q U u t).1 := by
  rw [clone_val_ne]
  have : t.1.filter (· ∈ U) = ∅ :=
    Finset.filter_false_of_mem (fun v hv => Finset.disjoint_left.mp hS (ht hv))
  rw [this]; simp

end clone

/-- Split condition from closure: a triple inside `A ∪ B` with two vertices in the closed
block `A` excludes its `B`-vertex. -/
lemma split_cond (q : TCM m) {A B : Finset (Fin m)} (hA : Closed q A) (t : Triple m)
    (ht : t.1 ⊆ A ∪ B) (h2 : (t.1 ∩ A).card = 2) : (q t).1 ∈ B := by
  obtain ⟨a1, a2, h12, hA12⟩ := Finset.card_eq_two.mp h2
  have ha1 : a1 ∈ t.1 ∩ A := hA12 ▸ by simp
  have ha2 : a2 ∈ t.1 ∩ A := hA12 ▸ by simp
  rw [Finset.mem_inter] at ha1 ha2
  have hnot : ¬ t.1 ⊆ A := by
    intro hsub
    rw [Finset.inter_eq_left.mpr hsub, t.2] at h2; omega
  obtain ⟨b, hbt, hbA⟩ := Finset.not_subset.mp hnot
  have hbB : b ∈ B := by
    rcases Finset.mem_union.mp (ht hbt) with h | h
    · exact absurd h hbA
    · exact h
  have h1b : a1 ≠ b := fun h => hbA (h ▸ ha1.2)
  have h2b : a2 ≠ b := fun h => hbA (h ▸ ha2.2)
  have hteq := triple_eq t ha1.1 ha2.1 hbt h12 h1b h2b
  rw [← ex_of_eq q t hteq, hA a1 a2 b ha1.2 ha2.2 h12 hbA]
  exact hbB

/-- 2-recursiveness of the union of two closed 2-recursive blocks. -/
lemma twoRec_union (q : TCM m) {A B : Finset (Fin m)} (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hAB : Disjoint A B) (hA : Closed q A) (hB : Closed q B) (hrA : TwoRec q A)
    (hrB : TwoRec q B) : TwoRec q (A ∪ B) := by
  refine TwoRec.split hAn hBn hAB rfl hrA hrB ?_ ?_
  · intro t ht h2; exact split_cond q hA t ht h2
  · intro t ht h2; exact split_cond q hB t (by rw [Finset.union_comm]; exact ht) h2

lemma blk_disjoint (lab : Fin m → Fin m) {i j : Fin m} (hij : i ≠ j) :
    Disjoint (blk lab i) (blk lab j) := by
  rw [Finset.disjoint_left]
  intro v hi hj
  rw [mem_blk] at hi hj
  exact hij (hi.symm.trans hj)

/-- Lemma 2 (invariants): merging two good blocks whose union is closed, via any clone along
a vertex of the union, gives a good labelling with the two blocks merged. -/
theorem good_merge (q : TCM m) (lab : Fin m → Fin m) (hg : Good q lab) {i j : Fin m}
    (hij : i ≠ j) (hin : (blk lab i).Nonempty) (hjn : (blk lab j).Nonempty)
    (hU : Closed q (blk lab i ∪ blk lab j)) {u : Fin m} (hu : u ∈ blk lab i ∪ blk lab j) :
    Good (clone q (blk lab i ∪ blk lab j) u) (merge lab i j) := by
  intro k
  by_cases hki : k = i
  · subst hki
    rw [blk_merge_i]
    refine ⟨clone_closed_U q hU, clone_unif_U q hu, ?_⟩
    have hr := twoRec_union q hin hjn (blk_disjoint lab hij) (hg k).1 (hg j).1 (hg k).2.2
      (hg j).2.2
    exact hr.congr (clone_agree_of_subset q (subset_refl _))
  by_cases hkj : k = j
  · subst hkj
    rw [blk_merge_j lab hij]
    refine ⟨?_, ?_, TwoRec.small (by simp)⟩
    · intro x _ _ hx; simp at hx
    · intro x _ _ _ hx; simp at hx
  rw [blk_merge_k lab hki hkj]
  have hd : Disjoint (blk lab k) (blk lab i ∪ blk lab j) :=
    Finset.disjoint_union_right.mpr ⟨blk_disjoint lab hki, blk_disjoint lab hkj⟩
  refine ⟨clone_closed_C q hu hd (hg k).1, clone_unif_C q hu hd (hg k).2.1, ?_⟩
  exact (hg k).2.2.congr (clone_agree_of_disjoint q hd)

end PSY
```

### `TCMSwitch.lean`

```lean
import TCMMerge

/-!
# Lemma 1, part 1: uniform loads, uniform block triangles, and the block switch

For a good labelling, cross loads and the choices on triples meeting three distinct blocks
depend only on the blocks.  `switch q lab i j k` re-chooses, on every triple meeting blocks
`i, j, k` once each, the pair in blocks `i, j` (it excludes the `k`-vertex).
-/

namespace PSY

variable {m : ℕ}

section uniform

variable {q : TCM m} {lab : Fin m → Fin m}

lemma unif_self {S : Finset (Fin m)} (hS : Unif q S) {x x' z w : Fin m} (hx : x ∈ S)
    (hx' : x' ∈ S) (hz : z ∉ S) (hw : w ∉ S) (hzw : z ≠ w) :
    ex q x z w = x ↔ ex q x' z w = x' := by
  have hxz : x ≠ z := fun h => hz (h ▸ hx)
  have hxw : x ≠ w := fun h => hw (h ▸ hx)
  have hx'z : x' ≠ z := fun h => hz (h ▸ hx')
  have hx'w : x' ≠ w := fun h => hw (h ▸ hx')
  have h1 := hS x x' z w hx hx' hz hw hzw
  have h2 := hS x x' w z hx hx' hw hz (Ne.symm hzw)
  rw [ex_comm23 q x w z, ex_comm23 q x' w z] at h2
  constructor
  · intro h
    rcases ex_mem q hx'z hx'w hzw with e' | e' | e'
    · exact e'
    · exfalso; have := h1.mpr e'; rw [h] at this; exact hxz this
    · exfalso; have := h2.mpr e'; rw [h] at this; exact hxw this
  · intro h
    rcases ex_mem q hxz hxw hzw with e | e | e
    · exact e
    · exfalso; have := h1.mp e; rw [h] at this; exact hx'z this
    · exfalso; have := h2.mp e; rw [h] at this; exact hx'w this

lemma mult_step (hg : Good q lab) {x x' y : Fin m} (hxx : lab x = lab x')
    (hxy : lab x ≠ lab y) : mult q x y = mult q x' y := by
  have hxy' : x ≠ y := fun h => hxy (congrArg lab h)
  have hx'y' : x' ≠ y := fun h => hxy (hxx.trans (congrArg lab h))
  obtain ⟨hC, hU, _⟩ := hg (lab x)
  have hxA : x ∈ blk lab (lab x) := mem_blk.mpr rfl
  have hx'A : x' ∈ blk lab (lab x) := mem_blk.mpr hxx.symm
  have hyA : y ∉ blk lab (lab x) := fun h => hxy (mem_blk.mp h).symm
  rw [mult_eq q hxy', mult_eq q hx'y']
  congr 1
  apply Finset.filter_congr
  intro z _
  by_cases hz : lab z = lab x
  · have hzA : z ∈ blk lab (lab x) := mem_blk.mpr hz
    constructor
    · rintro ⟨h1, h2, h3⟩
      exfalso
      rw [ex_comm23, hC x z y hxA hzA (Ne.symm h1) hyA] at h3
      exact h2 h3.symm
    · rintro ⟨h1, h2, h3⟩
      exfalso
      rw [ex_comm23, hC x' z y hx'A hzA (Ne.symm h1) hyA] at h3
      exact h2 h3.symm
  · have hzA : z ∉ blk lab (lab x) := fun h => hz (mem_blk.mp h)
    have hzx : z ≠ x := fun h => hz (congrArg lab h)
    have hzx' : z ≠ x' := fun h => hz ((congrArg lab h).trans hxx.symm)
    simp only [ne_eq, hzx, hzx', not_false_eq_true, true_and]
    constructor
    · rintro ⟨h2, h3⟩
      refine ⟨h2, ?_⟩
      rw [ex_comm23] at h3 ⊢
      exact (hU x x' z y hxA hx'A hzA hyA h2).mp h3
    · rintro ⟨h2, h3⟩
      refine ⟨h2, ?_⟩
      rw [ex_comm23] at h3 ⊢
      exact (hU x x' z y hxA hx'A hzA hyA h2).mpr h3

/-- Cross loads are constant between two blocks. -/
lemma mult_uniform (hg : Good q lab) {x x' y y' : Fin m} (hxx : lab x = lab x')
    (hyy : lab y = lab y') (hxy : lab x ≠ lab y) : mult q x y = mult q x' y' := by
  rw [mult_step hg hxx hxy, mult_comm, mult_step hg hyy (fun h => hxy (hxx.trans h.symm)),
    mult_comm]

/-- Choices on triples meeting three blocks are constant. -/
lemma triangle_uniform (hg : Good q lab) {x y z : Fin m} (hxy : lab x ≠ lab y)
    (hxz : lab x ≠ lab z) (hyz : lab y ≠ lab z) (h : ex q x y z = x) {x' y' z' : Fin m}
    (hx : lab x' = lab x) (hy : lab y' = lab y) (hz : lab z' = lab z) :
    ex q x' y' z' = x' := by
  have hyx' : lab y ≠ lab x' := by rw [hx]; exact Ne.symm hxy
  have hzx' : lab z ≠ lab x' := by rw [hx]; exact Ne.symm hxz
  -- vary x
  have s1 : ex q x' y z = x' :=
    (unif_self (hg (lab x)).2.1 (mem_blk.mpr rfl) (mem_blk.mpr hx)
      (fun h => hxy (mem_blk.mp h).symm) (fun h => hxz (mem_blk.mp h).symm)
      (fun h => hyz (congrArg lab h))).mp h
  -- vary y
  have s2 : ex q x' y' z = x' := by
    rw [ex_comm12] at s1 ⊢
    exact ((hg (lab y)).2.1 y y' x' z (mem_blk.mpr rfl) (mem_blk.mpr hy)
      (fun h => hyx' (mem_blk.mp h).symm) (fun h => hyz (mem_blk.mp h).symm)
      (fun h => hzx' (congrArg lab h).symm)).mp s1
  -- vary z
  have hy'x' : lab y' ≠ lab x' := by rw [hy]; exact hyx'
  have hzy' : lab z ≠ lab y' := by rw [hy]; exact Ne.symm hyz
  rw [← ex_rot] at s2 ⊢
  exact ((hg (lab z)).2.1 z z' x' y' (mem_blk.mpr rfl) (mem_blk.mpr hz)
    (fun h => hzx' (mem_blk.mp h).symm) (fun h => hzy' (mem_blk.mp h).symm)
    (fun h => hy'x' (congrArg lab h).symm)).mp s2

end uniform

/-! ### Transversal triples -/

lemma card_le_two_of_eq {a b c : Fin m} (h : a = b ∨ a = c ∨ b = c) :
    ({a, b, c} : Finset (Fin m)).card ≤ 2 := by
  rcases h with rfl | rfl | rfl
  · rw [Finset.insert_eq_of_mem (by simp)]; exact Finset.card_le_two
  · rw [Finset.insert_eq_of_mem (by simp)]; exact Finset.card_le_two
  · rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self b)]; exact Finset.card_le_two

lemma labels_ne {lab : Fin m → Fin m} {i j k u v z : Fin m} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hT : ({lab u, lab v, lab z} : Finset (Fin m)) = {i, j, k}) :
    lab u ≠ lab v ∧ lab u ≠ lab z ∧ lab v ≠ lab z := by
  have hc : ({lab u, lab v, lab z} : Finset (Fin m)).card = 3 := by
    rw [hT]; exact card3 hij hik hjk
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  · have := card_le_two_of_eq (a := lab u) (b := lab v) (c := lab z) (by tauto)
    omega

lemma eq_z_of_mem {lab : Fin m → Fin m} {i j k u v z c : Fin m} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hT : ({lab u, lab v, lab z} : Finset (Fin m)) = {i, j, k})
    (hc : c = u ∨ c = v ∨ c = z) : c = z ↔ lab z = lab c := by
  obtain ⟨h1, h2, h3⟩ := labels_ne hij hik hjk hT
  constructor
  · rintro rfl; rfl
  · intro h
    rcases hc with rfl | rfl | rfl
    · exact absurd h.symm h2
    · exact absurd h.symm h3
    · rfl

lemma image3 (lab : Fin m → Fin m) (u v z : Fin m) :
    ({u, v, z} : Finset (Fin m)).image lab = {lab u, lab v, lab z} := by
  simp [Finset.image_insert]

lemma exists_of_label {lab : Fin m → Fin m} {u v z i' : Fin m} {S : Finset (Fin m)}
    (hT : ({lab u, lab v, lab z} : Finset (Fin m)) = S) (hi : i' ∈ S) :
    ∃ a, (a = u ∨ a = v ∨ a = z) ∧ lab a = i' := by
  rw [← hT, ← image3] at hi
  obtain ⟨a, ha, hla⟩ := Finset.mem_image.mp hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  exact ⟨a, ha, hla⟩

/-- With the pattern "blocks `i, j, k` choose the `jk` pair", `q` excludes the `i`-vertex of
a transversal triple. -/
lemma ex_pattern_iff {q : TCM m} {lab : Fin m → Fin m} {i j k : Fin m} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k)
    (hpat : ∀ a b c, lab a = i → lab b = j → lab c = k → ex q a b c = a)
    {u v z : Fin m} (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    (hT : ({lab u, lab v, lab z} : Finset (Fin m)) = {i, j, k}) :
    ex q u v z = z ↔ lab z = i := by
  obtain ⟨a, ha, hla⟩ := exists_of_label hT (by simp : i ∈ ({i, j, k} : Finset (Fin m)))
  obtain ⟨b, hb, hlb⟩ := exists_of_label hT (by simp : j ∈ ({i, j, k} : Finset (Fin m)))
  obtain ⟨c, hc, hlc⟩ := exists_of_label hT (by simp : k ∈ ({i, j, k} : Finset (Fin m)))
  have hab : a ≠ b := fun h => hij (hla.symm.trans (h ▸ hlb))
  have hac : a ≠ c := fun h => hik (hla.symm.trans (h ▸ hlc))
  have hbc : b ≠ c := fun h => hjk (hlb.symm.trans (h ▸ hlc))
  let t : Triple m := ⟨{u, v, z}, card3 huv huz hvz⟩
  have mem : ∀ d, (d = u ∨ d = v ∨ d = z) → d ∈ t.1 := by
    intro d hd; simp only [t, Finset.mem_insert, Finset.mem_singleton]; exact hd
  have teq := triple_eq t (mem a ha) (mem b hb) (mem c hc) hab hac hbc
  have e : ex q u v z = a := by
    rw [ex_of_eq q t rfl, ← ex_of_eq q t teq, hpat a b c hla hlb hlc]
  rw [e, eq_z_of_mem hij hik hjk hT ha, hla]

/-! ### The switch -/

lemma exists_lab_k {lab : Fin m → Fin m} {i j k : Fin m} {s : Finset (Fin m)}
    (h : s.image lab = {i, j, k}) : ∃ a ∈ s, lab a = k :=
  Finset.mem_image.mp (by rw [h]; simp)

/-- Switch every triple meeting blocks `i, j, k` once each to exclude its `k`-vertex. -/
noncomputable def switch (q : TCM m) (lab : Fin m → Fin m) (i j k : Fin m) : TCM m := fun t =>
  if h : t.1.image lab = {i, j, k} then
    ⟨(exists_lab_k h).choose, (exists_lab_k h).choose_spec.1⟩
  else q t

lemma ex_switch_iff (q : TCM m) (lab : Fin m → Fin m) {i j k : Fin m} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) {u v z : Fin m} (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z) :
    ex (switch q lab i j k) u v z = z ↔
      (if ({lab u, lab v, lab z} : Finset (Fin m)) = {i, j, k} then lab z = k
        else ex q u v z = z) := by
  have h3 := card3 huv huz hvz
  have hq : ex q u v z = (q ⟨_, h3⟩).1 := ex_of_eq q ⟨_, h3⟩ rfl
  have hs : ex (switch q lab i j k) u v z = (switch q lab i j k ⟨_, h3⟩).1 :=
    ex_of_eq _ ⟨_, h3⟩ rfl
  rw [hs]
  by_cases hT : ({lab u, lab v, lab z} : Finset (Fin m)) = {i, j, k}
  · have himg : ({u, v, z} : Finset (Fin m)).image lab = {i, j, k} := by rw [image3, hT]
    simp only [hT, ↓reduceIte]
    have hval : (switch q lab i j k ⟨_, h3⟩).1 = (exists_lab_k himg).choose := by
      unfold switch; simp only [himg, ↓reduceDIte]
    rw [hval]
    have hspec := (exists_lab_k himg).choose_spec
    generalize (exists_lab_k himg).choose = c at hspec ⊢
    obtain ⟨hmem, hlab⟩ := hspec
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    exact (eq_z_of_mem hij hik hjk hT hmem).trans (by rw [hlab])
  · have himg : ¬ ({u, v, z} : Finset (Fin m)).image lab = {i, j, k} := by rw [image3]; exact hT
    simp only [hT, ↓reduceIte]
    have hval : (switch q lab i j k ⟨_, h3⟩).1 = (q ⟨_, h3⟩).1 := by
      unfold switch; simp only [himg, ↓reduceDIte]
    rw [hval, ← hq]

end PSY
```

### `TCMLemma1.lean`

```lean
import TCMSwitch

/-!
# Lemma 1: the maximal-score pair of blocks has closed union

Loads under the switch, the exact gain `F(switch) − F(q)`, the score inequality, and the
closure of the union of a maximal-score pair of blocks for a maximizer `q`.
-/

namespace PSY

variable {m : ℕ}

lemma perm_j {i j k a b c : Fin m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ha : a = i ∨ a = j ∨ a = k) (hb : b = i ∨ b = j ∨ b = k) (hc : c = i ∨ c = j ∨ c = k)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h1 : ¬ (a = i ∧ b = j)) (h2 : ¬ (a = j ∧ b = i))
    (h3 : ¬ (a = j ∧ b = k)) (h4 : ¬ (a = k ∧ b = j)) : c = j := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> simp_all

lemma mem3 {lab : Fin m → Fin m} {i j k u v z : Fin m}
    (hT : ({lab u, lab v, lab z} : Finset (Fin m)) = {i, j, k}) :
    (lab u = i ∨ lab u = j ∨ lab u = k) ∧ (lab v = i ∨ lab v = j ∨ lab v = k) ∧
      (lab z = i ∨ lab z = j ∨ lab z = k) := by
  have hu : lab u ∈ ({i, j, k} : Finset (Fin m)) := hT ▸ by simp
  have hv : lab v ∈ ({i, j, k} : Finset (Fin m)) := hT ▸ by simp
  have hz : lab z ∈ ({i, j, k} : Finset (Fin m)) := hT ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hz
  exact ⟨hu, hv, hz⟩

section switchLoads

variable (q : TCM m) (lab : Fin m → Fin m) {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k)
  (hjk : j ≠ k) (hpat : ∀ a b c, lab a = i → lab b = j → lab c = k → ex q a b c = a)
include hij hik hjk hpat

lemma mult_sw_ij {x y : Fin m} (hx : lab x = i) (hy : lab y = j) :
    mult (switch q lab i j k) x y = mult q x y + (blk lab k).card := by
  have hxy : x ≠ y := fun h => hij (hx.symm.trans ((congrArg lab h).trans hy))
  have tr : ∀ z, ({lab x, lab y, lab z} : Finset (Fin m)) = {i, j, k} ↔ lab z = k := by
    intro z; rw [hx, hy]
    constructor
    · intro h
      have : k ∈ ({i, j, lab z} : Finset (Fin m)) := h ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h' | h'
      · exact absurd h'.symm hik
      · exact absurd h'.symm hjk
      · exact h'.symm
    · intro h; rw [h]
  rw [mult_eq _ hxy, mult_eq _ hxy,
    card_split_U (blk lab k) (fun z => z ≠ x ∧ z ≠ y ∧ ex (switch q lab i j k) x y z = z),
    card_split_U (blk lab k) (fun z => z ≠ x ∧ z ≠ y ∧ ex q x y z = z)]
  have e1 : (blk lab k).filter (fun z => z ≠ x ∧ z ≠ y ∧ ex (switch q lab i j k) x y z = z) =
      blk lab k := by
    apply Finset.filter_true_of_mem
    intro z hz
    rw [mem_blk] at hz
    have hzx : z ≠ x := fun h => hik ((hx.symm.trans (congrArg lab h).symm).trans hz)
    have hzy : z ≠ y := fun h => hjk ((hy.symm.trans (congrArg lab h).symm).trans hz)
    refine ⟨hzx, hzy, ?_⟩
    rw [ex_switch_iff q lab hij hik hjk hxy (Ne.symm hzx) (Ne.symm hzy),
      ite_pos' ((tr z).mpr hz)]
    exact hz
  have e2 : (blk lab k).filter (fun z => z ≠ x ∧ z ≠ y ∧ ex q x y z = z) = ∅ := by
    apply Finset.filter_false_of_mem
    intro z hz ⟨hzx, hzy, he⟩
    rw [mem_blk] at hz
    have := (ex_pattern_iff hij hik hjk hpat hxy (Ne.symm hzx) (Ne.symm hzy)
      ((tr z).mpr hz)).mp he
    exact hik (this.symm.trans hz)
  have e3 : Finset.univ.filter (fun z => z ∉ blk lab k ∧
        (z ≠ x ∧ z ≠ y ∧ ex (switch q lab i j k) x y z = z)) =
      Finset.univ.filter (fun z => z ∉ blk lab k ∧ (z ≠ x ∧ z ≠ y ∧ ex q x y z = z)) := by
    apply Finset.filter_congr
    intro z _
    constructor
    · rintro ⟨hz, hzx, hzy, he⟩
      refine ⟨hz, hzx, hzy, ?_⟩
      rw [mem_blk] at hz
      rwa [ex_switch_iff q lab hij hik hjk hxy (Ne.symm hzx) (Ne.symm hzy),
        ite_neg' (fun h => hz ((tr z).mp h))] at he
    · rintro ⟨hz, hzx, hzy, he⟩
      refine ⟨hz, hzx, hzy, ?_⟩
      rw [mem_blk] at hz
      rwa [ex_switch_iff q lab hij hik hjk hxy (Ne.symm hzx) (Ne.symm hzy),
        ite_neg' (fun h => hz ((tr z).mp h))]
  rw [e1, e2, e3]
  simp only [Finset.card_empty, zero_add]
  omega

lemma mult_sw_jk {y z : Fin m} (hy : lab y = j) (hz : lab z = k) :
    mult q y z = mult (switch q lab i j k) y z + (blk lab i).card := by
  have hyz : y ≠ z := fun h => hjk (hy.symm.trans ((congrArg lab h).trans hz))
  have tr : ∀ x, ({lab y, lab z, lab x} : Finset (Fin m)) = {i, j, k} ↔ lab x = i := by
    intro x; rw [hy, hz]
    constructor
    · intro h
      have : i ∈ ({j, k, lab x} : Finset (Fin m)) := h ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h' | h'
      · exact absurd h' hij
      · exact absurd h' hik
      · exact h'.symm
    · intro h; rw [h]; ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [mult_eq _ hyz, mult_eq _ hyz,
    card_split_U (blk lab i) (fun x => x ≠ y ∧ x ≠ z ∧ ex q y z x = x),
    card_split_U (blk lab i) (fun x => x ≠ y ∧ x ≠ z ∧ ex (switch q lab i j k) y z x = x)]
  have e1 : (blk lab i).filter (fun x => x ≠ y ∧ x ≠ z ∧ ex q y z x = x) = blk lab i := by
    apply Finset.filter_true_of_mem
    intro x hx
    rw [mem_blk] at hx
    have hxy : x ≠ y := fun h => hij ((hx.symm.trans (congrArg lab h)).trans hy)
    have hxz : x ≠ z := fun h => hik ((hx.symm.trans (congrArg lab h)).trans hz)
    exact ⟨hxy, hxz, (ex_pattern_iff hij hik hjk hpat hyz (Ne.symm hxy) (Ne.symm hxz)
      ((tr x).mpr hx)).mpr hx⟩
  have e2 : (blk lab i).filter
      (fun x => x ≠ y ∧ x ≠ z ∧ ex (switch q lab i j k) y z x = x) = ∅ := by
    apply Finset.filter_false_of_mem
    intro x hx ⟨hxy, hxz, he⟩
    rw [mem_blk] at hx
    rw [ex_switch_iff q lab hij hik hjk hyz (Ne.symm hxy) (Ne.symm hxz),
      ite_pos' ((tr x).mpr hx)] at he
    exact hik (hx.symm.trans he)
  have e3 : Finset.univ.filter (fun x => x ∉ blk lab i ∧ (x ≠ y ∧ x ≠ z ∧ ex q y z x = x)) =
      Finset.univ.filter (fun x => x ∉ blk lab i ∧
        (x ≠ y ∧ x ≠ z ∧ ex (switch q lab i j k) y z x = x)) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨hx, hxy, hxz, he⟩
      refine ⟨hx, hxy, hxz, ?_⟩
      rw [mem_blk] at hx
      rwa [ex_switch_iff q lab hij hik hjk hyz (Ne.symm hxy) (Ne.symm hxz),
        ite_neg' (fun h => hx ((tr x).mp h))]
    · rintro ⟨hx, hxy, hxz, he⟩
      refine ⟨hx, hxy, hxz, ?_⟩
      rw [mem_blk] at hx
      rwa [ex_switch_iff q lab hij hik hjk hyz (Ne.symm hxy) (Ne.symm hxz),
        ite_neg' (fun h => hx ((tr x).mp h))] at he
  rw [e1, e2, e3]
  simp only [Finset.card_empty, zero_add]
  omega

lemma mult_sw_other {u v : Fin m} (huv : u ≠ v) (h1 : ¬ (lab u = i ∧ lab v = j))
    (h2 : ¬ (lab u = j ∧ lab v = i)) (h3 : ¬ (lab u = j ∧ lab v = k))
    (h4 : ¬ (lab u = k ∧ lab v = j)) :
    mult (switch q lab i j k) u v = mult q u v := by
  rw [mult_eq _ huv, mult_eq _ huv]
  congr 1
  apply Finset.filter_congr
  intro z _
  by_cases hzu : z = u
  · simp [hzu]
  by_cases hzv : z = v
  · simp [hzv]
  simp only [ne_eq, hzu, hzv, not_false_eq_true, true_and]
  rw [ex_switch_iff q lab hij hik hjk huv (Ne.symm hzu) (Ne.symm hzv)]
  split_ifs with hT
  · obtain ⟨n1, n2, n3⟩ := labels_ne hij hik hjk hT
    obtain ⟨mu, mv, mz⟩ := mem3 hT
    have hzj := perm_j hij hik hjk mu mv mz n1 n2 n3 h1 h2 h3 h4
    constructor
    · intro h; exact absurd (hzj.symm.trans h) hjk
    · intro h
      have := (ex_pattern_iff hij hik hjk hpat huv (Ne.symm hzu) (Ne.symm hzv) hT).mp h
      exact absurd (hzj.symm.trans this) (Ne.symm hij)
  · exact Iff.rfl

end switchLoads

/-! ### The exact gain of the switch -/

lemma sum_ind (lab : Fin m → Fin m) (i j : Fin m) (d : ℝ) :
    ∑ x, ∑ y, (if lab x = i ∧ lab y = j then d else 0) =
      ((blk lab i).card : ℝ) * (blk lab j).card * d := by
  have h1 : ∀ x, ∑ y, (if lab x = i ∧ lab y = j then d else 0) =
      if lab x = i then ((blk lab j).card : ℝ) * d else 0 := by
    intro x
    by_cases hx : lab x = i
    · simp only [hx, true_and, ↓reduceIte]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      rfl
    · simp [hx]
  simp only [h1]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  simp only [blk]; ring

theorem switch_gain (q : TCM m) (lab : Fin m → Fin m) (hg : Good q lab) {i j k : Fin m}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpat : ∀ a b c, lab a = i → lab b = j → lab c = k → ex q a b c = a)
    {x₀ y₀ z₀ : Fin m} (hx₀ : lab x₀ = i) (hy₀ : lab y₀ = j) (hz₀ : lab z₀ = k) (α : ℝ) :
    F (switch q lab i j k) α = F q α + 2 * (((blk lab i).card : ℝ) * (blk lab j).card *
      (α ^ (mult q x₀ y₀ + (blk lab k).card) - α ^ mult q x₀ y₀) +
      ((blk lab j).card : ℝ) * (blk lab k).card * (α ^ mult (switch q lab i j k) y₀ z₀ -
        α ^ (mult (switch q lab i j k) y₀ z₀ + (blk lab i).card))) := by
  set L := mult q x₀ y₀ with hLdef
  set K := mult (switch q lab i j k) y₀ z₀ with hKdef
  set d1 : ℝ := α ^ (L + (blk lab k).card) - α ^ L with hd1
  set d2 : ℝ := α ^ K - α ^ (K + (blk lab i).card) with hd2
  have hL : ∀ x y, lab x = i → lab y = j → mult q x y = L := fun x y hx hy =>
    mult_uniform hg (hx.trans hx₀.symm) (hy.trans hy₀.symm) (by rw [hx, hy]; exact hij)
  have hK : ∀ y z, lab y = j → lab z = k → mult (switch q lab i j k) y z = K := by
    intro y z hy hz
    have e1 := mult_sw_jk q lab hij hik hjk hpat hy hz
    have e2 := mult_sw_jk q lab hij hik hjk hpat hy₀ hz₀
    have e3 : mult q y z = mult q y₀ z₀ :=
      mult_uniform hg (hy.trans hy₀.symm) (hz.trans hz₀.symm) (by rw [hy, hz]; exact hjk)
    omega
  have pw : ∀ x y, (if x = y then 0 else α ^ mult (switch q lab i j k) x y) =
      (if x = y then 0 else α ^ mult q x y) + (if lab x = i ∧ lab y = j then d1 else 0) +
      (if lab x = j ∧ lab y = i then d1 else 0) + (if lab x = j ∧ lab y = k then d2 else 0) +
      (if lab x = k ∧ lab y = j then d2 else 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      have n1 : ¬ (lab x = i ∧ lab x = j) := fun h => hij (h.1.symm.trans h.2)
      have n2 : ¬ (lab x = j ∧ lab x = i) := fun h => hij (h.2.symm.trans h.1)
      have n3 : ¬ (lab x = j ∧ lab x = k) := fun h => hjk (h.1.symm.trans h.2)
      have n4 : ¬ (lab x = k ∧ lab x = j) := fun h => hjk (h.2.symm.trans h.1)
      rw [ite_pos' rfl, ite_pos' rfl, ite_neg' n1, ite_neg' n2, ite_neg' n3, ite_neg' n4]
      ring
    rw [ite_neg' hxy, ite_neg' hxy]
    by_cases c1 : lab x = i ∧ lab y = j
    · have n2 : ¬ (lab x = j ∧ lab y = i) := fun h => hij (c1.1.symm.trans h.1)
      have n3 : ¬ (lab x = j ∧ lab y = k) := fun h => hij (c1.1.symm.trans h.1)
      have n4 : ¬ (lab x = k ∧ lab y = j) := fun h => hik (c1.1.symm.trans h.1)
      rw [ite_pos' c1, ite_neg' n2, ite_neg' n3, ite_neg' n4,
        mult_sw_ij q lab hij hik hjk hpat c1.1 c1.2, hL x y c1.1 c1.2]
      ring
    by_cases c2 : lab x = j ∧ lab y = i
    · have n3 : ¬ (lab x = j ∧ lab y = k) := fun h => hik (c2.2.symm.trans h.2)
      have n4 : ¬ (lab x = k ∧ lab y = j) := fun h => hjk (c2.1.symm.trans h.1)
      rw [ite_neg' c1, ite_pos' c2, ite_neg' n3, ite_neg' n4, mult_comm (switch q lab i j k) x y,
        mult_comm q x y, mult_sw_ij q lab hij hik hjk hpat c2.2 c2.1, hL y x c2.2 c2.1]
      ring
    by_cases c3 : lab x = j ∧ lab y = k
    · have n4 : ¬ (lab x = k ∧ lab y = j) := fun h => hjk (c3.1.symm.trans h.1)
      rw [ite_neg' c1, ite_neg' c2, ite_pos' c3, ite_neg' n4,
        mult_sw_jk q lab hij hik hjk hpat c3.1 c3.2, hK x y c3.1 c3.2]
      ring
    by_cases c4 : lab x = k ∧ lab y = j
    · rw [ite_neg' c1, ite_neg' c2, ite_neg' c3, ite_pos' c4, mult_comm (switch q lab i j k) x y,
        mult_comm q x y, mult_sw_jk q lab hij hik hjk hpat c4.2 c4.1, hK y x c4.2 c4.1]
      ring
    rw [ite_neg' c1, ite_neg' c2, ite_neg' c3, ite_neg' c4,
      mult_sw_other q lab hij hik hjk hpat hxy c1 c2 c3 c4]
    ring
  unfold F
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => pw x y))]
  simp only [Finset.sum_add_distrib, sum_ind]
  ring

/-! ### Scores and the closure of the best pair -/

/-- Size-normalized score of the pair of blocks containing `x` and `y`. -/
noncomputable def score (q : TCM m) (lab : Fin m → Fin m) (α : ℝ) (x y : Fin m) : ℝ :=
  ((blk lab (lab x)).card : ℝ) * (blk lab (lab y)).card * α ^ mult q x y /
    ((α ^ (blk lab (lab x)).card - 1) * (α ^ (blk lab (lab y)).card - 1))

lemma score_comm (q : TCM m) (lab : Fin m → Fin m) (α : ℝ) (x y : Fin m) :
    score q lab α x y = score q lab α y x := by
  unfold score; rw [mult_comm]; ring

lemma score_congr {q : TCM m} {lab : Fin m → Fin m} (hg : Good q lab) (α : ℝ)
    {x x' y y' : Fin m} (hx : lab x = lab x') (hy : lab y = lab y') (hxy : lab x ≠ lab y) :
    score q lab α x y = score q lab α x' y' := by
  unfold score; rw [hx, hy, mult_uniform hg hx hy hxy]

/-- The gain is positive when the score of `AB` is at least that of `BC`. -/
lemma delta_pos {α : ℝ} (hα : 1 < α) {a b c L K : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : (b : ℝ) * c * α ^ (K + a) / ((α ^ b - 1) * (α ^ c - 1)) ≤
      (a : ℝ) * b * α ^ L / ((α ^ a - 1) * (α ^ b - 1))) :
    0 < (a : ℝ) * b * (α ^ (L + c) - α ^ L) + b * c * (α ^ K - α ^ (K + a)) := by
  have hP : 0 < α ^ a - 1 := by have := one_lt_pow₀ hα ha.ne'; linarith
  have hQ : 0 < α ^ b - 1 := by have := one_lt_pow₀ hα hb.ne'; linarith
  have hR : 0 < α ^ c - 1 := by have := one_lt_pow₀ hα hc.ne'; linarith
  rw [div_le_div_iff₀ (mul_pos hQ hR) (mul_pos hP hQ)] at hs
  have hs' : (b : ℝ) * c * α ^ (K + a) * (α ^ a - 1) ≤ a * b * α ^ L * (α ^ c - 1) := by
    refine le_of_mul_le_mul_right ?_ hQ
    calc (b : ℝ) * c * α ^ (K + a) * (α ^ a - 1) * (α ^ b - 1)
        = b * c * α ^ (K + a) * ((α ^ a - 1) * (α ^ b - 1)) := by ring
      _ ≤ a * b * α ^ L * ((α ^ b - 1) * (α ^ c - 1)) := hs
      _ = a * b * α ^ L * (α ^ c - 1) * (α ^ b - 1) := by ring
  have e1 : α ^ (L + c) - α ^ L = α ^ L * (α ^ c - 1) := by rw [pow_add]; ring
  have e2 : α ^ K - α ^ (K + a) = -(α ^ K * (α ^ a - 1)) := by rw [pow_add]; ring
  have hK : α ^ K < α ^ (K + a) := pow_lt_pow_right₀ hα (by omega)
  have hbc : (0 : ℝ) < b * c := by positivity
  have h3 : (b : ℝ) * c * α ^ K * (α ^ a - 1) < b * c * α ^ (K + a) * (α ^ a - 1) := by
    apply mul_lt_mul_of_pos_right _ hP
    exact mul_lt_mul_of_pos_left hK hbc
  rw [e1, e2]
  nlinarith [hs', h3]

lemma blk_card_pos {lab : Fin m → Fin m} (x : Fin m) : 0 < (blk lab (lab x)).card :=
  Finset.card_pos.mpr ⟨x, mem_blk.mpr rfl⟩

/-- Core of Lemma 1: for a maximizer, a block triangle choosing `BC` against a better-scoring
`AB` is impossible. -/
theorem no_bad_triangle (q : TCM m) (lab : Fin m → Fin m) (hg : Good q lab) {α : ℝ}
    (hα : 1 < α) (hmax : ∀ r : TCM m, w r α ≤ w q α) {x y z : Fin m} (hxy : lab x ≠ lab y)
    (hxz : lab x ≠ lab z) (hyz : lab y ≠ lab z) (hex : ex q x y z = x)
    (hs : score q lab α y z ≤ score q lab α x y) : False := by
  have hpat : ∀ a b c, lab a = lab x → lab b = lab y → lab c = lab z → ex q a b c = a :=
    fun a b c ha hb hc => triangle_uniform hg hxy hxz hyz hex ha hb hc
  have hgain := switch_gain q lab hg hxy hxz hyz hpat (x₀ := x) (y₀ := y) (z₀ := z) rfl rfl rfl α
  have hle : F (switch q lab (lab x) (lab y) (lab z)) α ≤ F q α := by
    rw [← two_mul_w, ← two_mul_w]; linarith [hmax (switch q lab (lab x) (lab y) (lab z))]
  have hyz' := mult_sw_jk q lab hxy hxz hyz hpat (y := y) (z := z) rfl rfl
  unfold score at hs
  rw [hyz'] at hs
  have hd := delta_pos hα (blk_card_pos x) (blk_card_pos y) (blk_card_pos z) hs
  linarith

/-- Lemma 1: the union of a maximal-score pair of blocks is closed. -/
theorem union_closed (q : TCM m) (lab : Fin m → Fin m) (hg : Good q lab) {α : ℝ}
    (hα : 1 < α) (hmax : ∀ r : TCM m, w r α ≤ w q α) {x₀ y₀ : Fin m} (hne : lab x₀ ≠ lab y₀)
    (hbest : ∀ x y, lab x ≠ lab y → score q lab α x y ≤ score q lab α x₀ y₀) :
    Closed q (blk lab (lab x₀) ∪ blk lab (lab y₀)) := by
  have key : ∀ x y z, lab x = lab x₀ → lab y = lab y₀ → lab z ≠ lab x₀ → lab z ≠ lab y₀ →
      ex q x y z = z := by
    intro x y z hx hy hzx hzy
    have hxy' : lab x ≠ lab y := by rw [hx, hy]; exact hne
    have hxz' : lab x ≠ lab z := by rw [hx]; exact Ne.symm hzx
    have hyz' : lab y ≠ lab z := by rw [hy]; exact Ne.symm hzy
    have dxy : x ≠ y := fun h => hxy' (congrArg lab h)
    have dxz : x ≠ z := fun h => hxz' (congrArg lab h)
    have dyz : y ≠ z := fun h => hyz' (congrArg lab h)
    have sxy : score q lab α x y = score q lab α x₀ y₀ := score_congr hg α hx hy hxy'
    rcases ex_mem q dxy dxz dyz with h | h | h
    · exact (no_bad_triangle q lab hg hα hmax hxy' hxz' hyz' h
        (by rw [sxy]; exact hbest y z hyz')).elim
    · have h' : ex q y x z = y := by rw [← ex_comm12]; exact h
      refine (no_bad_triangle q lab hg hα hmax (Ne.symm hxy') hyz' hxz' h' ?_).elim
      rw [score_comm q lab α y x, sxy]; exact hbest x z hxz'
    · exact h
  intro x y z hx hy hxy hz
  have hzx : lab z ≠ lab x₀ := fun h => hz (Finset.mem_union_left _ (mem_blk.mpr h))
  have hzy : lab z ≠ lab y₀ := fun h => hz (Finset.mem_union_right _ (mem_blk.mpr h))
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact (hg (lab x₀)).1 x y z hx hy hxy (fun h => hzx (mem_blk.mp h))
  · exact key x y z (mem_blk.mp hx) (mem_blk.mp hy) hzx hzy
  · rw [ex_comm12]; exact key y x z (mem_blk.mp hy) (mem_blk.mp hx) hzx hzy
  · exact (hg (lab y₀)).1 x y z hx hy hxy (fun h => hzy (mem_blk.mp h))

/-- Lemma 1 (existence form). -/
theorem exists_closed_pair (q : TCM m) (lab : Fin m → Fin m) (hg : Good q lab) {α : ℝ}
    (hα : 1 < α) (hmax : ∀ r : TCM m, w r α ≤ w q α) (h2 : ∃ x y, lab x ≠ lab y) :
    ∃ x₀ y₀, lab x₀ ≠ lab y₀ ∧ Closed q (blk lab (lab x₀) ∪ blk lab (lab y₀)) := by
  obtain ⟨x, y, hxy⟩ := h2
  set P := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => lab p.1 ≠ lab p.2) with hP
  have hPne : P.Nonempty := ⟨(x, y), by simp [P, hxy]⟩
  obtain ⟨p, hp, hmaxp⟩ := Finset.exists_max_image P (fun p => score q lab α p.1 p.2) hPne
  have hp' : lab p.1 ≠ lab p.2 := (Finset.mem_filter.mp hp).2
  refine ⟨p.1, p.2, hp', union_closed q lab hg hα hmax hp' ?_⟩
  intro x y hxy
  exact hmaxp (x, y) (by simp [P, hxy])

end PSY
```

### `TCMMain.lean`

```lean
import TCMLemma1

/-!
# Assembly: some maximizer is 2-recursive, hence `H(m, α) = H₂(m, α)`

Start from a global maximizer and the singleton labelling `id`; while two blocks remain,
Lemma 1 gives a pair with closed union, and Lemma 2 merges it (through a clone that is again a
maximizer).  The number of labels strictly decreases.
-/

namespace PSY

variable {m : ℕ}

/-- Singleton blocks form a good labelling for every TCM. -/
theorem good_id (q : TCM m) : Good q id := by
  intro i
  have hb : blk id i = {i} := by ext v; simp [blk]
  rw [hb]
  refine ⟨?_, ?_, TwoRec.small (by simp)⟩
  · intro x y z hx hy hxy _
    rw [Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  · intro x x' z w hx hx' _ _ _
    rw [Finset.mem_singleton] at hx hx'
    rw [hx, hx']

/-- The merging iteration, by induction on the number of labels. -/
theorem descent {α : ℝ} (hα : 1 < α) : ∀ n : ℕ, ∀ (q : TCM m) (lab : Fin m → Fin m),
    (∀ r : TCM m, w r α ≤ w q α) → Good q lab → (Finset.univ.image lab).card ≤ n →
    ∃ r : TCM m, (∀ r' : TCM m, w r' α ≤ w r α) ∧ TwoRec r Finset.univ := by
  intro n
  induction n with
  | zero =>
    intro q lab hmax _ hc
    refine ⟨q, hmax, TwoRec.small ?_⟩
    have h1 : Finset.univ.image lab = ∅ := Finset.card_eq_zero.mp (by omega)
    have h2 : (Finset.univ : Finset (Fin m)) = ∅ := Finset.image_eq_empty.mp h1
    rw [h2]; simp
  | succ n ih =>
    intro q lab hmax hg hc
    by_cases h2 : ∃ x y, lab x ≠ lab y
    · obtain ⟨x₀, y₀, hne, hcl⟩ := exists_closed_pair q lab hg hα hmax h2
      have hUne : (blk lab (lab x₀) ∪ blk lab (lab y₀)).Nonempty :=
        ⟨x₀, Finset.mem_union_left _ (mem_blk.mpr rfl)⟩
      obtain ⟨u, hu, hwu⟩ := exists_clone_ge q hcl hUne (by linarith : (0 : ℝ) < α)
      have hmax' : ∀ r, w r α ≤ w (clone q (blk lab (lab x₀) ∪ blk lab (lab y₀)) u) α :=
        fun r => (hmax r).trans hwu
      have hg' := good_merge q lab hg hne ⟨x₀, mem_blk.mpr rfl⟩ ⟨y₀, mem_blk.mpr rfl⟩ hcl hu
      have hc' := card_image_merge lab hne (Finset.mem_image_of_mem _ (Finset.mem_univ x₀))
        (Finset.mem_image_of_mem _ (Finset.mem_univ y₀))
      exact ih _ _ hmax' hg' (by omega)
    · push Not at h2
      refine ⟨q, hmax, ?_⟩
      by_cases hm : (Finset.univ : Finset (Fin m)).Nonempty
      · obtain ⟨x, _⟩ := hm
        have hb : blk lab (lab x) = Finset.univ := by
          ext v; simp [blk, h2 v x]
        rw [← hb]; exact (hg (lab x)).2.2
      · rw [Finset.not_nonempty_iff_eq_empty] at hm
        rw [hm]; exact TwoRec.small (by simp)

/-- Stronger form (all `α > 1`): every TCM is dominated by a 2-recursive TCM. -/
theorem recursive_dominates (α : ℝ) (hα : 1 < α) (q : TCM m) :
    ∃ r : TCM m, TwoRec r Finset.univ ∧ w q α ≤ w r α := by
  obtain ⟨q₀, _, hq₀⟩ :=
    Finset.exists_max_image Finset.univ (fun r : TCM m => w r α) Finset.univ_nonempty
  obtain ⟨r, hr, hrec⟩ := descent hα _ q₀ id (fun r => hq₀ r (Finset.mem_univ _))
    (good_id q₀) le_rfl
  exact ⟨r, hrec, hr q⟩

open Classical in
/-- `H(m, α) = H₂(m, α)` for every `m` and every `α > 1`. -/
theorem H_eq_H₂ (m : ℕ) (α : ℝ) (hα : 1 < α) : H m α = H₂ m α := by
  apply le_antisymm
  · unfold H
    apply Finset.sup'_le
    intro q _
    obtain ⟨r, hr, hqr⟩ := recursive_dominates α hα q
    unfold H₂
    exact hqr.trans (Finset.le_sup' (fun q => w q α)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩))
  · unfold H₂
    apply Finset.sup'_le
    intro q _
    unfold H
    exact Finset.le_sup' (fun q => w q α) (Finset.mem_univ q)

/-- **Peaslee–Sali–Yan, Conjecture 6.3** (main clause): `H(m, α) = H₂(m, α)` for all `m ≥ 3`
and `α ≥ 2`. -/
theorem psy_conj_6_3 (m : ℕ) (hm : 3 ≤ m) (α : ℝ) (hα : 2 ≤ α) : H m α = H₂ m α := by
  have _ := hm
  exact H_eq_H₂ m α (by linarith)

end PSY
```

### `TCMRecBound.lean`

```lean
import TCMBasic

/-!
# The H₂ recurrence as an upper bound (used only for the sanity values)

For a 2-recursive TCM on `S` with split `V₁ ⊔ V₂`, the ordered weight restricted to `S`
satisfies `W_S = α^{|V₂|} W_{V₁} + α^{|V₁|} W_{V₂} + 2|V₁||V₂|` (source, Lemma 5.1).  We only
need the resulting inequality `W_S ≤ 2 h(|S|)` for any `h` obeying the recurrence bound.
-/

namespace PSY

variable {m : ℕ}

/-- Multiplicity of `xy` counting only third vertices in `S`. -/
def multS (q : TCM m) (S : Finset (Fin m)) (x y : Fin m) : ℕ :=
  (S.filter (fun z => z ≠ x ∧ z ≠ y ∧ ex q x y z = z)).card

/-- Ordered weight restricted to `S`. -/
noncomputable def WS (q : TCM m) (S : Finset (Fin m)) (α : ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, if x = y then 0 else α ^ multS q S x y

lemma WS_univ (q : TCM m) (α : ℝ) : WS q Finset.univ α = F q α := by
  unfold WS F
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  by_cases h : x = y
  · simp [h]
  · simp only [h, ↓reduceIte, multS, mult_eq q h]

lemma sum_offdiag_one (S : Finset (Fin m)) :
    ∑ x ∈ S, ∑ y ∈ S, (if x = y then (0 : ℝ) else 1) = (S.card : ℝ) * (S.card - 1) := by
  have h1 : ∀ x ∈ S, ∑ y ∈ S, (if x = y then (0 : ℝ) else 1) = (S.card : ℝ) - 1 := by
    intro x hx
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
      mul_one]
    have : (S.filter (fun y => ¬ x = y)) = S.erase x := by
      ext y; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
    rw [this, Finset.card_erase_of_mem hx]
    have : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hx⟩
    push_cast [this]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]

lemma WS_small (q : TCM m) {S : Finset (Fin m)} (hS : S.card ≤ 2) (α : ℝ) :
    WS q S α = (S.card : ℝ) * (S.card - 1) := by
  rw [← sum_offdiag_one]
  unfold WS
  refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => ?_))
  by_cases h : x = y
  · simp [h]
  · simp only [h, ↓reduceIte]
    have : multS q S x y = 0 := by
      unfold multS
      rw [Finset.card_eq_zero]
      apply Finset.filter_false_of_mem
      intro z hz ⟨hzx, hzy, _⟩
      have hsub : ({x, y, z} : Finset (Fin m)) ⊆ S := by
        intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      rw [card3 h (Ne.symm hzx) (Ne.symm hzy)] at this
      omega
    rw [this, pow_zero]

/-- Loads under a split. -/
lemma multS_split_in (q : TCM m) {S V₁ V₂ : Finset (Fin m)} (hd : Disjoint V₁ V₂)
    (hU : V₁ ∪ V₂ = S)
    (c1 : ∀ t : Triple m, t.1 ⊆ S → (t.1 ∩ V₁).card = 2 → (q t).1 ∈ V₂)
    {x y : Fin m} (hx : x ∈ V₁) (hy : y ∈ V₁) (hxy : x ≠ y) :
    multS q S x y = multS q V₁ x y + V₂.card := by
  unfold multS
  rw [← hU, Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hd)]
  congr 1
  congr 1
  apply Finset.filter_true_of_mem
  intro z hz
  have hzx : z ≠ x := fun h => Finset.disjoint_left.mp hd hx (h ▸ hz)
  have hzy : z ≠ y := fun h => Finset.disjoint_left.mp hd hy (h ▸ hz)
  refine ⟨hzx, hzy, ?_⟩
  let t : Triple m := ⟨{x, y, z}, card3 hxy (Ne.symm hzx) (Ne.symm hzy)⟩
  have hts : t.1 ⊆ S := by
    intro v hv; simp only [t, Finset.mem_insert, Finset.mem_singleton] at hv
    rw [← hU]; rcases hv with rfl | rfl | rfl
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_left _ hy
    · exact Finset.mem_union_right _ hz
  have hint : t.1 ∩ V₁ = {x, y} := by
    ext v; simp only [t, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hv⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hv (Finset.disjoint_right.mp hd hz)
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, hx⟩
      · exact ⟨Or.inr (Or.inl rfl), hy⟩
  have h2 : (t.1 ∩ V₁).card = 2 := by rw [hint]; exact Finset.card_pair hxy
  have hm := c1 t hts h2
  rw [← ex_of_eq q t rfl] at hm
  rcases ex_mem q hxy (Ne.symm hzx) (Ne.symm hzy) with e | e | e
  · rw [e] at hm; exact absurd hm (Finset.disjoint_left.mp hd hx)
  · rw [e] at hm; exact absurd hm (Finset.disjoint_left.mp hd hy)
  · exact e

lemma multS_split_cross (q : TCM m) {S V₁ V₂ : Finset (Fin m)} (hd : Disjoint V₁ V₂)
    (hU : V₁ ∪ V₂ = S)
    (c1 : ∀ t : Triple m, t.1 ⊆ S → (t.1 ∩ V₁).card = 2 → (q t).1 ∈ V₂)
    (c2 : ∀ t : Triple m, t.1 ⊆ S → (t.1 ∩ V₂).card = 2 → (q t).1 ∈ V₁)
    {x y : Fin m} (hx : x ∈ V₁) (hy : y ∈ V₂) : multS q S x y = 0 := by
  have hxy : x ≠ y := fun h => Finset.disjoint_left.mp hd hx (h ▸ hy)
  unfold multS
  rw [Finset.card_eq_zero]
  apply Finset.filter_false_of_mem
  intro z hz ⟨hzx, hzy, he⟩
  let t : Triple m := ⟨{x, y, z}, card3 hxy (Ne.symm hzx) (Ne.symm hzy)⟩
  have hts : t.1 ⊆ S := by
    intro v hv; simp only [t, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · rw [← hU]; exact Finset.mem_union_left _ hx
    · rw [← hU]; exact Finset.mem_union_right _ hy
    · exact hz
  have hzS : z ∈ V₁ ∪ V₂ := hU ▸ hz
  rcases Finset.mem_union.mp hzS with hz1 | hz2
  · have hint : t.1 ∩ V₁ = {x, z} := by
      ext v; simp only [t, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hv⟩
        · exact Or.inl rfl
        · exact absurd hy (Finset.disjoint_left.mp hd hv)
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, hx⟩
        · exact ⟨Or.inr (Or.inr rfl), hz1⟩
    have hm := c1 t hts (by rw [hint]; exact Finset.card_pair (Ne.symm hzx))
    rw [← ex_of_eq q t rfl, he] at hm
    exact Finset.disjoint_left.mp hd hz1 hm
  · have hint : t.1 ∩ V₂ = {y, z} := by
      ext v; simp only [t, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, hv⟩
        · exact absurd hv (Finset.disjoint_left.mp hd hx)
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨Or.inr (Or.inl rfl), hy⟩
        · exact ⟨Or.inr (Or.inr rfl), hz2⟩
    have hm := c2 t hts (by rw [hint]; exact Finset.card_pair (Ne.symm hzy))
    rw [← ex_of_eq q t rfl, he] at hm
    exact Finset.disjoint_right.mp hd hz2 hm

/-- Recurrence upper bound for the restricted ordered weight of a 2-recursive TCM. -/
theorem WS_le (q : TCM m) {α : ℝ} (hα : 0 ≤ α) (h : ℕ → ℝ)
    (hs : ∀ n : ℕ, n ≤ 2 → (n : ℝ) * (n - 1) ≤ 2 * h n)
    (hr : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a + b ≤ m → α ^ b * h a + α ^ a * h b + a * b ≤ h (a + b))
    {S : Finset (Fin m)} (hS : TwoRec q S) : WS q S α ≤ 2 * h S.card := by
  induction hS with
  | small hS => rw [WS_small q hS]; exact hs _ hS
  | @split S V₁ V₂ h1 h2 hd hU _ _ c1 c2 ih1 ih2 =>
    have hdS : Disjoint V₁ V₂ := hd
    have hsplit : WS q S α = α ^ V₂.card * WS q V₁ α + α ^ V₁.card * WS q V₂ α +
        2 * (V₁.card * V₂.card) := by
      have hc2 : ∀ x ∈ V₂, ∀ y ∈ V₁, multS q S x y = 0 := by
        intro x hx y hy; rw [multS, ← multS, show multS q S x y = multS q S y x from ?_]
        · exact multS_split_cross q hd hU c1 c2 hy hx
        · unfold multS; congr 1; apply Finset.filter_congr; intro z _
          rw [ex_comm12]; tauto
      have hU' : S = V₁ ∪ V₂ := hU.symm
      unfold WS
      rw [hU', Finset.sum_union hdS]
      simp only [Finset.sum_union hdS]
      rw [← hU']
      have e11 : ∑ x ∈ V₁, ∑ y ∈ V₁, (if x = y then 0 else α ^ multS q S x y) =
          α ^ V₂.card * ∑ x ∈ V₁, ∑ y ∈ V₁, (if x = y then 0 else α ^ multS q V₁ x y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y hy => ?_)
        by_cases hxy : x = y
        · simp [hxy]
        · simp only [hxy, ↓reduceIte, multS_split_in q hd hU c1 hx hy hxy, pow_add]; ring
      have e22 : ∑ x ∈ V₂, ∑ y ∈ V₂, (if x = y then 0 else α ^ multS q S x y) =
          α ^ V₁.card * ∑ x ∈ V₂, ∑ y ∈ V₂, (if x = y then 0 else α ^ multS q V₂ x y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y hy => ?_)
        by_cases hxy : x = y
        · simp [hxy]
        · have hU2 : V₂ ∪ V₁ = S := by rw [Finset.union_comm]; exact hU
          simp only [hxy, ↓reduceIte, multS_split_in q hd.symm hU2 c2 hx hy hxy, pow_add]
          ring
      have e12 : ∑ x ∈ V₁, ∑ y ∈ V₂, (if x = y then 0 else α ^ multS q S x y) =
          (V₁.card : ℝ) * V₂.card := by
        have : ∀ x ∈ V₁, ∑ y ∈ V₂, (if x = y then 0 else α ^ multS q S x y) = V₂.card := by
          intro x hx
          rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ))]
          · simp
          intro y hy
          have hxy : x ≠ y := fun h => Finset.disjoint_left.mp hd hx (h ▸ hy)
          simp [hxy, multS_split_cross q hd hU c1 c2 hx hy]
        rw [Finset.sum_congr rfl this]; simp
      have e21 : ∑ x ∈ V₂, ∑ y ∈ V₁, (if x = y then 0 else α ^ multS q S x y) =
          (V₂.card : ℝ) * V₁.card := by
        have : ∀ x ∈ V₂, ∑ y ∈ V₁, (if x = y then 0 else α ^ multS q S x y) = V₁.card := by
          intro x hx
          rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ))]
          · simp
          intro y hy
          have hxy : x ≠ y := fun h => Finset.disjoint_left.mp hd hy (h ▸ hx)
          simp [hxy, hc2 x hx y hy]
        rw [Finset.sum_congr rfl this]; simp
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e11, e22, e12, e21]; ring
    have hcard : S.card = V₁.card + V₂.card := by
      rw [← hU, Finset.card_union_of_disjoint hdS]
    have ha : 1 ≤ V₁.card := Finset.card_pos.mpr h1
    have hb : 1 ≤ V₂.card := Finset.card_pos.mpr h2
    have hm : V₁.card + V₂.card ≤ m := by
      rw [← hcard]; exact (Finset.card_le_univ S).trans (by simp)
    have hrec := hr _ _ ha hb hm
    rw [hsplit, hcard]
    have p1 : 0 ≤ α ^ V₂.card := pow_nonneg hα _
    have p2 : 0 ≤ α ^ V₁.card := pow_nonneg hα _
    have q1 := mul_le_mul_of_nonneg_left ih1 p1
    have q2 := mul_le_mul_of_nonneg_left ih2 p2
    nlinarith [q1, q2, hrec]

end PSY
```

### `TCMSanity.lean`

```lean
import TCMMain
import TCMRecBound
import Mathlib.Tactic.IntervalCases

/-!
# Sanity checks requested by the review

* `H(3,2) = H₂(3,2) = 4` (every TCM on 3 vertices has weight 4, by `decide`);
* `H(4,2) = H₂(4,2) = 12` (all 81 TCMs on 4 vertices by `decide`, independently of the main
  theorem, plus an explicit 2-recursive TCM);
* `H₂(5,2) = 30`, `H₂(6,2) = 73` (explicit 2-recursive TCMs and the recurrence upper bound);
* the cyclic TCM on 4 vertices is not 2-recursive, so `TwoRec` is not trivially true.
-/

namespace PSY

/-- Integer weight at `α = 2`. -/
def wN {m : ℕ} (q : TCM m) : ℕ :=
  ∑ e ∈ (Finset.univ : Finset (Fin m)).offDiag.filter (fun p => p.1 < p.2), 2 ^ mult q e.1 e.2

lemma w_two {m : ℕ} (q : TCM m) : w q 2 = (wN q : ℝ) := by
  unfold w wN; push_cast; rfl

/-! ### Explicit 2-recursive TCMs -/

/-- Least element of `s` (default `d`). -/
def pickMin {n : ℕ} (s : Finset (Fin n)) (d : Fin n) : Fin n :=
  if h : s.Nonempty then s.min' h else d

/-- Split at `k`: a triple meeting both sides excludes its lone vertex; a triple inside one
side excludes its least vertex. -/
def splitSel (n k : ℕ) [NeZero n] (s : Finset (Fin n)) : Fin n :=
  if (s.filter (fun v => v.val < k)).card = 1 then pickMin (s.filter (fun v => v.val < k)) 0
  else if (s.filter (fun v => k ≤ v.val)).card = 1 then
    pickMin (s.filter (fun v => k ≤ v.val)) 0
  else pickMin s 0

lemma sel4 : ∀ s : Finset (Fin 4), s.card = 3 → splitSel 4 2 s ∈ s := by decide
lemma sel5 : ∀ s : Finset (Fin 5), s.card = 3 → splitSel 5 2 s ∈ s := by decide
lemma sel6 : ∀ s : Finset (Fin 6), s.card = 3 → splitSel 6 3 s ∈ s := by decide

def tcm4 : TCM 4 := fun t => ⟨splitSel 4 2 t.1, sel4 t.1 t.2⟩
def tcm5 : TCM 5 := fun t => ⟨splitSel 5 2 t.1, sel5 t.1 t.2⟩
def tcm6 : TCM 6 := fun t => ⟨splitSel 6 3 t.1, sel6 t.1 t.2⟩

theorem tcm4_twoRec : TwoRec tcm4 Finset.univ :=
  TwoRec.split (V₁ := {0, 1}) (V₂ := {2, 3}) ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
    (by decide) (TwoRec.small (by decide)) (TwoRec.small (by decide)) (by decide) (by decide)

theorem tcm5_twoRec : TwoRec tcm5 Finset.univ :=
  TwoRec.split (V₁ := {0, 1}) (V₂ := {2, 3, 4}) ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
    (by decide) (TwoRec.small (by decide))
    (TwoRec.split (V₁ := {2}) (V₂ := {3, 4}) ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
      (by decide) (TwoRec.small (by decide)) (TwoRec.small (by decide)) (by decide)
      (by decide))
    (by decide) (by decide)

theorem tcm6_twoRec : TwoRec tcm6 Finset.univ :=
  TwoRec.split (V₁ := {0, 1, 2}) (V₂ := {3, 4, 5}) ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide)
    (by decide)
    (TwoRec.split (V₁ := {0}) (V₂ := {1, 2}) ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
      (by decide) (TwoRec.small (by decide)) (TwoRec.small (by decide)) (by decide)
      (by decide))
    (TwoRec.split (V₁ := {3}) (V₂ := {4, 5}) ⟨3, by decide⟩ ⟨4, by decide⟩ (by decide)
      (by decide) (TwoRec.small (by decide)) (TwoRec.small (by decide)) (by decide)
      (by decide))
    (by decide) (by decide)

lemma wN_tcm4 : wN tcm4 = 12 := by decide
lemma wN_tcm5 : wN tcm5 = 30 := by decide
lemma wN_tcm6 : wN tcm6 = 73 := by decide

/-! ### Exhaustive values for 3 and 4 vertices -/

lemma wN_all3 : ∀ q : TCM 3, wN q = 4 := by decide
lemma wN_all4 : ∀ q : TCM 4, wN q ≤ 12 := by decide

/-! ### Recurrence upper bound for `H₂` at `α = 2` -/

/-- The values `H₂(n, 2)` for `n ≤ 6` (source, Lemma 5.1 recurrence). -/
def hN : ℕ → ℕ
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 12 | 5 => 30 | 6 => 73 | _ => 0

lemma hN_rec : ∀ a < 7, ∀ b < 7, 1 ≤ a → 1 ≤ b → a + b ≤ 6 →
    2 ^ b * hN a + 2 ^ a * hN b + a * b ≤ hN (a + b) := by decide

open Classical in
theorem H₂_two_le {m : ℕ} (hm : m ≤ 6) : H₂ m 2 ≤ hN m := by
  unfold H₂
  apply Finset.sup'_le
  intro q hq
  have hr := (Finset.mem_filter.mp hq).2
  have hs : ∀ n : ℕ, n ≤ 2 → (n : ℝ) * (n - 1) ≤ 2 * (hN n : ℝ) := by
    intro n hn; interval_cases n <;> norm_num [hN]
  have hrr : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a + b ≤ m →
      (2 : ℝ) ^ b * (hN a : ℝ) + 2 ^ a * (hN b : ℝ) + a * b ≤ (hN (a + b) : ℝ) := by
    intro a b ha hb hab
    have := hN_rec a (by omega) b (by omega) ha hb (by omega)
    exact_mod_cast this
  have := WS_le q (α := 2) (by norm_num) (fun n => (hN n : ℝ)) hs hrr hr
  rw [WS_univ, ← two_mul_w, Finset.card_univ, Fintype.card_fin] at this
  linarith

open Classical in
theorem H₂_ge {m : ℕ} (q : TCM m) (hq : TwoRec q Finset.univ) (α : ℝ) : w q α ≤ H₂ m α := by
  unfold H₂
  exact Finset.le_sup' (fun q => w q α) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩)

theorem H_ge {m : ℕ} (q : TCM m) (α : ℝ) : w q α ≤ H m α :=
  Finset.le_sup' (fun q => w q α) (Finset.mem_univ q)

/-! ### The sanity values -/

theorem H_3_2 : H 3 2 = 4 := by
  apply le_antisymm
  · unfold H; apply Finset.sup'_le; intro q _; rw [w_two, wN_all3 q]; norm_num
  · have := H_ge (maxTCM 3) 2; rw [w_two, wN_all3] at this; exact_mod_cast this

theorem H₂_3_2 : H₂ 3 2 = 4 := by
  apply le_antisymm
  · have := H₂_two_le (m := 3) (by norm_num); simpa [hN] using this
  · have := H₂_ge (maxTCM 3) (maxTCM_twoRec 3 _) 2; rw [w_two, wN_all3] at this
    exact_mod_cast this

/-- `H(4,2) = 12`, by exhausting all 81 TCMs (independent of the main theorem). -/
theorem H_4_2 : H 4 2 = 12 := by
  apply le_antisymm
  · unfold H; apply Finset.sup'_le; intro q _; rw [w_two]; exact_mod_cast wN_all4 q
  · have := H_ge tcm4 2; rw [w_two, wN_tcm4] at this; exact_mod_cast this

theorem H₂_4_2 : H₂ 4 2 = 12 := by
  apply le_antisymm
  · have := H₂_two_le (m := 4) (by norm_num); simpa [hN] using this
  · have := H₂_ge tcm4 tcm4_twoRec 2; rw [w_two, wN_tcm4] at this; exact_mod_cast this

theorem H₂_5_2 : H₂ 5 2 = 30 := by
  apply le_antisymm
  · have := H₂_two_le (m := 5) (by norm_num); simpa [hN] using this
  · have := H₂_ge tcm5 tcm5_twoRec 2; rw [w_two, wN_tcm5] at this; exact_mod_cast this

theorem H₂_6_2 : H₂ 6 2 = 73 := by
  apply le_antisymm
  · have := H₂_two_le (m := 6) (by norm_num); simpa [hN] using this
  · have := H₂_ge tcm6 tcm6_twoRec 2; rw [w_two, wN_tcm6] at this; exact_mod_cast this

/-- Consequences of the main theorem. -/
theorem H_5_2 : H 5 2 = 30 := by rw [psy_conj_6_3 5 (by norm_num) 2 le_rfl, H₂_5_2]
theorem H_6_2 : H 6 2 = 73 := by rw [psy_conj_6_3 6 (by norm_num) 2 le_rfl, H₂_6_2]

/-! ### A TCM that is not 2-recursive -/

lemma cyc_aux0 : ∀ s : Finset (Fin 4), 0 ∉ s → s.card = 3 → 1 ∈ s := by decide
lemma cyc_aux1 : ∀ s : Finset (Fin 4), 1 ∉ s → s.card = 3 → 2 ∈ s := by decide
lemma cyc_aux2 : ∀ s : Finset (Fin 4), 2 ∉ s → s.card = 3 → 3 ∈ s := by decide

/-- The cyclic TCM on 4 vertices: the triple missing `k` excludes `k + 1 (mod 4)`. -/
def cyc4 : TCM 4 := fun t =>
  if h0 : (0 : Fin 4) ∉ t.1 then ⟨1, cyc_aux0 _ h0 t.2⟩
  else if h1 : (1 : Fin 4) ∉ t.1 then ⟨2, cyc_aux1 _ h1 t.2⟩
  else if h2 : (2 : Fin 4) ∉ t.1 then ⟨3, cyc_aux2 _ h2 t.2⟩
  else ⟨0, by simpa using h0⟩

lemma cyc4_split_fails : ∀ V₁ V₂ : Finset (Fin 4), V₁ ∪ V₂ = Finset.univ → V₁ ∩ V₂ = ∅ →
    (∀ t : Triple 4, (t.1 ∩ V₁).card = 2 → (cyc4 t).1 ∈ V₂) →
    (∀ t : Triple 4, (t.1 ∩ V₂).card = 2 → (cyc4 t).1 ∈ V₁) → V₁ = ∅ ∨ V₂ = ∅ := by
  decide

theorem cyc4_not_twoRec : ¬ TwoRec cyc4 Finset.univ := by
  intro h
  cases h with
  | small h => exact absurd h (by decide)
  | split h1 h2 hd hU _ _ c1 c2 =>
    rcases cyc4_split_fails _ _ hU (Finset.disjoint_iff_inter_eq_empty.mp hd)
      (fun t ht => c1 t (Finset.subset_univ _) ht)
      (fun t ht => c2 t (Finset.subset_univ _) ht) with h | h
    · exact Finset.nonempty_iff_ne_empty.mp h1 h
    · exact Finset.nonempty_iff_ne_empty.mp h2 h

theorem exists_not_twoRec : ∃ q : TCM 4, ¬ TwoRec q Finset.univ := ⟨cyc4, cyc4_not_twoRec⟩

end PSY
```

### `TCMEndpoint.lean`

```lean
import TCMSanity

/-!
# Endpoint report: statements, definitions and axioms
-/

#print PSY.Triple
#print PSY.TCM
#print PSY.mult
#print PSY.w
#print PSY.TwoRec
#print PSY.H
#print PSY.H₂
#check @PSY.twoRec_nonempty
#check @PSY.psy_conj_6_3
#check @PSY.recursive_dominates
#check @PSY.H_eq_H₂
#check @PSY.H_3_2
#check @PSY.H₂_3_2
#check @PSY.H_4_2
#check @PSY.H₂_4_2
#check @PSY.H₂_5_2
#check @PSY.H₂_6_2
#check @PSY.exists_not_twoRec

#print axioms PSY.psy_conj_6_3
#print axioms PSY.recursive_dominates
#print axioms PSY.H_eq_H₂
#print axioms PSY.twoRec_nonempty
#print axioms PSY.H_3_2
#print axioms PSY.H₂_3_2
#print axioms PSY.H_4_2
#print axioms PSY.H₂_4_2
#print axioms PSY.H₂_5_2
#print axioms PSY.H₂_6_2
#print axioms PSY.H_5_2
#print axioms PSY.H_6_2
#print axioms PSY.exists_not_twoRec
```

