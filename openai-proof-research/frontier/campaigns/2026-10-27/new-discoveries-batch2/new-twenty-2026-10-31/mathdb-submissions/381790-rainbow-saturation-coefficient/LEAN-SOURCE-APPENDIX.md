# Lean source appendix for MathDB 381790

Fourteen modules in import order, byte-identical to `src/`. The summary module `RainbowMain` prints every definition, endpoint statement and axiom list.

### `RainbowDefinitions.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Sym
import Mathlib.Order.Lattice.Nat

/-! Source-faithful palette repair: the minimization uses the allowed colours ℕ. -/
namespace Rainbow381790

structure ECGraph (V C : Type) where
  G : SimpleGraph V
  col : Sym2 V → C

def RainbowCliqueIn {V C : Type} (Γ : ECGraph V C) (S : Set V)
    (m : ℕ) (avoid : C → Prop) : Prop :=
  ∃ s : Finset V, (↑s ⊆ S) ∧ s.card = m ∧ (s : Set V).Pairwise Γ.G.Adj ∧
    Set.InjOn Γ.col {e | e ∈ s.sym2 ∧ ¬ e.IsDiag} ∧
    ∀ e ∈ s.sym2, ¬ e.IsDiag → ¬ avoid (Γ.col e)

def InHatF {V C : Type} (k : ℕ) (Γ : ECGraph V C) : Prop :=
  ¬ RainbowCliqueIn Γ Set.univ (k+1) (fun _ => False) ∧
  (∀ v, RainbowCliqueIn Γ {v}ᶜ k (fun _ => False)) ∧
  (∀ c : C, RainbowCliqueIn Γ Set.univ k (· = c))

noncomputable def f (k : ℕ) : ℕ :=
  sInf {n | ∃ Γ : ECGraph (Fin n) ℕ, InHatF k Γ}

end Rainbow381790
```

### `RainbowVacuity.lean`

```lean
import RainbowDefinitions
import Lean.Elab.Tactic.Omega

namespace Rainbow381790

/-- A legal object under the review's exact arbitrary-Type palette definition. -/
def emptyPaletteGraph : ECGraph (Fin 0) Empty where
  G := ⊥
  col := isEmptyElim

theorem emptyPaletteGraph_mem (k : ℕ) : InHatF k emptyPaletteGraph := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, _, hcard, _⟩
    have hs : s = ∅ := by ext v; exact Fin.elim0 v
    simp [hs] at hcard
  · intro v
    exact Fin.elim0 v
  · intro c
    exact Empty.elim c

/-- The defining set is nonempty; the failure is not the default for sInf ∅. -/
theorem zero_mem_minimization_set (k : ℕ) :
    0 ∈ {n | ∃ (C : Type) (Γ : ECGraph (Fin n) C), InHatF k Γ} :=
  ⟨Empty, emptyPaletteGraph, emptyPaletteGraph_mem k⟩

/-- P2 does give the intended lower bound once a vertex exists. -/
theorem member_order_lower_bound {n k : ℕ} {C : Type}
    (Γ : ECGraph (Fin n) C) (hΓ : InHatF k Γ) (hn : 0 < n) : k + 1 ≤ n := by
  classical
  let v : Fin n := ⟨0, hn⟩
  obtain ⟨s, hsub, hcard, _⟩ := hΓ.2.1 v
  have hnot : v ∉ s := by
    intro hv
    exact hsub hv (by simp)
  have hc := Finset.card_le_univ (insert v s)
  rw [Finset.card_insert_of_notMem hnot, hcard, Fintype.card_fin] at hc
  exact hc

/-- A nonempty palette rules out zero vertices for positive k, via P3. -/
theorem member_positive_order {n k : ℕ} {C : Type} [Nonempty C]
    (Γ : ECGraph (Fin n) C) (hΓ : InHatF k Γ) (hk : 0 < k) : 0 < n := by
  obtain ⟨s, _, hcard, _⟩ := hΓ.2.2 (Classical.choice ‹Nonempty C›)
  have hc := Finset.card_le_univ s
  rw [hcard, Fintype.card_fin] at hc
  omega

theorem member_order_lower_bound_nonempty_palette {n k : ℕ} {C : Type} [Nonempty C]
    (Γ : ECGraph (Fin n) C) (hΓ : InHatF k Γ) (hk : 0 < k) : k + 1 ≤ n :=
  member_order_lower_bound Γ hΓ (member_positive_order Γ hΓ hk)

/-- The zero-parameter issue persists even with an inhabited colour palette. -/
def zeroGraph : ECGraph (Fin 0) Unit where
  G := ⊥
  col := fun _ => ()

theorem zeroGraph_mem : InHatF 0 zeroGraph := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, _, hcard, _⟩
    have hs : s = ∅ := by ext v; exact Fin.elim0 v
    simp [hs] at hcard
  · intro v
    exact Fin.elim0 v
  · intro c
    refine ⟨∅, by simp, rfl, ?_, ?_, ?_⟩
    · simp
    · simp [Set.InjOn]
    · simp

#print axioms emptyPaletteGraph_mem
#print axioms zero_mem_minimization_set
#print axioms member_order_lower_bound
#print axioms member_positive_order
#print axioms member_order_lower_bound_nonempty_palette
#print axioms zeroGraph_mem

end Rainbow381790
```

### `RainbowSanity.lean`

```lean
import RainbowDefinitions

namespace Rainbow381790

/-- Every unordered edge is itself its colour. -/
def rainbowComplete (V : Type) : ECGraph V (Sym2 V) where
  G := ⊤
  col := id

theorem rainbowComplete_clique (n : ℕ) :
    RainbowCliqueIn (rainbowComplete (Fin n)) Set.univ n (fun _ => False) := by
  classical
  refine ⟨Finset.univ, by simp, by simp, ?_, ?_, ?_⟩
  · intro a _ b _ hab
    exact hab
  · exact Function.injective_id.injOn
  · simp

theorem rainbow_K_succ_not_mem (k : ℕ) :
    ¬ InHatF k (rainbowComplete (Fin (k + 1))) := by
  intro h
  exact h.1 (rainbowComplete_clique (k + 1))

#print axioms rainbowComplete_clique
#print axioms rainbow_K_succ_not_mem

end Rainbow381790
```

### `RainbowFormula.lean`

```lean
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Rainbow381790
noncomputable section

def conjFormula (k : ℕ) : ℤ :=
  k + ⌈(-1 + Real.sqrt (4 * (k : ℝ) - 3)) / 2⌉

theorem sqrt_2053_bounds : (45 : ℝ) < Real.sqrt 2053 ∧ Real.sqrt 2053 < 46 := by
  constructor
  · apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 45)).2
    norm_num
  · apply (Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 2053) (by norm_num : (0 : ℝ) ≤ 46)).2
    norm_num

theorem ceil_at_2053 : ⌈(-1 + Real.sqrt (2053 : ℝ)) / 2⌉ = (23 : ℤ) := by
  apply Int.ceil_eq_iff.mpr
  obtain ⟨hl, hu⟩ := sqrt_2053_bounds
  constructor <;> norm_num <;> linarith

theorem conjFormula_514 : conjFormula 514 = 537 := by
  unfold conjFormula
  norm_num
  rw [ceil_at_2053]
  norm_num

#print axioms sqrt_2053_bounds
#print axioms ceil_at_2053
#print axioms conjFormula_514

end

end Rainbow381790
```

### `RainbowConstruction.lean`

```lean
import RainbowDefinitions
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Rainbow381790
namespace Tripartite

inductive Vertex (I : Type) where
  | a : I → Vertex I
  | b : I → Vertex I
  | c : I → Vertex I
  | x : I → I → I → Vertex I
  deriving DecidableEq, Fintype

open Vertex
variable {I : Type} [DecidableEq I]
abbrev Colour (I : Type) := (I × I) ⊕ Sym2 (Vertex I)

def colourPair : Vertex I → Vertex I → Colour I
  | a i, b j | b j, a i => Sum.inl (i,j)
  | c l, x i j m | x i j m, c l =>
      if l = m then Sum.inl (i,j) else Sum.inr s(c l, x i j m)
  | u, v => Sum.inr s(u,v)

theorem colourPair_symm (u v : Vertex I) : colourPair u v = colourPair v u := by
  cases u <;> cases v <;> simp [colourPair, Sym2.eq_swap]

def colour : Sym2 (Vertex I) → Colour I := Sym2.lift ⟨colourPair, colourPair_symm⟩

@[simp] theorem colour_mk (u v : Vertex I) : colour s(u,v) = colourPair u v := rfl

/-- Exactly the repeated colour classes described in the construction. -/
theorem colour_shared_iff (e : Sym2 (Vertex I)) (i j : I) :
    colour e = Sum.inl (i,j) ↔
    e = s(a i, b j) ∨ ∃ l, e = s(c l, x i j l) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    cases u <;> cases v <;>
      simp [colourPair, Sym2.eq_iff, and_comm] <;> split <;> simp_all [eq_comm]

theorem colour_fresh (e : Sym2 (Vertex I)) (d : Sym2 (Vertex I))
    (h : colour e = Sum.inr d) : e = d := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    cases u <;> cases v <;> simp [colourPair] at h <;>
      first | exact h | (split at h <;> simp_all [Sym2.eq_swap])

/-- Private vertices are universal; core edges run between different parts. -/
def part : Vertex I → Fin 4
  | a _ => 0 | b _ => 1 | c _ => 2 | x _ _ _ => 3

def graph : SimpleGraph (Vertex I) where
  Adj u v := u ≠ v ∧ (part u ≠ part v ∨ part u = 3)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h
    · exact Or.inl h.symm
    · by_cases hv : part v = 3
      · exact Or.inr hv
      · exact Or.inl (by intro he; exact hv (he ▸ h))⟩
  loopless := ⟨fun u h => h.1 rfl⟩

def construction : ECGraph (Vertex I) (Colour I) := ⟨graph, colour⟩

@[simp] theorem adj_aa (i j : I) : ¬ graph.Adj (a i) (a j) := by simp [graph, part]
@[simp] theorem adj_bb (i j : I) : ¬ graph.Adj (b i) (b j) := by simp [graph, part]
@[simp] theorem adj_cc (i j : I) : ¬ graph.Adj (c i) (c j) := by simp [graph, part]

end Tripartite
end Rainbow381790
```

### `RainbowWitness.lean`

```lean
import RainbowConstruction

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace Rainbow381790.Tripartite
open Vertex
variable {I : Type} [DecidableEq I]

theorem rainbow_injective (s : Finset (Vertex I))
    (_ha : ∀ i j, a i ∈ s → a j ∈ s → i = j)
    (_hb : ∀ i j, b i ∈ s → b j ∈ s → i = j)
    (hc : ∀ i j, c i ∈ s → c j ∈ s → i = j)
    (hd : ∀ i j l, a i ∈ s → b j ∈ s → c l ∈ s → x i j l ∉ s) :
    Set.InjOn colour {e | e ∈ s.sym2 ∧ ¬ e.IsDiag} := by
  intro e he d hd' hed
  cases hcol : colour e with
  | inr q =>
    have hdcol : colour d = Sum.inr q := hed.symm.trans hcol
    exact (colour_fresh e q hcol).trans (colour_fresh d q hdcol).symm
  | inl p =>
    obtain ⟨i,j⟩ := p
    have h1 := (colour_shared_iff e i j).mp hcol
    have h2 := (colour_shared_iff d i j).mp (hed.symm.trans hcol)
    rcases h1 with rfl | ⟨l,rfl⟩ <;> rcases h2 with rfl | ⟨m,rfl⟩
    · rfl
    · obtain ⟨hai,hbj⟩ := Finset.mk_mem_sym2_iff.mp he.1
      obtain ⟨hcm,hxm⟩ := Finset.mk_mem_sym2_iff.mp hd'.1
      exact False.elim (hd i j m hai hbj hcm hxm)
    · obtain ⟨hcl,hxl⟩ := Finset.mk_mem_sym2_iff.mp he.1
      obtain ⟨hai,hbj⟩ := Finset.mk_mem_sym2_iff.mp hd'.1
      exact False.elim (hd i j l hai hbj hcl hxl)
    · have hlm := hc l m (Finset.mk_mem_sym2_iff.mp he.1).1
          (Finset.mk_mem_sym2_iff.mp hd'.1).1
      rw [hlm]

variable [Fintype I]

def privates : Finset (Vertex I) :=
  Finset.univ.image (fun p : I × I × I => x p.1 p.2.1 p.2.2)

@[simp] theorem mem_privates (v : Vertex I) : v ∈ privates ↔ ∃ i j l, v = x i j l := by
  simp only [privates, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i,j,l⟩,h⟩; exact ⟨i,j,l,h.symm⟩
  · rintro ⟨i,j,l,rfl⟩; exact ⟨(i,j,l),rfl⟩

@[simp] theorem a_not_private (i : I) : a i ∉ (privates : Finset (Vertex I)) := by simp
@[simp] theorem b_not_private (i : I) : b i ∉ (privates : Finset (Vertex I)) := by simp
@[simp] theorem c_not_private (i : I) : c i ∉ (privates : Finset (Vertex I)) := by simp
@[simp] theorem x_private (i j l : I) : x i j l ∈ (privates : Finset (Vertex I)) := by simp

@[simp] theorem card_privates : (privates : Finset (Vertex I)).card = Fintype.card I ^ 3 := by
  rw [privates, Finset.card_image_of_injective]
  · simp [pow_succ, Nat.mul_assoc]
  · rintro ⟨i,j,l⟩ ⟨i',j',l'⟩ h
    simpa using h

def box (i j l : I) : Finset (Vertex I) := insert (a i) (insert (b j) (insert (c l) privates))

@[simp] theorem mem_box (i j l : I) (v : Vertex I) :
    v ∈ box i j l ↔ v = a i ∨ v = b j ∨ v = c l ∨ v ∈ privates := by
  simp [box]

@[simp] theorem card_box (i j l : I) : (box i j l).card = Fintype.card I ^ 3 + 3 := by
  simp [box, Nat.add_assoc]

theorem box_clique (i j l : I) : (box i j l : Set (Vertex I)).Pairwise graph.Adj := by
  intro u hu v hv huv
  refine ⟨huv, ?_⟩
  cases u <;> cases v <;> simp_all [part, mem_box]

theorem box_rainbow (i j l : I) (s : Finset (Vertex I)) (hs : s ⊆ box i j l)
    (hd : ¬ (a i ∈ s ∧ b j ∈ s ∧ c l ∈ s ∧ x i j l ∈ s)) :
    Set.InjOn colour {e | e ∈ s.sym2 ∧ ¬ e.IsDiag} := by
  have ha : ∀ q, a q ∈ s → q = i := by intro q h; simpa using hs h
  have hb : ∀ q, b q ∈ s → q = j := by intro q h; simpa using hs h
  have hc : ∀ q, c q ∈ s → q = l := by intro q h; simpa using hs h
  apply rainbow_injective s
  · intro q r hq hr; exact (ha q hq).trans (ha r hr).symm
  · intro q r hq hr; exact (hb q hq).trans (hb r hr).symm
  · intro q r hq hr; exact (hc q hq).trans (hc r hr).symm
  · intro q r z hq hr hz hx
    have := ha q hq; subst q
    have := hb r hr; subst r
    have := hc z hz; subst z
    exact hd ⟨hq,hr,hz,hx⟩

end Rainbow381790.Tripartite
```

### `RainbowProperties.lean`

```lean
import RainbowWitness

set_option linter.unusedSimpArgs false
namespace Rainbow381790.Tripartite
open Vertex
variable {I : Type} [DecidableEq I] [Fintype I] [Nonempty I]

theorem select_label (s : Finset (Vertex I)) (g : I → Vertex I)
    (h : ∀ i j, g i ∈ s → g j ∈ s → i = j) :
    ∃ i, ∀ j, g j ∈ s → j = i := by
  classical
  by_cases hex : ∃ i, g i ∈ s
  · obtain ⟨i,hi⟩ := hex
    exact ⟨i,fun j hj => h j i hj hi⟩
  · exact ⟨Classical.choice ‹Nonempty I›, fun j hj => False.elim (hex ⟨j,hj⟩)⟩

theorem clique_subset_box (s : Finset (Vertex I))
    (hs : (s : Set (Vertex I)).Pairwise graph.Adj) :
    ∃ i j l, s ⊆ box i j l := by
  have ha : ∀ i j, a i ∈ s → a j ∈ s → i = j := by
    intro i j hi hj
    by_contra hij
    exact adj_aa i j (hs hi hj (by simpa using hij))
  have hb : ∀ i j, b i ∈ s → b j ∈ s → i = j := by
    intro i j hi hj
    by_contra hij
    exact adj_bb i j (hs hi hj (by simpa using hij))
  have hc : ∀ i j, c i ∈ s → c j ∈ s → i = j := by
    intro i j hi hj
    by_contra hij
    exact adj_cc i j (hs hi hj (by simpa using hij))
  obtain ⟨i,hi⟩ := select_label s a ha
  obtain ⟨j,hj⟩ := select_label s b hb
  obtain ⟨l,hl⟩ := select_label s c hc
  refine ⟨i,j,l,?_⟩
  intro v hv
  cases v with
  | a q => simp [hi q hv]
  | b q => simp [hj q hv]
  | c q => simp [hl q hv]
  | x q r z => simp

theorem no_large_rainbow :
    ¬ RainbowCliqueIn (construction : ECGraph (Vertex I) (Colour I)) Set.univ
      (Fintype.card I ^ 3 + 2 + 1) (fun _ => False) := by
  rintro ⟨s,_,hcard,hcl,hinj,_⟩
  obtain ⟨i,j,l,hsub⟩ := clique_subset_box s hcl
  have heq : s = box i j l := Finset.eq_of_subset_of_card_le hsub (by
    rw [card_box,hcard])
  subst s
  have h1 : s(a i,b j) ∈ (box i j l).sym2 ∧ ¬ s(a i,b j).IsDiag := by simp
  have h2 : s(c l,x i j l) ∈ (box i j l).sym2 ∧ ¬ s(c l,x i j l).IsDiag := by simp
  have hh := hinj h1 h2 (by simp [construction,colourPair])
  simp [Sym2.eq_iff] at hh

/-- Removing a core vertex, or the matching private vertex, destroys the sole collision. -/
theorem erased_box (i j l : I) (v : Vertex I)
    (hv : v = a i ∨ v = b j ∨ v = c l ∨ v = x i j l) :
    RainbowCliqueIn (construction : ECGraph (Vertex I) (Colour I)) {v}ᶜ
      (Fintype.card I ^ 3 + 2) (fun _ => False) := by
  classical
  have hmem : v ∈ box i j l := by rcases hv with rfl | rfl | rfl | rfl <;> simp
  refine ⟨(box i j l).erase v, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    simpa using (Finset.mem_erase.mp hu).1
  · rw [Finset.card_erase_of_mem hmem,card_box]; omega
  · exact (box_clique i j l).mono (Finset.erase_subset v _)
  · apply box_rainbow i j l _ (Finset.erase_subset v _)
    rcases hv with rfl | rfl | rfl | rfl <;> simp
  · simp

theorem vertex_avoid (v : Vertex I) :
    RainbowCliqueIn (construction : ECGraph (Vertex I) (Colour I)) {v}ᶜ
      (Fintype.card I ^ 3 + 2) (fun _ => False) := by
  let d : I := Classical.choice ‹Nonempty I›
  cases v with
  | a i => exact erased_box i d d (a i) (Or.inl rfl)
  | b j => exact erased_box d j d (b j) (Or.inr (Or.inl rfl))
  | c l => exact erased_box d d l (c l) (Or.inr (Or.inr (Or.inl rfl)))
  | x i j l => exact erased_box i j l (x i j l) (Or.inr (Or.inr (Or.inr rfl)))

theorem shared_avoid (i j i' l : I) (hi : i' ≠ i) :
    RainbowCliqueIn (construction : ECGraph (Vertex I) (Colour I)) Set.univ
      (Fintype.card I ^ 3 + 2) (· = Sum.inl (i,j)) := by
  -- Use the explicit erased box rather than an opaque existential witness.
  classical
  refine ⟨(box i' j l).erase (c l), by simp, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem (by simp : c l ∈ box i' j l),card_box]; omega
  · exact (box_clique i' j l).mono (Finset.erase_subset _ _)
  · apply box_rainbow i' j l _ (Finset.erase_subset _ _)
    simp
  · intro e he _ hcol
    rcases (colour_shared_iff e i j).mp hcol with rfl | ⟨m,rfl⟩
    · have hh := (Finset.mk_mem_sym2_iff.mp he).1
      simp at hh
      exact hi hh.symm
    · have hh := (Finset.mk_mem_sym2_iff.mp he).1
      simp at hh

theorem fresh_avoid (d : Sym2 (Vertex I)) :
    RainbowCliqueIn (construction : ECGraph (Vertex I) (Colour I)) Set.univ
      (Fintype.card I ^ 3 + 2) (· = Sum.inr d) := by
  induction d using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨s,hsub,hcard,hcl,hinj,_⟩ := vertex_avoid u
    refine ⟨s, by simp, hcard,hcl,hinj,?_⟩
    intro e he _ hcol
    have heq := colour_fresh e s(u,v) hcol
    subst e
    have hu := (Finset.mk_mem_sym2_iff.mp he).1
    exact hsub hu (by simp)

theorem member (hI : ∀ i : I, ∃ j : I, j ≠ i) :
    InHatF (Fintype.card I ^ 3 + 2) (construction : ECGraph (Vertex I) (Colour I)) := by
  refine ⟨no_large_rainbow, vertex_avoid, ?_⟩
  intro q
  cases q with
  | inr d => exact fresh_avoid d
  | inl p =>
    obtain ⟨i,j⟩ := p
    obtain ⟨i',hi⟩ := hI i
    exact shared_avoid i j i' (Classical.choice ‹Nonempty I›) hi

#print axioms member
end Rainbow381790.Tripartite
```

### `RainbowTransport.lean`

```lean
import RainbowDefinitions
import Mathlib.Data.Fintype.EquivFin

set_option linter.unusedSimpArgs false
namespace Rainbow381790

variable {V W C D : Type}

def recolour (Γ : ECGraph V C) (h : C → D) : ECGraph V D := ⟨Γ.G,h ∘ Γ.col⟩

theorem recolour_clique (Γ : ECGraph V C) (h : C → D) (hh : Function.Injective h)
    (S : Set V) (m : ℕ) (p : D → Prop) :
    RainbowCliqueIn (recolour Γ h) S m p ↔ RainbowCliqueIn Γ S m (p ∘ h) := by
  constructor
  · rintro ⟨s,hsub,hcard,hcl,hinj,hav⟩
    exact ⟨s,hsub,hcard,hcl,fun _ he _ hd heq => hinj he hd (congrArg h heq),hav⟩
  · rintro ⟨s,hsub,hcard,hcl,hinj,hav⟩
    exact ⟨s,hsub,hcard,hcl,fun _ he _ hd heq => hinj he hd (hh heq),hav⟩

theorem recolour_member [Nonempty C] (Γ : ECGraph V C) (h : C → D)
    (hh : Function.Injective h) {k : ℕ} (hΓ : InHatF k Γ) : InHatF k (recolour Γ h) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact fun hc => hΓ.1 ((recolour_clique Γ h hh _ _ _).mp hc)
  · intro v
    exact (recolour_clique Γ h hh _ _ _).mpr (hΓ.2.1 v)
  · intro d
    apply (recolour_clique Γ h hh _ _ _).mpr
    by_cases hd : ∃ c, h c = d
    · obtain ⟨c,rfl⟩ := hd
      obtain ⟨s,hs,hc,hcl,hi,ha⟩ := hΓ.2.2 c
      refine ⟨s,hs,hc,hcl,hi,?_⟩
      intro e he hn heq
      exact ha e he hn (hh heq)
    · obtain ⟨s,hs,hc,hcl,hi,_⟩ := hΓ.2.2 (Classical.choice ‹Nonempty C›)
      exact ⟨s,hs,hc,hcl,hi,fun e _ _ heq => hd ⟨Γ.col e,heq⟩⟩

/-- Relabel vertices without changing any of the literal rainbow-clique conditions. -/
theorem map_clique (Γ : ECGraph V C) (Δ : ECGraph W C) (e : V ≃ W)
    (hadj : ∀ u v, Γ.G.Adj u v ↔ Δ.G.Adj (e u) (e v))
    (hcol : ∀ d, Δ.col (d.map e) = Γ.col d)
    {S : Set V} {T : Set W} {m : ℕ} {p : C → Prop}
    (hST : ∀ v ∈ S, e v ∈ T) (hc : RainbowCliqueIn Γ S m p) :
    RainbowCliqueIn Δ T m p := by
  classical
  obtain ⟨s,hs,hcard,hcl,hinj,hav⟩ := hc
  refine ⟨s.map e.toEmbedding, ?_, by simpa using hcard, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hv
    exact hST u (hs hu)
  · intro u hu v hv huv
    obtain ⟨u,hu0,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨v,hv0,rfl⟩ := Finset.mem_map.mp hv
    exact (hadj u v).mp (hcl hu0 hv0 (fun he => huv (congrArg e he)))
  · intro d hd q hq heq
    rw [Finset.sym2_map] at hd hq
    obtain ⟨d,hd0,rfl⟩ := Finset.mem_map.mp hd.1
    obtain ⟨q,hq0,rfl⟩ := Finset.mem_map.mp hq.1
    have hde : ¬ d.IsDiag := fun hn => hd.2 (hn.map)
    have hqe : ¬ q.IsDiag := fun hn => hq.2 (hn.map)
    change Δ.col (Sym2.map e d) = Δ.col (Sym2.map e q) at heq
    have heq' : Γ.col d = Γ.col q := by simpa only [hcol] using heq
    exact congrArg (Sym2.map e) (hinj ⟨hd0,hde⟩ ⟨hq0,hqe⟩ heq')
  · intro d hd hn
    rw [Finset.sym2_map] at hd
    obtain ⟨d,hd0,rfl⟩ := Finset.mem_map.mp hd
    change ¬ p (Δ.col (Sym2.map e d))
    rw [hcol]
    exact hav d hd0 (fun hh => hn hh.map)

def relabel (Γ : ECGraph V C) (e : V ≃ W) : ECGraph W C where
  G := Γ.G.comap e.symm
  col := Γ.col ∘ Sym2.map e.symm

@[simp] theorem relabel_col (Γ : ECGraph V C) (e : V ≃ W) (d : Sym2 V) :
    (relabel Γ e).col (d.map e) = Γ.col d := by
  induction d using Sym2.inductionOn with
  | _ u v => simp [relabel,Sym2.map_mk]

theorem relabel_member (Γ : ECGraph V C) (e : V ≃ W) {k : ℕ}
    (hΓ : InHatF k Γ) : InHatF k (relabel Γ e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    apply hΓ.1
    exact map_clique (relabel Γ e) Γ e.symm (by intro u v; rfl)
      (by intro d; rfl) (by simp) hc
  · intro v
    apply map_clique Γ (relabel Γ e) e (by intro u v; simp [relabel])
      (relabel_col Γ e) _ (hΓ.2.1 (e.symm v))
    intro u hu he
    apply hu
    simpa using congrArg e.symm he
  · intro c
    exact map_clique Γ (relabel Γ e) e (by intro u v; simp [relabel])
      (relabel_col Γ e) (by simp) (hΓ.2.2 c)

end Rainbow381790
```

### `RainbowFamily.lean`

```lean
import RainbowProperties
import RainbowTransport
import Mathlib.Tactic.Ring

namespace Rainbow381790
open Tripartite

/-- Finite palettes embed injectively into the source's fixed palette ℕ. -/
noncomputable def finiteColourCode (C : Type) [Fintype C] : C → ℕ :=
  fun c => (Fintype.equivFin C c).val

theorem finiteColourCode_injective (C : Type) [Fintype C] :
    Function.Injective (finiteColourCode C) :=
  fun _ _ h => (Fintype.equivFin C).injective (Fin.val_injective h)

theorem vertex_card (t : ℕ) : Fintype.card (Vertex (Fin t)) = t^3 + 3*t := by
  rw [← Fintype.card_congr (Vertex.proxyTypeEquiv (Fin t))]
  simp [pow_succ]
  ring

noncomputable def familyGraph (t : ℕ) : ECGraph (Fin (t^3 + 3*t)) ℕ :=
  recolour (relabel (construction : ECGraph (Vertex (Fin t)) (Colour (Fin t)))
    ((Fintype.equivFin _).trans (finCongr (vertex_card t))))
    (finiteColourCode (Colour (Fin t)))

theorem familyGraph_member (t : ℕ) (ht : 2 ≤ t) : InHatF (t^3+2) (familyGraph t) := by
  have : Nonempty (Fin t) := ⟨⟨0,by omega⟩⟩
  have : Nonempty (Colour (Fin t)) := ⟨Sum.inl (Classical.choice inferInstance,Classical.choice inferInstance)⟩
  apply recolour_member _ _ (finiteColourCode_injective _)
  apply relabel_member
  simpa using (member (I := Fin t) (by
    intro i
    by_cases hi : i.val = 0
    · exact ⟨⟨1,by omega⟩,by intro he; have := congrArg Fin.val he; simp_all⟩
    · exact ⟨⟨0,by omega⟩,by intro he; have := congrArg Fin.val he; simp_all⟩))

theorem tripartite_family (t : ℕ) (ht : 2 ≤ t) :
    ∃ Γ : ECGraph (Fin (t^3+3*t)) ℕ, InHatF (t^3+2) Γ :=
  ⟨familyGraph t, familyGraph_member t ht⟩

theorem f_family_le (t : ℕ) (ht : 2 ≤ t) : f (t^3+2) ≤ t^3+3*t :=
  Nat.sInf_le (tripartite_family t ht)

#print axioms familyGraph_member
#print axioms tripartite_family
end Rainbow381790
```

### `RainbowExistence.lean`

```lean
import RainbowFamily
import RainbowVacuity

set_option linter.unusedSimpArgs false
namespace Rainbow381790
namespace Double

abbrev V (k : ℕ) := Bool × Fin k

def graph (k : ℕ) : ECGraph (V k) (Sym2 (V k)) where
  G := { Adj := fun u v => u.1 = v.1 ∧ u ≠ v
         symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
         loopless := ⟨fun _ h => h.2 rfl⟩ }
  col := id

def side (k : ℕ) (b : Bool) : Finset (V k) :=
  Finset.univ.map ⟨fun i => (b,i),fun _ _ h => (Prod.mk.inj h).2⟩

@[simp] theorem mem_side (k : ℕ) (b : Bool) (v : V k) : v ∈ side k b ↔ v.1 = b := by
  constructor
  · intro h
    obtain ⟨i,_,hi⟩ := Finset.mem_map.mp h
    exact (congrArg Prod.fst hi).symm
  · intro h
    apply Finset.mem_map.mpr
    exact ⟨v.2,Finset.mem_univ _,Prod.ext h.symm rfl⟩

@[simp] theorem card_side (k : ℕ) (b : Bool) : (side k b).card = k := by simp [side]

theorem side_clique (k : ℕ) (b : Bool) :
    (side k b : Set (V k)).Pairwise (graph k).G.Adj := by
  intro u hu v hv huv
  exact ⟨(mem_side k b u).mp hu |>.trans ((mem_side k b v).mp hv).symm,huv⟩

theorem no_large (k : ℕ) : ¬ RainbowCliqueIn (graph k) Set.univ (k+1) (fun _ => False) := by
  rintro ⟨s,_,hcard,hcl,_⟩
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hs : s ⊆ side k v.1 := by
    intro u hu
    apply (mem_side k v.1 u).mpr
    by_cases he : u = v
    · subst u; rfl
    · exact (hcl hu hv he).1
  have hh := Finset.card_le_card hs
  rw [card_side,hcard] at hh
  omega

theorem vertex_avoid (k : ℕ) (v : V k) :
    RainbowCliqueIn (graph k) {v}ᶜ k (fun _ => False) := by
  refine ⟨side k (!v.1),?_,card_side _ _,side_clique _ _,Function.injective_id.injOn,by simp⟩
  intro u hu he
  have hh := (mem_side k (!v.1) u).mp hu
  simp only [Set.mem_singleton_iff] at he
  subst u
  exact (show ∀ b : Bool, b ≠ !b by decide) v.1 hh

theorem colour_avoid (k : ℕ) (d : Sym2 (V k)) :
    RainbowCliqueIn (graph k) Set.univ k (· = d) := by
  induction d using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨s,hsub,hcard,hcl,hinj,_⟩ := vertex_avoid k u
    refine ⟨s,by simp,hcard,hcl,hinj,?_⟩
    intro e he _ heq
    change e = s(u,v) at heq
    subst e
    exact hsub (Finset.mk_mem_sym2_iff.mp he).1 (by simp)

theorem member (k : ℕ) : InHatF k (graph k) :=
  ⟨no_large k,vertex_avoid k,colour_avoid k⟩

end Double

theorem minimization_nonempty (k : ℕ) (hk : 1 ≤ k) :
    {n | ∃ Γ : ECGraph (Fin n) ℕ, InHatF k Γ}.Nonempty := by
  have : Nonempty (Fin k) := ⟨⟨0,by omega⟩⟩
  have : Nonempty (Sym2 (Double.V k)) := ⟨s((false,Classical.choice inferInstance),(false,Classical.choice inferInstance))⟩
  refine ⟨Fintype.card (Double.V k),?_⟩
  exact ⟨recolour (relabel (Double.graph k) (Fintype.equivFin _))
      (finiteColourCode _),
    recolour_member _ _ (finiteColourCode_injective _)
      (relabel_member _ _ (Double.member k))⟩

theorem f_minimum_attained (k : ℕ) (hk : 1 ≤ k) :
    ∃ Γ : ECGraph (Fin (f k)) ℕ, InHatF k Γ :=
  Nat.sInf_mem (minimization_nonempty k hk)

theorem f_lower_bound (k : ℕ) (hk : 1 ≤ k) : k+1 ≤ f k := by
  obtain ⟨Γ,hΓ⟩ := f_minimum_attained k hk
  exact member_order_lower_bound_nonempty_palette Γ hΓ (by omega)

#print axioms minimization_nonempty
#print axioms f_minimum_attained
#print axioms f_lower_bound
end Rainbow381790
```

### `RainbowEndpoint.lean`

```lean
import RainbowExistence
import RainbowFormula
import RainbowSanity
import Mathlib.Tactic.NormNum

namespace Rainbow381790

/-- An actual ℕ-coloured 536-vertex member, not an empty-set infimum argument. -/
theorem explicit_514_member :
    ∃ Γ : ECGraph (Fin 536) ℕ, InHatF 514 Γ := by
  simpa using tripartite_family 8 (by decide)

theorem f_514_le : f 514 ≤ 536 := Nat.sInf_le explicit_514_member

theorem f_514_lt_conjFormula : (f 514 : ℤ) < conjFormula 514 := by
  rw [conjFormula_514]
  have := f_514_le
  omega

/-- Literal negation of the printed conjunction, with the source's ℕ palette. -/
theorem chlt_conj_5_1_false (α : ℕ → ℝ) :
    ¬ ∀ k : ℕ, 4 ≤ k → α (k+2) = f k ∧ (f k : ℤ) = conjFormula k := by
  intro h
  have he := (h 514 (by decide)).2
  exact (ne_of_lt f_514_lt_conjFormula) he

#print axioms explicit_514_member
#print axioms f_514_le
#print axioms f_514_lt_conjFormula
#print axioms chlt_conj_5_1_false
end Rainbow381790
```

### `RainbowVariable.lean`

```lean
import RainbowDefinitions
import Mathlib.Tactic.DeriveFintype
import Lean.Elab.Tactic.Omega

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! Variable tripartite cores (the every-k extension of the written proof).

Parts `A`, `B`, `C` are indexed by `IA`, `IB`, `IC`.  Every `A`–`B` edge is present;
`c l` is adjacent to `a i` iff `NA l i` and to `b j` iff `NB l j`; each part is
independent.  There is one private vertex `x p` for every core triangle
`p = (i, j, l)`; the private vertices form a clique joined to every core vertex.
The edge `a i b j` and the edges `c l x_(i,j,l)` share the colour `(i, j)`; every
other edge has its own colour. -/
namespace Rainbow381790
namespace Variable

inductive Vertex (IA IB IC P : Type) where
  | a : IA → Vertex IA IB IC P
  | b : IB → Vertex IA IB IC P
  | c : IC → Vertex IA IB IC P
  | x : P → Vertex IA IB IC P
  deriving DecidableEq, Fintype

open Vertex

variable {IA IB IC : Type} [DecidableEq IA] [DecidableEq IB] [DecidableEq IC]

/-- The core triangles: `(i, j, l)` with `c l` adjacent to both `a i` and `b j`. -/
abbrev Tri (NA : IC → IA → Bool) (NB : IC → IB → Bool) : Type :=
  {p : IA × IB × IC // NA p.2.2 p.1 = true ∧ NB p.2.2 p.2.1 = true}

variable (NA : IC → IA → Bool) (NB : IC → IB → Bool)

abbrev V := Vertex IA IB IC (Tri NA NB)
abbrev Colour := (IA × IB) ⊕ Sym2 (V NA NB)

variable {NA NB}

def colourPair : V NA NB → V NA NB → Colour NA NB
  | a i, b j | b j, a i => Sum.inl (i, j)
  | c l, x p | x p, c l =>
      if p.1.2.2 = l then Sum.inl (p.1.1, p.1.2.1) else Sum.inr s(c l, x p)
  | u, v => Sum.inr s(u, v)

theorem colourPair_symm (u v : V NA NB) : colourPair u v = colourPair v u := by
  cases u <;> cases v <;> simp [colourPair, Sym2.eq_swap]

def colour : Sym2 (V NA NB) → Colour NA NB := Sym2.lift ⟨colourPair, colourPair_symm⟩

@[simp] theorem colour_mk (u v : V NA NB) : colour s(u, v) = colourPair u v := rfl

theorem colour_fresh (e d : Sym2 (V NA NB)) (h : colour e = Sum.inr d) : e = d := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    cases u <;> cases v <;> simp [colourPair] at h <;>
      first | exact h | (split at h <;> simp_all [Sym2.eq_swap])

/-- The repeated colour classes are exactly `{a i b j} ∪ {c l x_(i,j,l)}`. -/
theorem colour_shared (e : Sym2 (V NA NB)) (i : IA) (j : IB)
    (h : colour e = Sum.inl (i, j)) :
    e = s(a i, b j) ∨ ∃ p : Tri NA NB, p.1.1 = i ∧ p.1.2.1 = j ∧ e = s(c p.1.2.2, x p) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    cases u <;> cases v <;> simp [colourPair] at h
    · obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl
    · obtain ⟨rfl, rfl⟩ := h; exact Or.inl Sym2.eq_swap
    · rename_i l p
      split at h
      · rename_i hl
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        subst hl
        exact Or.inr ⟨p, rfl, rfl, rfl⟩
      · simp at h
    · rename_i p l
      split at h
      · rename_i hl
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        subst hl
        exact Or.inr ⟨p, rfl, rfl, Sym2.eq_swap⟩
      · simp at h

/-- Adjacency relation before excluding loops. -/
def adjRel : V NA NB → V NA NB → Prop
  | a _, b _ | b _, a _ => True
  | a i, c l | c l, a i => NA l i = true
  | b j, c l | c l, b j => NB l j = true
  | x _, _ | _, x _ => True
  | _, _ => False

theorem adjRel_symm (u v : V NA NB) : adjRel u v ↔ adjRel v u := by
  cases u <;> cases v <;> simp [adjRel]

def graph : SimpleGraph (V NA NB) where
  Adj u v := u ≠ v ∧ adjRel u v
  symm := ⟨fun u v h => ⟨h.1.symm, (adjRel_symm u v).mp h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable (NA NB) in
def construction : ECGraph (V NA NB) (Colour NA NB) := ⟨graph, colour⟩

@[simp] theorem adj_aa (i i' : IA) : ¬ (graph : SimpleGraph (V NA NB)).Adj (a i) (a i') := by
  simp [graph, adjRel]
@[simp] theorem adj_bb (j j' : IB) : ¬ (graph : SimpleGraph (V NA NB)).Adj (b j) (b j') := by
  simp [graph, adjRel]
@[simp] theorem adj_cc (l l' : IC) : ¬ (graph : SimpleGraph (V NA NB)).Adj (c l) (c l') := by
  simp [graph, adjRel]

/-- Rainbow criterion: at most one `C` vertex, and no triangle together with its own
private vertex. -/
theorem rainbow_injective (s : Finset (V NA NB))
    (hc : ∀ l m, c l ∈ s → c m ∈ s → l = m)
    (hd : ∀ p : Tri NA NB, a p.1.1 ∈ s → b p.1.2.1 ∈ s → c p.1.2.2 ∈ s → x p ∉ s) :
    Set.InjOn colour {e | e ∈ s.sym2 ∧ ¬ e.IsDiag} := by
  intro e he d hd' hed
  cases hcol : colour e with
  | inr q =>
    have hdcol : colour d = Sum.inr q := hed.symm.trans hcol
    exact (colour_fresh e q hcol).trans (colour_fresh d q hdcol).symm
  | inl ij =>
    obtain ⟨i, j⟩ := ij
    have h1 := colour_shared e i j hcol
    have h2 := colour_shared d i j (hed.symm.trans hcol)
    rcases h1 with rfl | ⟨p, rfl, rfl, rfl⟩ <;> rcases h2 with rfl | ⟨q, hqi, hqj, rfl⟩
    · rfl
    · obtain ⟨hai, hbj⟩ := Finset.mk_mem_sym2_iff.mp he.1
      obtain ⟨hcq, hxq⟩ := Finset.mk_mem_sym2_iff.mp hd'.1
      rw [← hqi] at hai; rw [← hqj] at hbj
      exact False.elim (hd q hai hbj hcq hxq)
    · obtain ⟨hcp, hxp⟩ := Finset.mk_mem_sym2_iff.mp he.1
      obtain ⟨hai, hbj⟩ := Finset.mk_mem_sym2_iff.mp hd'.1
      exact False.elim (hd p hai hbj hcp hxp)
    · have hl := hc _ _ (Finset.mk_mem_sym2_iff.mp he.1).1 (Finset.mk_mem_sym2_iff.mp hd'.1).1
      have hpq : p = q := Subtype.ext (Prod.ext hqi.symm (Prod.ext hqj.symm hl))
      rw [hpq]

variable [Fintype IA] [Fintype IB] [Fintype IC]

def privates : Finset (V NA NB) := Finset.univ.image x

@[simp] theorem mem_privates (v : V NA NB) : v ∈ privates ↔ ∃ p, v = x p := by
  simp only [privates, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, h⟩; exact ⟨p, h.symm⟩
  · rintro ⟨p, rfl⟩; exact ⟨p, rfl⟩

@[simp] theorem card_privates :
    (privates : Finset (V NA NB)).card = Fintype.card (Tri NA NB) := by
  rw [privates, Finset.card_image_of_injective]
  · simp
  · intro p q h; simpa using h

/-- All private vertices together with one vertex from each of `A`, `B`, `C`. -/
def box (i : IA) (j : IB) (l : IC) : Finset (V NA NB) :=
  insert (a i) (insert (b j) (insert (c l) privates))

@[simp] theorem mem_box (i : IA) (j : IB) (l : IC) (v : V NA NB) :
    v ∈ box i j l ↔ v = a i ∨ v = b j ∨ v = c l ∨ ∃ p, v = x p := by
  simp [box]

@[simp] theorem card_box (i : IA) (j : IB) (l : IC) :
    (box i j l : Finset (V NA NB)).card = Fintype.card (Tri NA NB) + 3 := by
  simp [box, Nat.add_assoc]

/-- All private vertices together with one `A` vertex and one `B` vertex. -/
def pairSet (i : IA) (j : IB) : Finset (V NA NB) := insert (a i) (insert (b j) privates)

@[simp] theorem mem_pairSet (i : IA) (j : IB) (v : V NA NB) :
    v ∈ pairSet i j ↔ v = a i ∨ v = b j ∨ ∃ p, v = x p := by
  simp [pairSet]

@[simp] theorem card_pairSet (i : IA) (j : IB) :
    (pairSet i j : Finset (V NA NB)).card = Fintype.card (Tri NA NB) + 2 := by
  simp [pairSet, Nat.add_assoc]

theorem pairSet_clique (i : IA) (j : IB) :
    ((pairSet i j : Finset (V NA NB)) : Set (V NA NB)).Pairwise graph.Adj := by
  intro u hu v hv huv
  refine ⟨huv, ?_⟩
  simp only [Finset.mem_coe, mem_pairSet] at hu hv
  rcases hu with rfl | rfl | ⟨p, rfl⟩ <;> rcases hv with rfl | rfl | ⟨q, rfl⟩ <;>
    simp_all [adjRel]

theorem pairSet_rainbow (i : IA) (j : IB) :
    Set.InjOn (colour : Sym2 (V NA NB) → Colour NA NB)
      {e | e ∈ (pairSet i j).sym2 ∧ ¬ e.IsDiag} := by
  apply rainbow_injective
  · intro l m hl; simp at hl
  · intro p _ _ hc; simp at hc

theorem triSet_clique (p : Tri NA NB) :
    ((box p.1.1 p.1.2.1 p.1.2.2 : Finset (V NA NB)) : Set (V NA NB)).Pairwise graph.Adj := by
  obtain ⟨⟨i, j, l⟩, hA, hB⟩ := p
  intro u hu v hv huv
  refine ⟨huv, ?_⟩
  simp only [Finset.mem_coe, mem_box] at hu hv
  rcases hu with rfl | rfl | rfl | ⟨p, rfl⟩ <;>
    rcases hv with rfl | rfl | rfl | ⟨q, rfl⟩ <;> simp_all [adjRel]

theorem triSet_erase_rainbow (p : Tri NA NB) :
    Set.InjOn (colour : Sym2 (V NA NB) → Colour NA NB)
      {e | e ∈ ((box p.1.1 p.1.2.1 p.1.2.2).erase (x p)).sym2 ∧ ¬ e.IsDiag} := by
  apply rainbow_injective
  · intro l m hl hm
    simp at hl hm
    rw [hl, hm]
  · intro q ha hb hc hx
    simp at ha hb hc hx
    have hpq : q = p := Subtype.ext (Prod.ext ha (Prod.ext hb hc))
    exact hx hpq

/-! The three defining properties. -/

theorem select_label {I : Type} [Nonempty I] (s : Finset (V NA NB)) (g : I → V NA NB)
    (h : ∀ i j, g i ∈ s → g j ∈ s → i = j) :
    ∃ i, ∀ j, g j ∈ s → j = i := by
  by_cases hex : ∃ i, g i ∈ s
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, fun j hj => h j i hj hi⟩
  · exact ⟨Classical.choice ‹Nonempty I›, fun j hj => False.elim (hex ⟨j, hj⟩)⟩

variable [Nonempty IA] [Nonempty IB] [Nonempty IC]

theorem clique_subset_box (s : Finset (V NA NB))
    (hs : (s : Set (V NA NB)).Pairwise graph.Adj) :
    ∃ i j l, s ⊆ box i j l := by
  have ha : ∀ i j, a i ∈ s → a j ∈ s → i = j := by
    intro i j hi hj
    by_contra hij
    exact adj_aa i j (hs hi hj (by simpa using hij))
  have hb : ∀ i j, b i ∈ s → b j ∈ s → i = j := by
    intro i j hi hj
    by_contra hij
    exact adj_bb i j (hs hi hj (by simpa using hij))
  have hc : ∀ i j, c i ∈ s → c j ∈ s → i = j := by
    intro i j hi hj
    by_contra hij
    exact adj_cc i j (hs hi hj (by simpa using hij))
  obtain ⟨i, hi⟩ := select_label s a ha
  obtain ⟨j, hj⟩ := select_label s b hb
  obtain ⟨l, hl⟩ := select_label s c hc
  refine ⟨i, j, l, ?_⟩
  intro v hv
  cases v with
  | a q => simp [hi q hv]
  | b q => simp [hj q hv]
  | c q => simp [hl q hv]
  | x q => simp

theorem no_large_rainbow :
    ¬ RainbowCliqueIn (construction NA NB) Set.univ
      (Fintype.card (Tri NA NB) + 2 + 1) (fun _ => False) := by
  rintro ⟨s, _, hcard, hcl, hinj, _⟩
  obtain ⟨i, j, l, hsub⟩ := clique_subset_box s hcl
  have heq : s = box i j l := Finset.eq_of_subset_of_card_le hsub (by
    rw [card_box, hcard])
  subst s
  have hac : (construction NA NB).G.Adj (a i) (c l) :=
    hcl (Finset.mem_coe.mpr (by simp)) (Finset.mem_coe.mpr (by simp)) (by simp)
  have hbc : (construction NA NB).G.Adj (b j) (c l) :=
    hcl (Finset.mem_coe.mpr (by simp)) (Finset.mem_coe.mpr (by simp)) (by simp)
  have hA : NA l i = true := hac.2
  have hB : NB l j = true := hbc.2
  let p : Tri NA NB := ⟨(i, j, l), hA, hB⟩
  have h1 : s(a i, b j) ∈ (box i j l : Finset (V NA NB)).sym2 ∧
      ¬ (s(a i, b j) : Sym2 (V NA NB)).IsDiag := by simp
  have h2 : s(c l, x p) ∈ (box i j l : Finset (V NA NB)).sym2 ∧
      ¬ (s(c l, x p) : Sym2 (V NA NB)).IsDiag := by
    refine ⟨Finset.mk_mem_sym2_iff.mpr ⟨by simp, by simp⟩, by simp⟩
  have hh := hinj h1 h2 (by simp [construction, colourPair, p])
  simp [Sym2.eq_iff] at hh

theorem pair_avoid (i : IA) (j : IB) (v : V NA NB) (hv : v ∉ pairSet i j) :
    RainbowCliqueIn (construction NA NB) {v}ᶜ
      (Fintype.card (Tri NA NB) + 2) (fun _ => False) := by
  refine ⟨pairSet i j, ?_, card_pairSet i j, pairSet_clique i j, pairSet_rainbow i j, by simp⟩
  intro u hu he
  simp only [Set.mem_singleton_iff] at he
  subst he
  exact hv hu

theorem vertex_avoid (hA : ∀ i : IA, ∃ i', i' ≠ i) (hB : ∀ j : IB, ∃ j', j' ≠ j)
    (v : V NA NB) :
    RainbowCliqueIn (construction NA NB) {v}ᶜ
      (Fintype.card (Tri NA NB) + 2) (fun _ => False) := by
  let i0 : IA := Classical.choice ‹Nonempty IA›
  let j0 : IB := Classical.choice ‹Nonempty IB›
  cases v with
  | a i =>
    obtain ⟨i', hi⟩ := hA i
    exact pair_avoid i' j0 (a i) (by simp [hi.symm])
  | b j =>
    obtain ⟨j', hj⟩ := hB j
    exact pair_avoid i0 j' (b j) (by simp [hj.symm])
  | c l => exact pair_avoid i0 j0 (c l) (by simp)
  | x p =>
    refine ⟨(box p.1.1 p.1.2.1 p.1.2.2).erase (x p), ?_, ?_, ?_, triSet_erase_rainbow p, by simp⟩
    · intro u hu
      simpa using (Finset.mem_erase.mp hu).1
    · rw [Finset.card_erase_of_mem (by simp), card_box]; omega
    · exact (triSet_clique p).mono (Finset.erase_subset _ _)

theorem shared_avoid (i i' : IA) (j : IB) (hi : i' ≠ i) :
    RainbowCliqueIn (construction NA NB) Set.univ
      (Fintype.card (Tri NA NB) + 2) (· = Sum.inl (i, j)) := by
  refine ⟨pairSet i' j, by simp, card_pairSet i' j, pairSet_clique i' j,
    pairSet_rainbow i' j, ?_⟩
  intro e he _ hcol
  rcases colour_shared e i j hcol with rfl | ⟨p, _, _, rfl⟩
  · have hh := (Finset.mk_mem_sym2_iff.mp he).1
    simp at hh
    exact hi hh.symm
  · have hh := (Finset.mk_mem_sym2_iff.mp he).1
    simp at hh

theorem fresh_avoid (hA : ∀ i : IA, ∃ i', i' ≠ i) (hB : ∀ j : IB, ∃ j', j' ≠ j)
    (d : Sym2 (V NA NB)) :
    RainbowCliqueIn (construction NA NB) Set.univ
      (Fintype.card (Tri NA NB) + 2) (· = Sum.inr d) := by
  induction d using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨s, hsub, hcard, hcl, hinj, _⟩ := vertex_avoid hA hB u
    refine ⟨s, by simp, hcard, hcl, hinj, ?_⟩
    intro e he _ hcol
    have heq := colour_fresh e s(u, v) hcol
    subst e
    have hu := (Finset.mk_mem_sym2_iff.mp he).1
    exact hsub hu (by simp)

/-- The variable-core graph lies in the source's class with `k = #triangles + 2`. -/
theorem member (hA : ∀ i : IA, ∃ i', i' ≠ i) (hB : ∀ j : IB, ∃ j', j' ≠ j) :
    InHatF (Fintype.card (Tri NA NB) + 2) (construction NA NB) := by
  refine ⟨no_large_rainbow, vertex_avoid hA hB, ?_⟩
  intro q
  cases q with
  | inr d => exact fresh_avoid hA hB d
  | inl ij =>
    obtain ⟨i, j⟩ := ij
    obtain ⟨i', hi⟩ := hA i
    exact shared_avoid i i' j hi

#print axioms member

end Variable
end Rainbow381790
```

### `RainbowAllK.lean`

```lean
import RainbowVariable
import RainbowFamily
import RainbowFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! The every-k bound `f k ≤ k + 3 ⌈(k - 2)^(1/3)⌉` for `k ≥ 4`. -/
namespace Rainbow381790
namespace Variable

theorem vertex_card (IA IB IC P : Type) [Fintype IA] [Fintype IB] [Fintype IC] [Fintype P] :
    Fintype.card (Vertex IA IB IC P) =
      Fintype.card IA + Fintype.card IB + Fintype.card IC + Fintype.card P := by
  rw [← Fintype.card_congr (Vertex.proxyTypeEquiv IA IB IC P)]
  simp
  omega

variable {IA IB IC : Type} [DecidableEq IA] [DecidableEq IB] [DecidableEq IC]
  [Fintype IA] [Fintype IB] [Fintype IC]

def triEquiv (NA : IC → IA → Bool) (NB : IC → IB → Bool) :
    Tri NA NB ≃ Σ l : IC, {i : IA // NA l i = true} × {j : IB // NB l j = true} where
  toFun p := ⟨p.1.2.2, ⟨p.1.1, p.2.1⟩, ⟨p.1.2.1, p.2.2⟩⟩
  invFun q := ⟨(q.2.1.1, q.2.2.1, q.1), q.2.1.2, q.2.2.2⟩
  left_inv := by rintro ⟨⟨i, j, l⟩, h⟩; rfl
  right_inv := by rintro ⟨l, ⟨i, hi⟩, ⟨j, hj⟩⟩; rfl

/-- The number of core triangles is `∑_c |N_A(c)| |N_B(c)|`. -/
theorem card_tri (NA : IC → IA → Bool) (NB : IC → IB → Bool) :
    Fintype.card (Tri NA NB) =
      ∑ l, Fintype.card {i : IA // NA l i = true} * Fintype.card {j : IB // NB l j = true} := by
  rw [Fintype.card_congr (triEquiv NA NB), Fintype.card_sigma]
  simp [Fintype.card_prod]

/-- A member of the class on `T + |IA| + |IB| + |IC|` vertices with `k = T + 2`,
palette `ℕ`, whenever `A` and `B` have at least two vertices and `C` is nonempty. -/
theorem exists_member (NA : IC → IA → Bool) (NB : IC → IB → Bool)
    [Nonempty IA] [Nonempty IB] [Nonempty IC]
    (hA : ∀ i : IA, ∃ i', i' ≠ i) (hB : ∀ j : IB, ∃ j', j' ≠ j) :
    ∃ Γ : ECGraph (Fin (Fintype.card IA + Fintype.card IB + Fintype.card IC +
      Fintype.card (Tri NA NB))) ℕ, InHatF (Fintype.card (Tri NA NB) + 2) Γ := by
  have : Nonempty (Colour NA NB) :=
    ⟨Sum.inl (Classical.choice inferInstance, Classical.choice inferInstance)⟩
  refine ⟨recolour (relabel (construction NA NB)
      ((Fintype.equivFin _).trans (finCongr (vertex_card IA IB IC (Tri NA NB)))))
      (finiteColourCode (Colour NA NB)), ?_⟩
  apply recolour_member _ _ (finiteColourCode_injective _)
  apply relabel_member
  exact member hA hB

/-! The explicit core for a prescribed number of triangles `M = q t² + u t + v`. -/

/-- `C` consists of `q` full vertices, one vertex `inr false` with neighbourhoods
`A` and `{j < u}`, and one vertex `inr true` with neighbourhoods `{i < v}` and `{0}`. -/
def specA (q t v : ℕ) : (Fin q ⊕ Bool) → Fin t → Bool
  | Sum.inl _, _ => true
  | Sum.inr false, _ => true
  | Sum.inr true, i => decide (i.val < v)

def specB (q t u : ℕ) : (Fin q ⊕ Bool) → Fin t → Bool
  | Sum.inl _, _ => true
  | Sum.inr false, j => decide (j.val < u)
  | Sum.inr true, j => decide (j.val < 1)

theorem card_spec_tri (q t u v : ℕ) (ht : 1 ≤ t) (hu : u ≤ t) (hv : v ≤ t) :
    Fintype.card (Tri (specA q t v) (specB q t u)) = q * (t * t) + t * u + v := by
  rw [card_tri, Fintype.sum_sum_type, Fintype.sum_bool]
  have h0 : Fintype.card {j : Fin t // (j : ℕ) = 0} = 1 := by
    simpa using Fintype.card_fin_lt_of_le (n := t) (m := 1) ht
  simp [specA, specB, Fintype.card_fin_lt_of_le hu, Fintype.card_fin_lt_of_le hv, h0]
  ring

theorem f_le_decomposition (q t u v : ℕ) (ht : 2 ≤ t) (hu : u ≤ t) (hv : v ≤ t) :
    f (q * (t * t) + t * u + v + 2) ≤ (q * (t * t) + t * u + v) + 2 * t + (q + 2) := by
  have : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
  have hA : ∀ i : Fin t, ∃ i', i' ≠ i := by
    intro i
    by_cases hi : i.val = 0
    · exact ⟨⟨1, by omega⟩, by intro he; have := congrArg Fin.val he; simp_all⟩
    · exact ⟨⟨0, by omega⟩, by intro he; have := congrArg Fin.val he; simp_all⟩
  have hmem := exists_member (specA q t v) (specB q t u) hA hA
  have hcard : Fintype.card (Fin t) + Fintype.card (Fin t) + Fintype.card (Fin q ⊕ Bool) +
      Fintype.card (Tri (specA q t v) (specB q t u)) =
      (q * (t * t) + t * u + v) + 2 * t + (q + 2) := by
    rw [card_spec_tri q t u v (by omega) hu hv]
    simp
    ring
  have hmem' : _ ∈ {n | ∃ Γ : ECGraph (Fin n) ℕ,
      InHatF (Fintype.card (Tri (specA q t v) (specB q t u)) + 2) Γ} := hmem
  rw [hcard, card_spec_tri q t u v (by omega) hu hv] at hmem'
  exact Nat.sInf_le hmem'

end Variable

/-! Integer cube-root decomposition. -/

theorem cube_root_exists (M : ℕ) : ∃ t : ℕ, M ≤ t ^ 3 :=
  ⟨M, by
    rcases Nat.eq_zero_or_pos M with h | h
    · simp [h]
    · calc M = M ^ 1 := (pow_one M).symm
        _ ≤ M ^ 3 := Nat.pow_le_pow_right h (by norm_num)⟩

/-- For `M ≥ 2` and `t` the least integer with `M ≤ t³`, the bound `f (M + 2) ≤ M + 2 + 3 t`. -/
theorem f_le_cube_root (M : ℕ) (hM : 2 ≤ M) :
    f (M + 2) ≤ M + 2 + 3 * Nat.find (cube_root_exists M) := by
  classical
  set t := Nat.find (cube_root_exists M) with ht_def
  have hMt : M ≤ t ^ 3 := Nat.find_spec (cube_root_exists M)
  have ht2 : 2 ≤ t := by
    by_contra h
    have h1 : t ^ 3 ≤ 1 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  set q := M / (t * t)
  set r := M % (t * t)
  set u := r / t
  set v := r % t
  have hpos : 0 < t := by omega
  have htt : 0 < t * t := Nat.mul_pos hpos hpos
  have hMdec : M = q * (t * t) + t * u + v := by
    have h1 := Nat.div_add_mod M (t * t)
    have h2 := Nat.div_add_mod r t
    simp only [q, r, u, v] at *
    nlinarith [h1, h2]
  have hq : q ≤ t := by
    apply Nat.div_le_of_le_mul
    calc M ≤ t ^ 3 := hMt
      _ = t * t * t := by ring
  have hr : r < t * t := Nat.mod_lt _ htt
  have hu : u ≤ t := by
    have : u < t := Nat.div_lt_of_lt_mul hr
    omega
  have hv : v ≤ t := (Nat.mod_lt _ hpos).le
  have := Variable.f_le_decomposition q t u v ht2 hu hv
  rw [← hMdec] at this
  omega

/-- Bridge from the integer cube root to the real `⌈(k - 2)^(1/3)⌉`. -/
theorem find_le_ceil_cbrt (M : ℕ) :
    (Nat.find (cube_root_exists M) : ℤ) ≤ ⌈(M : ℝ) ^ ((1 : ℝ) / 3)⌉ := by
  classical
  set t := Nat.find (cube_root_exists M) with ht_def
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0]
    exact Int.ceil_nonneg (by positivity)
  have hmin : ¬ M ≤ (t - 1) ^ 3 := Nat.find_min (cube_root_exists M) (by omega)
  rw [Int.le_ceil_iff]
  by_contra hle'
  have hle := not_lt.mp hle'
  have hy0 : (0 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hcube : ((M : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = M := by
    rw [one_div]
    exact_mod_cast Real.rpow_inv_natCast_pow (Nat.cast_nonneg M) (by norm_num : (3 : ℕ) ≠ 0)
  have hcast : ((t : ℤ) : ℝ) - 1 = ((t - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hcast] at hle
  have h3 : ((M : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 ≤ ((t - 1 : ℕ) : ℝ) ^ 3 :=
    pow_le_pow_left₀ hy0 hle 3
  rw [hcube] at h3
  exact hmin (by exact_mod_cast h3)

/-- The every-k theorem of the written proof: for all `k ≥ 4`,
`f k ≤ k + 3 ⌈(k - 2)^(1/3)⌉`. -/
theorem f_le_all_k (k : ℕ) (hk : 4 ≤ k) :
    (f k : ℤ) ≤ k + 3 * ⌈((k : ℝ) - 2) ^ ((1 : ℝ) / 3)⌉ := by
  obtain ⟨M, rfl⟩ : ∃ M, k = M + 2 := ⟨k - 2, by omega⟩
  have h1 := f_le_cube_root M (by omega)
  have h2 := find_le_ceil_cbrt M
  have hr : ((M + 2 : ℕ) : ℝ) - 2 = (M : ℝ) := by push_cast; ring
  rw [hr]
  have h1' : (f (M + 2) : ℤ) ≤ (M + 2 : ℕ) + 3 * (Nat.find (cube_root_exists M) : ℤ) := by
    exact_mod_cast h1
  linarith

/-! Infinitely many violations of the printed formula: every `t ≥ 8`. -/

theorem conjFormula_family_lower (t : ℕ) (ht : 8 ≤ t) :
    (t ^ 3 + 3 * t : ℤ) < conjFormula (t ^ 3 + 2) := by
  unfold conjFormula
  push_cast
  have htR : (8 : ℝ) ≤ t := by exact_mod_cast ht
  have hprod : 0 ≤ ((t : ℝ) - 8) * t * (t - 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hpoly : (6 * (t : ℝ) - 3) ^ 2 < 4 * ((t : ℝ) ^ 3 + 2) - 3 := by nlinarith
  have hsqrt : 6 * (t : ℝ) - 3 < Real.sqrt (4 * ((t : ℝ) ^ 3 + 2) - 3) :=
    (Real.lt_sqrt (by linarith)).mpr hpoly
  have hceil : ((3 * (t : ℤ) - 2 : ℤ) : ℝ) <
      (-1 + Real.sqrt (4 * ((t : ℝ) ^ 3 + 2) - 3)) / 2 := by
    push_cast
    linarith
  have := Int.lt_ceil.mpr hceil
  linarith

theorem conj_fails_on_family (t : ℕ) (ht : 8 ≤ t) :
    (f (t ^ 3 + 2) : ℤ) < conjFormula (t ^ 3 + 2) := by
  have h1 := f_family_le t (by omega)
  have h1' : (f (t ^ 3 + 2) : ℤ) ≤ t ^ 3 + 3 * t := by exact_mod_cast h1
  have h2 := conjFormula_family_lower t ht
  linarith

#print axioms Variable.exists_member
#print axioms f_le_cube_root
#print axioms f_le_all_k
#print axioms conj_fails_on_family

end Rainbow381790
```

### `RainbowMain.lean`

```lean
import RainbowEndpoint
import RainbowAllK

/-! Summary module: the literal definitions, every endpoint statement, and their axioms. -/
namespace Rainbow381790

/-- Sanity check with the source's palette `ℕ`: a rainbow `K_{k+1}` coloured injectively
by natural numbers is not in the class. -/
theorem rainbow_K_succ_not_mem_nat (k : ℕ) :
    ¬ InHatF k (recolour (rainbowComplete (Fin (k + 1)))
      (finiteColourCode (Sym2 (Fin (k + 1))))) := fun h =>
  h.1 ((recolour_clique _ _ (finiteColourCode_injective _) _ _ _).mpr
    (rainbowComplete_clique (k + 1)))

#print ECGraph
#print RainbowCliqueIn
#print InHatF
#print f
#print conjFormula

#check @chlt_conj_5_1_false
#check @f_514_le
#check @f_514_lt_conjFormula
#check @conjFormula_514
#check @explicit_514_member
#check @tripartite_family
#check @f_family_le
#check @conj_fails_on_family
#check @f_le_all_k
#check @f_lower_bound
#check @f_minimum_attained
#check @rainbow_K_succ_not_mem
#check @rainbow_K_succ_not_mem_nat
#check @zero_mem_minimization_set

#print axioms chlt_conj_5_1_false
#print axioms f_514_le
#print axioms f_514_lt_conjFormula
#print axioms conjFormula_514
#print axioms explicit_514_member
#print axioms tripartite_family
#print axioms f_family_le
#print axioms conj_fails_on_family
#print axioms f_le_all_k
#print axioms f_lower_bound
#print axioms f_minimum_attained
#print axioms rainbow_K_succ_not_mem
#print axioms rainbow_K_succ_not_mem_nat
#print axioms zero_mem_minimization_set

end Rainbow381790
```

