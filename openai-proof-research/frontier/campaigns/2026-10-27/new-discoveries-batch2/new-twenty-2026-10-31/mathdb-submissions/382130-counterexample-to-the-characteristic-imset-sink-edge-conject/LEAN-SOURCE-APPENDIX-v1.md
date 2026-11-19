# Literal Lean source appendix v1

Pinned Lean 4.34.1. Modules appear in build order. No generated or omitted proof text.

<!-- BEGIN SOURCE Finite.lean sha256=1d52b90315beb3be30f7ac3e7e9c12c084758be199a765a84370e10361ce33a4 -->
```lean
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment

namespace ImsetSink
abbrev Arrow (n : ℕ) := Fin n → Fin n → Bool
structure DAG (n : ℕ) where
  arrow : Arrow n
  rank : Fin n → ℕ
  forward : ∀ u v, arrow u v = true → rank u < rank v

def skeleton {n} (h : Arrow n) (u v : Fin n) : Bool := h u v || h v u
def sink {n} (h : Arrow n) (i u v : Fin n) : Bool :=
  if v = i then skeleton h u v else if u = i then false else h u v

def coord (n : ℕ) := {s : Finset (Fin n) // 2 ≤ s.card}
def code {n} (h : Arrow n) (s : Finset (Fin n)) : ℕ :=
  if ∃ v ∈ s, ∀ u ∈ s, u ≠ v → h u v = true then 1 else 0
noncomputable def imset {n} (h : Arrow n) : coord n → ℝ := fun s => (code h s.val : ℝ)
noncomputable def CIM {n} (g : Arrow n) : Set (coord n → ℝ) :=
  convexHull ℝ {x | ∃ h : DAG n, skeleton h.arrow = g ∧ imset h.arrow = x}

def fromEdges (es : List (Fin 5 × Fin 5)) : Arrow 5 := fun u v => decide ((u,v) ∈ es)
def C : Arrow 5 := fromEdges [(1,0),(1,3),(1,4),(2,0),(2,4),(3,0),(3,2),(4,0)]
def D : Arrow 5 := fromEdges [(0,3),(1,0),(1,3),(1,4),(2,0),(2,3),(2,4),(4,0)]
def A : Arrow 5 := fromEdges [(0,4),(1,0),(1,4),(2,0),(2,4),(3,0),(3,1),(3,2)]
def B : Arrow 5 := fromEdges [(1,0),(1,3),(1,4),(2,0),(2,3),(2,4),(3,0),(4,0)]
def rankC : Fin 5 → ℕ := ![4,0,2,1,3]
def rankD : Fin 5 → ℕ := ![3,0,1,4,2]
def rankA : Fin 5 → ℕ := ![3,1,2,0,4]
def rankB : Fin 5 → ℕ := ![4,0,1,2,3]
def dagC : DAG 5 := ⟨C,rankC,by decide⟩
def dagD : DAG 5 := ⟨D,rankD,by decide⟩
def dagA : DAG 5 := ⟨A,rankA,by decide⟩
def dagB : DAG 5 := ⟨B,rankB,by decide⟩
theorem same_skeleton : skeleton C = skeleton D ∧ skeleton C = skeleton A ∧ skeleton C = skeleton B := by decide
theorem sink_C : sink C 3 = D := by decide

/-- Source labels are 1,...,5, transported by k ↦ k-1. -/
abbrev Label := {k : ℕ // 1 ≤ k ∧ k ≤ 5}
def labelToFin (k : Label) : Fin 5 := ⟨k.val - 1, by have hk := k.property; omega⟩
def finToLabel (k : Fin 5) : Label := ⟨k.val+1, by omega⟩
theorem labels_left (k : Label) : finToLabel (labelToFin k) = k := by
  apply Subtype.ext; have hk := k.property; dsimp [finToLabel,labelToFin]; omega
theorem labels_right (k : Fin 5) : labelToFin (finToLabel k) = k := by
  apply Fin.ext; simp [labelToFin,finToLabel]

/-- All subsets, including every zero coordinate, are checked by kernel reduction. -/
theorem code_balance : ∀ s : Finset (Fin 5), code C s + code D s = code A s + code B s := by decide

theorem imset_balance : imset C + imset D = imset A + imset B := by
  funext s
  have h := code_balance s.val
  change (code C s.val : ℝ) + code D s.val = (code A s.val : ℝ) + code B s.val
  exact_mod_cast h

noncomputable def q : coord 5 := ⟨{1,2,3}, by decide⟩
noncomputable def f : coord 5 := ⟨{0,3,4}, by decide⟩
theorem values_q : imset C q = 0 ∧ imset D q = 1 ∧ imset A q = 0 := by norm_num [imset,q,code,C,D,A,fromEdges]
theorem values_f : imset C f = 1 ∧ imset D f = 0 ∧ imset A f = 0 := by norm_num [imset,f,code,C,D,A,fromEdges]

theorem A_outside : imset A ∉ segment ℝ (imset C) (imset D) := by
  rintro ⟨a,b,ha,hb,hab,he⟩
  have hq := congrFun he q
  have hf := congrFun he f
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hq hf
  rw [values_q.1, values_q.2.1, values_q.2.2] at hq
  rw [values_f.1, values_f.2.1, values_f.2.2] at hf
  norm_num at hq hf
  linarith

#print axioms ImsetSink.imset_balance
#print axioms ImsetSink.A_outside
end ImsetSink
```
<!-- END SOURCE Finite.lean -->

<!-- BEGIN SOURCE Convex.lean sha256=15f27955b00de3f681a05b05fa92c6c9b705db03327acf5a97067f1751886b0f -->
```lean
import Finite
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
namespace ImsetSink
/-- A convex subset with the defining face property for strict convex combinations. -/
def Face {E : Type*} [AddCommGroup E] [Module ℝ E] (P F : Set E) : Prop :=
  Convex ℝ F ∧ F ⊆ P ∧ ∀ a ∈ P, ∀ b ∈ P, ∀ t : ℝ,
    0 < t → t < 1 → (1-t) • a + t • b ∈ F → a ∈ F ∧ b ∈ F
/-- An edge is a face of affine dimension one. -/
def Edge {E : Type*} [AddCommGroup E] [Module ℝ E] (P F : Set E) : Prop :=
  Face P F ∧ Module.finrank ℝ (vectorSpan ℝ F) = 1

theorem four_point_nonface {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {c d a b : E} (ha : a ∈ P) (hb : b ∈ P)
    (h : a + b = c + d) (hout : a ∉ segment ℝ c d) :
    ¬ Face P (segment ℝ c d) := by
  intro hf
  have hm : (1-(1/2:ℝ)) • a + (1/2:ℝ) • b ∈ segment ℝ c d := by
    have he : (1-(1/2:ℝ)) • a + (1/2:ℝ) • b = (1/2:ℝ) • c + (1/2:ℝ) • d := by
      norm_num
      rw [← smul_add, h, smul_add]
    rw [he]
    exact ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩
  exact hout (hf.2.2 a ha b hb (1/2) (by norm_num) (by norm_num) hm).1

theorem member_C : imset C ∈ CIM (skeleton C) :=
  subset_convexHull ℝ _ ⟨dagC,rfl,rfl⟩
theorem member_D : imset D ∈ CIM (skeleton C) :=
  subset_convexHull ℝ _ ⟨dagD,same_skeleton.1.symm,rfl⟩
theorem member_A : imset A ∈ CIM (skeleton C) :=
  subset_convexHull ℝ _ ⟨dagA,same_skeleton.2.1.symm,rfl⟩
theorem member_B : imset B ∈ CIM (skeleton C) :=
  subset_convexHull ℝ _ ⟨dagB,same_skeleton.2.2.symm,rfl⟩
theorem witness_nonface : ¬ Face (CIM (skeleton C)) (segment ℝ (imset C) (imset D)) :=
  four_point_nonface member_A member_B imset_balance.symm A_outside
theorem witness_nonedge : ¬ Edge (CIM (skeleton C)) (segment ℝ (imset C) (imset D)) :=
  fun h => witness_nonface h.1
#print axioms ImsetSink.four_point_nonface
#print axioms ImsetSink.witness_nonedge
end ImsetSink
```
<!-- END SOURCE Convex.lean -->

<!-- BEGIN SOURCE Bridges.lean sha256=0ca78f25eeddc9d19fcf45de35f5db29fc831f5319b89b83e8805a6c98448d03 -->
```lean
import Finite
namespace ImsetSink
def parents {n} (h : Arrow n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => h u v = true)
theorem parent_formula {n} (h : Arrow n) (s : Finset (Fin n)) :
    code h s = if ∃ v ∈ s, s ⊆ parents h v ∪ {v} then 1 else 0 := by
  unfold code
  congr 1
  apply propext
  constructor
  · rintro ⟨v,hv,hh⟩
    refine ⟨v,hv,?_⟩
    intro u hu
    by_cases he : u = v
    · simp [he]
    · simp [parents, hh u hu he]
  · rintro ⟨v,hv,hh⟩
    refine ⟨v,hv,?_⟩
    intro u hu he
    have hm := hh hu
    simpa [parents,he] using hm

def Acyclic {n} (h : Arrow n) : Prop := ∀ v, ¬ Relation.TransGen (fun u v => h u v = true) v v
theorem DAG.acyclic {n} (h : DAG n) : Acyclic h.arrow := by
  intro v ht
  have hr : ∀ {u v}, Relation.TransGen (fun u v => h.arrow u v = true) u v → h.rank u < h.rank v := by
    intro u v hp
    induction hp with
    | single he => exact h.forward _ _ he
    | tail hp he ih => exact lt_trans ih (h.forward _ _ he)
  exact (lt_irrefl _ (hr ht))

def R : Finset (Finset (Fin 5)) :=
 {{0,1},{0,2},{0,3},{0,4},{1,3},{1,4},{2,3},{2,4},
 {0,1,2},{0,1,3},{0,1,4},{0,2,3},{0,2,4},{1,2,4},{0,1,2,3},{0,1,2,4}}
def F : Finset (Finset (Fin 5)) := {{0,3,4},{0,1,3,4},{0,2,3,4},{0,1,2,3,4}}
def Q : Finset (Finset (Fin 5)) := {{1,2,3}}
def Z : Finset (Finset (Fin 5)) := {{1,2},{3,4},{1,3,4},{2,3,4},{1,2,3,4}}
theorem full_partition :
    (R ∪ F ∪ Q ∪ Z).card = 26 ∧
    (∀ s : Finset (Fin 5), 2 ≤ s.card ↔ s ∈ R ∪ F ∪ Q ∪ Z) ∧
    Disjoint R F ∧ Disjoint R Q ∧ Disjoint R Z ∧ Disjoint F Q ∧ Disjoint F Z ∧ Disjoint Q Z := by decide
set_option maxRecDepth 10000 in
theorem full_table : ∀ s : Finset (Fin 5), 2 ≤ s.card →
    code C s = (if s ∈ R ∪ F then 1 else 0) ∧
    code D s = (if s ∈ R ∪ Q then 1 else 0) ∧
    code A s = (if s ∈ R then 1 else 0) ∧
    code B s = (if s ∈ R ∪ F ∪ Q then 1 else 0) := by decide
#print axioms ImsetSink.parent_formula
#print axioms ImsetSink.DAG.acyclic
#print axioms ImsetSink.full_table
end ImsetSink
```
<!-- END SOURCE Bridges.lean -->

<!-- BEGIN SOURCE Semantics.lean sha256=11df907fddb744c00ec24e77d2b6e680d2893a7d1278330141b6a9213c3276af -->
```lean
import Finite
namespace ImsetSink
/-- A simple undirected path with k interior vertices; k<n suffices for every simple path. -/
def AdjacentPath {n} (h : Arrow n) {k : Fin n} (p : Fin (k.val+2) → Fin n) : Prop :=
  ∀ t : Fin (k.val+1), skeleton h (p ⟨t.val,by omega⟩) (p ⟨t.val+1,by omega⟩) = true

def Collider {n} (h : Arrow n) {k : Fin n} (p : Fin (k.val+2) → Fin n) (t : Fin k.val) : Prop :=
  h (p ⟨t.val,by omega⟩) (p ⟨t.val+1,by omega⟩) = true ∧
  h (p ⟨t.val+2,by omega⟩) (p ⟨t.val+1,by omega⟩) = true
instance {n} (h : Arrow n) {k : Fin n} (p : Fin (k.val+2) → Fin n) (t : Fin k.val) : Decidable (Collider h p t) := inferInstanceAs (Decidable (_ ∧ _))
instance {n} (h : Arrow n) {k : Fin n} (p : Fin (k.val+2) → Fin n) : Decidable (AdjacentPath h p) := inferInstanceAs (Decidable (∀ _t : Fin (k.val+1), _))

def Reach {n} (h : Arrow n) := Relation.ReflTransGen (fun u v => h u v = true)
def Active {n} (h : Arrow n) {k : Fin n} (p : Fin (k.val+2) → Fin n) (z : Finset (Fin n)) : Prop :=
  ∀ t : Fin k.val, if Collider h p t then ∃ v ∈ z, Reach h (p ⟨t.val+1,by omega⟩) v else p ⟨t.val+1,by omega⟩ ∉ z

def Connected {n} (h : Arrow n) (x y : Fin n) (z : Finset (Fin n)) : Prop :=
  ∃ k : Fin n, ∃ p : Fin (k.val+2) → Fin n,
    Function.Injective p ∧ p 0 = x ∧ p ⟨k.val+1,by omega⟩ = y ∧ AdjacentPath h p ∧ Active h p z

def DSeparated {n} (h : Arrow n) (x y z : Finset (Fin n)) : Prop :=
  ∀ a ∈ x, ∀ b ∈ y, ¬ Connected h a b z

def MarkovEquivalent {n} (h j : Arrow n) : Prop :=
  ∀ x y z : Finset (Fin n), Disjoint x y → Disjoint x z → Disjoint y z →
    (DSeparated h x y z ↔ DSeparated j x y z)

theorem active_empty {n} (h : Arrow n) {k : Fin n} (p : Fin (k.val+2) → Fin n) :
    Active h p ∅ ↔ ∀ t, ¬ Collider h p t := by
  simp [Active]

theorem D_noin1 : ∀ u, D u 1 = false := by decide
theorem D_noin2 : ∀ u, D u 2 = false := by decide

theorem D_collider : ∀ k : Fin 5, ∀ p : Fin (k.val+2) → Fin 5,
    Function.Injective p → p 0 = 1 → p ⟨k.val+1,by omega⟩ = 2 → AdjacentPath D p →
    ∃ t, Collider D p t := by
  intro k p _ hx hy hp
  by_contra hn
  have hnc : ∀ t, ¬ Collider D p t := by simpa only [not_exists] using hn
  have forward : ∀ t : ℕ, (ht : t ≤ k.val) →
      D (p ⟨t,by omega⟩) (p ⟨t+1,by omega⟩) = true := by
    intro t
    induction t with
    | zero =>
      intro ht
      have he := hp ⟨0,by omega⟩
      change (D (p 0) (p ⟨1,by omega⟩) || D (p ⟨1,by omega⟩) (p 0)) = true at he
      rw [hx,D_noin1] at he
      simpa [hx] using he
    | succ t ih =>
      intro ht
      have prev := ih (by omega)
      have nc := hnc ⟨t,by omega⟩
      have he := hp ⟨t+1,by omega⟩
      change (D (p ⟨t+1,by omega⟩) (p ⟨t+2,by omega⟩) || D (p ⟨t+2,by omega⟩) (p ⟨t+1,by omega⟩)) = true at he
      cases hv : D (p ⟨t+1,by omega⟩) (p ⟨t+2,by omega⟩) with
      | false =>
        simp only [hv, Bool.false_or] at he
        exact False.elim (nc ⟨prev,he⟩)
      | true => rfl
  have he := forward k.val (le_refl _)
  rw [hy,D_noin2] at he
  contradiction

theorem D_disconnected : ¬ Connected D 1 2 ∅ := by
  rintro ⟨k,p,hi,hx,hy,hp,ha⟩
  obtain ⟨t,ht⟩ := D_collider k p hi hx hy hp
  exact (active_empty D p).mp ha t ht

theorem C_connected : Connected C 1 2 ∅ := by
  refine ⟨1, ![1,3,2], ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · rfl
  · rfl
  · decide
  · rw [active_empty]; decide

theorem singleton_separation {n} (h : Arrow n) (x y : Fin n) (z : Finset (Fin n)) :
    DSeparated h {x} {y} z ↔ ¬ Connected h x y z := by simp [DSeparated]
theorem witness_not_ME : ¬ MarkovEquivalent C D := by
  intro h
  have he := h {1} {2} ∅ (by decide) (by simp) (by simp)
  rw [singleton_separation, singleton_separation] at he
  exact he.mpr D_disconnected C_connected
#print axioms ImsetSink.D_collider
#print axioms ImsetSink.witness_not_ME
end ImsetSink
```
<!-- END SOURCE Semantics.lean -->

<!-- BEGIN SOURCE SourceNegation.lean sha256=702e47e3299643bb57e2617c9b56165222a20384b5b2ec875d7e13168451045e -->
```lean
import Convex
import Bridges
import Semantics
namespace ImsetSink
/-- Real convex hull of every acyclic orientation, with no rank certificate restriction. -/
noncomputable def SourceCIM {n} (g : Arrow n) : Set (coord n → ℝ) :=
  convexHull ℝ {x | ∃ h : Arrow n, Acyclic h ∧ skeleton h = g ∧ imset h = x}
def Simple {n} (g : Arrow n) : Prop :=
  (∀ u, g u u = false) ∧ (∀ u v, g u v = g v u)
/-- Literal arbitrary-n source predicate. -/
def UniversalSinkEdge : Prop := ∀ n : ℕ, ∀ g : Arrow n, Simple g →
  ∀ h : Arrow n, Acyclic h → skeleton h = g → ∀ i : Fin n,
  ¬ MarkovEquivalent h (sink h i) →
  Edge (SourceCIM g) (segment ℝ (imset h) (imset (sink h i)))

theorem source_nonface : ¬ Face (SourceCIM (skeleton C)) (segment ℝ (imset C) (imset D)) := by
  apply four_point_nonface (a := imset A) (b := imset B)
  · exact subset_convexHull ℝ _ ⟨A,dagA.acyclic,same_skeleton.2.1.symm,rfl⟩
  · exact subset_convexHull ℝ _ ⟨B,dagB.acyclic,same_skeleton.2.2.symm,rfl⟩
  · exact imset_balance.symm
  · exact A_outside

theorem source_nonedge : ¬ Edge (SourceCIM (skeleton C)) (segment ℝ (imset C) (imset D)) :=
  fun h => source_nonface h.1

theorem source_negation : ¬ UniversalSinkEdge := by
  intro h
  have hh := h 5 (skeleton C) (by unfold Simple; decide) C dagC.acyclic rfl 3
  rw [sink_C] at hh
  exact source_nonedge (hh witness_not_ME)

theorem explicit_five_counterexample :
  Acyclic C ∧ Acyclic D ∧ skeleton C = skeleton D ∧ sink C 3 = D ∧
  ¬ MarkovEquivalent C D ∧
  ¬ Edge (SourceCIM (skeleton C)) (segment ℝ (imset C) (imset D)) :=
  ⟨dagC.acyclic,dagD.acyclic,same_skeleton.1,sink_C,witness_not_ME,source_nonedge⟩

/-- Numeric source labels transported to zero-based Fin 5. -/
theorem source_C_labels : ∀ u v : Fin 5, C u v = decide
    (((finToLabel u).val,(finToLabel v).val) ∈
    ([(2,1),(2,4),(2,5),(3,1),(3,5),(4,1),(4,3),(5,1)] : List (ℕ × ℕ))) := by decide
theorem source_D_labels : ∀ u v : Fin 5, D u v = decide
    (((finToLabel u).val,(finToLabel v).val) ∈
    ([(1,4),(2,1),(2,4),(2,5),(3,1),(3,4),(3,5),(5,1)] : List (ℕ × ℕ))) := by decide
theorem source_A_labels : ∀ u v : Fin 5, A u v = decide
    (((finToLabel u).val,(finToLabel v).val) ∈
    ([(1,5),(2,1),(2,5),(3,1),(3,5),(4,1),(4,2),(4,3)] : List (ℕ × ℕ))) := by decide
theorem source_B_labels : ∀ u v : Fin 5, B u v = decide
    (((finToLabel u).val,(finToLabel v).val) ∈
    ([(2,1),(2,4),(2,5),(3,1),(3,4),(3,5),(4,1),(5,1)] : List (ℕ × ℕ))) := by decide
#print axioms ImsetSink.source_negation
#print axioms ImsetSink.explicit_five_counterexample
#print axioms ImsetSink.source_C_labels
end ImsetSink
```
<!-- END SOURCE SourceNegation.lean -->

<!-- BEGIN SOURCE CertificateAudit.lean sha256=84a18ee27dda815eea6c08c426acf5ce415c63c690ba3b1f838d7e62bd3bff38 -->
```lean
import SourceNegation
namespace ImsetSink
theorem source_member_C : imset C ∈ SourceCIM (skeleton C) :=
  subset_convexHull ℝ _ ⟨C,dagC.acyclic,rfl,rfl⟩
theorem source_member_D : imset D ∈ SourceCIM (skeleton C) :=
  subset_convexHull ℝ _ ⟨D,dagD.acyclic,same_skeleton.1.symm,rfl⟩
theorem source_member_A : imset A ∈ SourceCIM (skeleton C) :=
  subset_convexHull ℝ _ ⟨A,dagA.acyclic,same_skeleton.2.1.symm,rfl⟩
theorem source_member_B : imset B ∈ SourceCIM (skeleton C) :=
  subset_convexHull ℝ _ ⟨B,dagB.acyclic,same_skeleton.2.2.symm,rfl⟩
theorem all_parents : ∀ v : Fin 5,
    parents C v = ![{1,2,3,4},∅,{3},{1},{1,2}] v ∧
    parents D v = ![{1,2,4},∅,∅,{0,1,2},{1,2}] v ∧
    parents A v = ![{1,2,3},{3},{3},∅,{0,1,2}] v ∧
    parents B v = ![{1,2,3,4},∅,∅,{1,2},{1,2}] v := by decide
theorem all_orders : ∀ p : Fin 5,
    rankC (![1,3,2,4,0] p) = p.val ∧ rankD (![1,2,4,0,3] p) = p.val ∧
    rankA (![3,1,2,0,4] p) = p.val ∧ rankB (![1,2,3,4,0] p) = p.val := by decide
theorem source_imset_formula {n} (h : Arrow n) (s : coord n) :
    imset h s = ((if ∃ v ∈ s.val, s.val ⊆ parents h v ∪ {v} then 1 else 0 : ℕ) : ℝ) := by
  exact congrArg (fun k : ℕ => (k : ℝ)) (parent_formula h s.val)
#print axioms ImsetSink.source_negation
#print axioms ImsetSink.explicit_five_counterexample
#print axioms ImsetSink.source_nonface
#print axioms ImsetSink.source_member_C
#print axioms ImsetSink.source_member_D
#print axioms ImsetSink.source_member_A
#print axioms ImsetSink.source_member_B
#print axioms ImsetSink.source_imset_formula
#print axioms ImsetSink.all_parents
#print axioms ImsetSink.all_orders
#print axioms ImsetSink.sink_C
#print axioms ImsetSink.same_skeleton
#print axioms ImsetSink.full_partition
#print axioms ImsetSink.full_table
#print axioms ImsetSink.active_empty
#print axioms ImsetSink.singleton_separation
#print axioms ImsetSink.witness_not_ME
#print axioms ImsetSink.labels_left
#print axioms ImsetSink.labels_right
#print axioms ImsetSink.source_C_labels
#print axioms ImsetSink.source_D_labels
#print axioms ImsetSink.source_A_labels
#print axioms ImsetSink.source_B_labels
end ImsetSink
```
<!-- END SOURCE CertificateAudit.lean -->
