# Lean source appendix — MathDB 370688

Status: COMPLETE. All files below are in dependency order and byte-identical to src/.

### `MatchingDefinitions.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-- Compatibility spelling: Mathlib 4.34 calls adjacent-pair chains `IsChain`. -/
abbrev List.Chain' {α : Type*} (L : List α) (R : α → α → Prop) : Prop := L.IsChain R

namespace Matching370688
open Finset

/-- Source perfect matchings represented by their unique partner involution. -/
abbrev PM (n : ℕ) := {p : Fin n → Fin n // Function.Involutive p ∧ ∀ v, p v ≠ v}

namespace PM
variable {n : ℕ}
def E (M : PM n) : Finset (Sym2 (Fin n)) := univ.image (fun v => s(v, M.val v))

lemma inv (M : PM n) (v : Fin n) : M.val (M.val v) = v := M.property.1 v
lemma free (M : PM n) (v : Fin n) : M.val v ≠ v := M.property.2 v

lemma edge_mem (M : PM n) (v : Fin n) : s(v, M.val v) ∈ M.E :=
  mem_image.mpr ⟨v, mem_univ _, rfl⟩

lemma edge_at (M : PM n) {e : Sym2 (Fin n)} (he : e ∈ M.E) {v : Fin n}
    (hv : v ∈ e) : e = s(v, M.val v) := by
  obtain ⟨u, _, rfl⟩ := mem_image.mp he
  rcases (Sym2.mem_iff.mp hv) with h | h
  · subst v
    rfl
  · subst v
    rw [M.inv, Sym2.eq_swap]

lemma not_diag (M : PM n) : ∀ e ∈ M.E, ¬ e.IsDiag := by
  intro e he
  obtain ⟨v, _, rfl⟩ := mem_image.mp he
  simpa only [Sym2.mk_isDiag_iff] using Ne.symm (M.free v)

lemma cover (M : PM n) (v : Fin n) : ∃! e, e ∈ M.E ∧ v ∈ e := by
  refine ⟨s(v, M.val v), ⟨M.edge_mem v, by simp⟩, ?_⟩
  intro e he
  exact M.edge_at he.1 he.2

lemma mem_E_iff (M : PM n) (u v : Fin n) : s(u,v) ∈ M.E ↔ M.val u = v := by
  constructor
  · intro h
    have he := M.edge_at h (by simp : u ∈ s(u,v))
    have hv : v ∈ s(u, M.val u) := by rw [← he]; simp
    rcases Sym2.mem_iff.mp hv with hv | hv
    · subst v
      exact False.elim (M.not_diag _ h (by simp))
    · exact hv.symm
  · intro h
    rw [← h]
    exact M.edge_mem u
end PM

/-- Literal source realizability; no ordering or positivity is built into this predicate. -/
def Realizes {n : ℕ} (d : Fin n → ℕ) (M : PM n) : Prop :=
  ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
    (∀ v, G.degree v = d v) ∧ ∀ e ∈ M.E, e ∈ G.edgeSet

/-- Source §5 preorder, quantifying over weakly decreasing natural degree vectors. -/
def Prec {n : ℕ} (N M : PM n) : Prop :=
  ∀ d : Fin n → ℕ, Antitone d → Realizes d M → Realizes d N

/-- The three literal directed replacements in source §5. -/
def IsSwitchOf {n : ℕ} (N M : PM n) : Prop :=
  ∃ w x y z : Fin n, w < x ∧ x < y ∧ y < z ∧
    ((M.E \ N.E = {s(w,x), s(y,z)} ∧ N.E \ M.E = {s(w,y), s(x,z)}) ∨
     (M.E \ N.E = {s(w,y), s(x,z)} ∧ N.E \ M.E = {s(w,z), s(x,y)}) ∨
     (M.E \ N.E = {s(w,x), s(y,z)} ∧ N.E \ M.E = {s(w,z), s(x,y)}))

/-- Required list endpoint, including both signs and switch directions. -/
def ChainConclusion {n : ℕ} (N M : PM n) : Prop :=
  ∃ L : List (PM n), L ≠ [] ∧ L.head? = some N ∧ L.getLast? = some M ∧
    L.Chain' (fun A B => Prec A B ∧ IsSwitchOf A B)

/-- The unproved universal target, a proposition rather than a theorem declaration. -/
def Conjecture11 : Prop := ∀ n (N M : PM n), Prec N M → ChainConclusion N M

variable {n : ℕ} {A B C M N : PM n} {d : Fin n → ℕ}

lemma realizes_lt (h : Realizes d M) (v : Fin n) : d v < n := by
  obtain ⟨G, inst, hd, _⟩ := h
  let := inst
  rw [← hd v]
  simpa using G.degree_lt_card_verts v

lemma realizes_pos (h : Realizes d M) (v : Fin n) : 1 ≤ d v := by
  obtain ⟨G, inst, hd, hM⟩ := h
  let := inst
  have ha : G.Adj v (M.val v) := hM _ (M.edge_mem v)
  have hm : M.val v ∈ G.neighborFinset v := by simpa using ha
  have hc := Finset.card_pos.mpr ⟨M.val v, hm⟩
  rw [G.card_neighborFinset_eq_degree, hd v] at hc
  exact hc

lemma prec_refl (M : PM n) : Prec M M := fun _ _ h => h
lemma prec_trans (h₁ : Prec A B) (h₂ : Prec B C) : Prec A C :=
  fun d hd h => h₁ d hd (h₂ d hd h)

lemma chainConclusion_refl (M : PM n) : ChainConclusion M M := by
  exact ⟨[M], by simp, by simp, by simp, by simp⟩

#print axioms PM.cover
#print axioms PM.not_diag
#print axioms realizes_pos
#print axioms realizes_lt
#print axioms chainConclusion_refl
end Matching370688
```

### `MatchingRepresentation.lean`

```lean
import MatchingDefinitions

namespace Matching370688
open Finset

/-- The review's literal finite-edge representation, used to certify that
partner involutions represent every source matching, not a proper subclass. -/
structure EdgePM (n : ℕ) where
  E : Finset (Sym2 (Fin n))
  not_diag : ∀ e ∈ E, ¬ e.IsDiag
  cover : ∀ v, ∃! e, e ∈ E ∧ v ∈ e

namespace EdgePM
variable {n : ℕ}
noncomputable def chosenEdge (Q : EdgePM n) (v : Fin n) : Sym2 (Fin n) := (Q.cover v).choose
lemma chosenEdge_spec (Q : EdgePM n) (v : Fin n) :
    Q.chosenEdge v ∈ Q.E ∧ v ∈ Q.chosenEdge v := (Q.cover v).choose_spec.1
noncomputable def partner (Q : EdgePM n) (v : Fin n) : Fin n :=
  (Sym2.mem_iff_exists.mp (Q.chosenEdge_spec v).2).choose
lemma chosenEdge_eq (Q : EdgePM n) (v : Fin n) : Q.chosenEdge v = s(v,Q.partner v) :=
  (Sym2.mem_iff_exists.mp (Q.chosenEdge_spec v).2).choose_spec
lemma partner_mem (Q : EdgePM n) (v : Fin n) : s(v,Q.partner v) ∈ Q.E := by
  rw [← Q.chosenEdge_eq]
  exact (Q.chosenEdge_spec v).1
lemma partner_free (Q : EdgePM n) (v : Fin n) : Q.partner v ≠ v := by
  intro h
  have hn := Q.not_diag _ (Q.partner_mem v)
  exact hn (by simp [h])
lemma edge_at (Q : EdgePM n) {e : Sym2 (Fin n)} (he : e ∈ Q.E) {v : Fin n} (hv : v ∈ e) :
    e = s(v,Q.partner v) := by
  have heq := (Q.cover v).choose_spec.2 e ⟨he,hv⟩
  exact heq.trans (Q.chosenEdge_eq v)
lemma partner_inv (Q : EdgePM n) : Function.Involutive Q.partner := by
  intro v
  have heq := Q.edge_at (Q.partner_mem v) (by simp : Q.partner v ∈ s(v,Q.partner v))
  have hv : v ∈ s(Q.partner v,Q.partner (Q.partner v)) := by rw [← heq]; simp
  rcases Sym2.mem_iff.mp hv with hv | hv
  · exact False.elim ((Q.partner_free v) hv.symm)
  · exact hv.symm
noncomputable def toPM (Q : EdgePM n) : PM n := ⟨Q.partner,Q.partner_inv,Q.partner_free⟩

lemma toPM_edges (Q : EdgePM n) : Q.toPM.E = Q.E := by
  ext e
  constructor
  · intro he
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp he
    exact Q.partner_mem v
  · intro he
    obtain ⟨⟨u,v⟩,rfl⟩ := Sym2.mk_surjective e
    have heq := Q.edge_at he (by simp : u ∈ s(u,v))
    rw [heq]
    exact Q.toPM.edge_mem u
end EdgePM

namespace PM
variable {n : ℕ}
def toEdgePM (M : PM n) : EdgePM n := ⟨M.E,M.not_diag,M.cover⟩
end PM

theorem all_edge_matchings_represented {n : ℕ} (Q : EdgePM n) :
    ∃ M : PM n, M.E = Q.E := ⟨Q.toPM,Q.toPM_edges⟩

#print axioms all_edge_matchings_represented
end Matching370688
```

### `MatchingFinite.lean`

```lean
import MatchingDefinitions

namespace Matching370688
open Finset
variable {n : ℕ}

def allEdges (n : ℕ) : Finset (Sym2 (Fin n)) := univ.filter (fun e => ¬ e.IsDiag)
def codeDegree (F : Finset (Sym2 (Fin n))) (v : Fin n) : ℕ :=
  (univ.filter (fun u => s(v,u) ∈ F ∧ v ≠ u)).card

def degreeSupport (M : PM n) : Finset (Fin n → ℕ) :=
  (((allEdges n).powerset.filter (fun F => M.E ⊆ F)).image codeDegree).filter Antitone

lemma degree_fromEdgeSet (F : Finset (Sym2 (Fin n))) (v : Fin n) :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).degree v = codeDegree F v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext u
  simp [SimpleGraph.fromEdgeSet_adj]

lemma realizes_code (d : Fin n → ℕ) (M : PM n) :
    Realizes d M ↔ ∃ F ∈ (allEdges n).powerset, M.E ⊆ F ∧ codeDegree F = d := by
  classical
  constructor
  · rintro ⟨G, inst, hd, hm⟩
    let := inst
    refine ⟨G.edgeFinset, mem_powerset.mpr ?_, ?_, ?_⟩
    · intro e he
      exact mem_filter.mpr ⟨mem_univ _, G.not_isDiag_of_mem_edgeFinset he⟩
    · intro e he
      exact SimpleGraph.mem_edgeFinset.mpr (hm e he)
    · funext v
      rw [← hd v, ← degree_fromEdgeSet]
      have hg : SimpleGraph.fromEdgeSet (G.edgeFinset : Set (Sym2 (Fin n))) = G := by simp
      simp only [← SimpleGraph.ncard_neighborSet]
      rw [hg]
  · rintro ⟨F, hF, hm, rfl⟩
    refine ⟨SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n))), inferInstance,
      degree_fromEdgeSet F, ?_⟩
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨hm he, M.not_diag e he⟩

lemma mem_degreeSupport (d : Fin n → ℕ) (M : PM n) :
    d ∈ degreeSupport M ↔ Antitone d ∧ Realizes d M := by
  rw [degreeSupport, mem_filter, realizes_code]
  constructor
  · rintro ⟨h, ha⟩
    obtain ⟨F, hF, hd⟩ := mem_image.mp h
    exact ⟨ha, F, (mem_filter.mp hF).1, (mem_filter.mp hF).2, hd⟩
  · rintro ⟨ha, F, hF, hm, hd⟩
    exact ⟨mem_image.mpr ⟨F, mem_filter.mpr ⟨hF, hm⟩, hd⟩, ha⟩

lemma prec_iff_support (N M : PM n) : Prec N M ↔ degreeSupport M ⊆ degreeSupport N := by
  constructor
  · intro h d hd
    obtain ⟨ha, hr⟩ := (mem_degreeSupport d M).mp hd
    exact (mem_degreeSupport d N).mpr ⟨ha, h d ha hr⟩
  · intro h d ha hr
    exact ((mem_degreeSupport d N).mp (h ((mem_degreeSupport d M).mpr ⟨ha,hr⟩))).2

/-- A finite decider certified equivalent to the literal, unbounded source preorder. -/
instance (N M : PM n) : Decidable (Prec N M) :=
  decidable_of_iff (degreeSupport M ⊆ degreeSupport N) (prec_iff_support N M).symm

instance (N M : PM n) : Decidable (IsSwitchOf N M) := by
  unfold IsSwitchOf
  infer_instance

#print axioms realizes_code
#print axioms prec_iff_support
end Matching370688
```

### `MatchingExtensions.lean`

```lean
import MatchingFinite

namespace Matching370688
open Finset
variable {n : ℕ}

/-- Enumerate only optional edges, and discard unsorted vectors before deduplication. -/
def extensionSupport (M : PM n) : Finset (Fin n → ℕ) :=
  ((((allEdges n) \ M.E).powerset).filter
    (fun F => Antitone (codeDegree (F ∪ M.E)))).image (fun F => codeDegree (F ∪ M.E))

lemma matching_edges_subset (M : PM n) : M.E ⊆ allEdges n := by
  intro e he
  exact mem_filter.mpr ⟨mem_univ _, M.not_diag e he⟩

lemma mem_extensionSupport (M : PM n) (d : Fin n → ℕ) :
    d ∈ extensionSupport M ↔ Antitone d ∧ Realizes d M := by
  classical
  rw [extensionSupport, mem_image, realizes_code]
  constructor
  · rintro ⟨F, hF, rfl⟩
    obtain ⟨hF, ha⟩ := mem_filter.mp hF
    have hf := mem_powerset.mp hF
    refine ⟨ha, F ∪ M.E, mem_powerset.mpr ?_, subset_union_right, rfl⟩
    exact union_subset (fun _ h => (mem_sdiff.mp (hf h)).1) (matching_edges_subset M)
  · rintro ⟨ha, F, hF, hm, rfl⟩
    have hU : F \ M.E ∪ M.E = F := sdiff_union_of_subset hm
    refine ⟨F \ M.E, mem_filter.mpr ⟨mem_powerset.mpr ?_, by simpa [hU]⟩, by rw [hU]⟩
    exact sdiff_subset_sdiff (mem_powerset.mp hF) (Subset.refl _)

lemma prec_iff_extension (N M : PM n) : Prec N M ↔ extensionSupport M ⊆ extensionSupport N := by
  constructor
  · intro h d hd
    obtain ⟨ha, hr⟩ := (mem_extensionSupport M d).mp hd
    exact (mem_extensionSupport N d).mpr ⟨ha, h d ha hr⟩
  · intro h d ha hr
    exact ((mem_extensionSupport N d).mp (h ((mem_extensionSupport M d).mpr ⟨ha,hr⟩))).2

lemma realizes_iff_optional (M : PM n) (d : Fin n → ℕ) :
    Realizes d M ↔ ∃ F ∈ ((allEdges n) \ M.E).powerset,
      codeDegree (F ∪ M.E) = d := by
  classical
  rw [realizes_code]
  constructor
  · rintro ⟨F,hF,hm,rfl⟩
    refine ⟨F \ M.E, mem_powerset.mpr ?_, ?_⟩
    · exact sdiff_subset_sdiff (mem_powerset.mp hF) (Subset.refl _)
    · rw [sdiff_union_of_subset hm]
  · rintro ⟨F,hF,rfl⟩
    have hf := mem_powerset.mp hF
    refine ⟨F ∪ M.E, mem_powerset.mpr ?_, subset_union_right, rfl⟩
    exact union_subset (fun _ h => (mem_sdiff.mp (hf h)).1) (matching_edges_subset M)

#print axioms prec_iff_extension
end Matching370688
```

### `MatchingSanity.lean`

```lean
import MatchingFinite
import Mathlib.Data.Fin.VecNotation

namespace Matching370688
instance (n : ℕ) : DecidablePred (fun p : Fin n → Fin n =>
    Function.Involutive p ∧ ∀ v, p v ≠ v) := by
  intro p
  unfold Function.Involutive
  infer_instance

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def m4nested : PM 4 := ⟨![3,2,1,0], by decide⟩
def m4crossed : PM 4 := ⟨![2,3,0,1], by decide⟩
def m4separate : PM 4 := ⟨![1,0,3,2], by decide⟩

theorem m4_type1 : IsSwitchOf m4crossed m4separate := by decide
theorem m4_type2 : IsSwitchOf m4nested m4crossed := by decide
theorem m4_type3 : IsSwitchOf m4nested m4separate := by decide

theorem m4_nested_support : degreeSupport m4nested =
    {![1,1,1,1], ![2,2,2,2], ![3,3,3,3], ![2,2,1,1], ![3,3,2,2], ![3,2,2,1]} := by decide

theorem m4_crossed_support : degreeSupport m4crossed =
    {![1,1,1,1], ![2,2,2,2], ![3,3,3,3], ![2,2,1,1], ![3,3,2,2]} := by decide

theorem m4_separate_support : degreeSupport m4separate =
    {![1,1,1,1], ![2,2,2,2], ![3,3,3,3]} := by decide

theorem four_table : ∀ (N M : PM 4), Prec N M ↔ N = M ∨ IsSwitchOf N M := by decide

theorem conjecture_11_four (N M : PM 4) (h : Prec N M) : ChainConclusion N M := by
  rcases (four_table N M).mp h with he | hs
  · subst M
    exact chainConclusion_refl N
  · refine ⟨[N,M], by simp, by simp, by simp, ?_⟩
    simpa [List.Chain'] using And.intro h hs

#print axioms conjecture_11_four
#print axioms four_table
end Matching370688
```

### `MatchingSixObjects.lean`

```lean
import MatchingExtensions
import Mathlib.Data.Fin.VecNotation
namespace Matching370688
instance sixPMDecidable (n : ℕ) : DecidablePred (fun p : Fin n → Fin n =>
    Function.Involutive p ∧ ∀ v, p v ≠ v) := by
  intro p
  unfold Function.Involutive
  infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def m6_0 : PM 6 := ⟨![1,0,3,2,5,4], by decide⟩
def m6_1 : PM 6 := ⟨![1,0,4,5,2,3], by decide⟩
def m6_2 : PM 6 := ⟨![1,0,5,4,3,2], by decide⟩
def m6_3 : PM 6 := ⟨![2,3,0,1,5,4], by decide⟩
def m6_4 : PM 6 := ⟨![2,4,0,5,1,3], by decide⟩
def m6_5 : PM 6 := ⟨![2,5,0,4,3,1], by decide⟩
def m6_6 : PM 6 := ⟨![3,2,1,0,5,4], by decide⟩
def m6_7 : PM 6 := ⟨![3,4,5,0,1,2], by decide⟩
def m6_8 : PM 6 := ⟨![3,5,4,0,2,1], by decide⟩
def m6_9 : PM 6 := ⟨![4,2,1,5,0,3], by decide⟩
def m6_10 : PM 6 := ⟨![4,3,5,1,0,2], by decide⟩
def m6_11 : PM 6 := ⟨![4,5,3,2,0,1], by decide⟩
def m6_12 : PM 6 := ⟨![5,2,1,4,3,0], by decide⟩
def m6_13 : PM 6 := ⟨![5,3,4,1,2,0], by decide⟩
def m6_14 : PM 6 := ⟨![5,4,3,2,1,0], by decide⟩
end Matching370688
```

### `MatchingSixSanity.lean`

```lean
import MatchingSixObjects

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Matching370688
open Finset

def d6a : Fin 6 → ℕ := ![5,3,3,3,3,1]
def d6b : Fin 6 → ℕ := ![5,5,3,3,2,2]

theorem six_type1 : IsSwitchOf m6_1 m6_0 := by decide
theorem six_type2 : IsSwitchOf m6_2 m6_1 := by decide
theorem six_type3 : IsSwitchOf m6_2 m6_0 := by decide

theorem six_realizes_a : Realizes d6a m6_13 := by
  apply (realizes_code d6a m6_13).mpr
  exact ⟨{s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,3),s(1,4),s(2,3),s(2,4)},
    by apply mem_powerset.mpr; decide, by decide, by decide⟩

theorem six_realizes_b : Realizes d6b m6_11 := by
  apply (realizes_code d6b m6_11).mpr
  exact ⟨{s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(1,2),s(1,3),s(1,4),s(1,5),s(2,3)},
    by apply mem_powerset.mpr; decide, by decide, by decide⟩

theorem six_not_realizes_a : ¬ Realizes d6a m6_11 := by
  rintro ⟨G, inst, hd, hm⟩
  let := inst
  have h0 : G.IsUniversal 0 := (G.degree_eq_card_sub_one 0).mp (by simpa [d6a] using hd 0)
  have h50 : G.Adj 5 0 := (h0 (w := 5) (by decide)).symm
  have h51 : G.Adj 5 1 := (show G.Adj 1 5 from hm s(1,5) (by decide)).symm
  have hdeg : G.degree 5 = 1 := by simpa [d6a] using hd 5
  have huniq := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have heq : (0 : Fin 6) = 1 := huniq.unique h50 h51
  exact (by decide : (0 : Fin 6) ≠ 1) heq

theorem six_not_realizes_b : ¬ Realizes d6b m6_13 := by
  rintro ⟨G, inst, hd, hm⟩
  let := inst
  have h0 : G.IsUniversal 0 := (G.degree_eq_card_sub_one 0).mp (by simpa [d6b] using hd 0)
  have h1 : G.IsUniversal 1 := (G.degree_eq_card_sub_one 1).mp (by simpa [d6b] using hd 1)
  have h40 : G.Adj 4 0 := (h0 (w := 4) (by decide)).symm
  have h41 : G.Adj 4 1 := (h1 (w := 4) (by decide)).symm
  have h42 : G.Adj 4 2 := (show G.Adj 2 4 from hm s(2,4) (by decide)).symm
  have hsub : ({0,1,2} : Finset (Fin 6)) ⊆ G.neighborFinset 4 := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> simpa using ‹G.Adj 4 _›
  have hc := Finset.card_le_card hsub
  have hcard : ({0,1,2} : Finset (Fin 6)).card = 3 := by decide
  rw [hcard, G.card_neighborFinset_eq_degree, hd 4] at hc
  have : d6b 4 = 2 := by decide
  omega

/-- The source's two labelled matchings are genuinely incomparable in the literal preorder. -/
theorem six_incomparable : ¬ Prec m6_11 m6_13 ∧ ¬ Prec m6_13 m6_11 := by
  constructor
  · intro h
    exact six_not_realizes_a (h d6a (by decide) six_realizes_a)
  · intro h
    exact six_not_realizes_b (h d6b (by decide) six_realizes_b)

#print axioms six_incomparable
#print axioms six_type1
#print axioms six_type2
#print axioms six_type3
end Matching370688
```

### `MatchingRankStepCore.lean`

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Int.Parity
import Lean.Elab.Tactic.Omega

/-! A checked finite-sum core for the overlap argument in PROOF-370688.md.
This is NOT the full matching conjecture. Its graph construction, rank-step
choice and chain endpoint remain to be formalized; diagonal parity is included. -/
set_option linter.unusedSectionVars false
namespace MatchingProofLane
open Finset
variable {V : Type*} [DecidableEq V]

def rectSum (A : V → V → ℤ) (S T : Finset V) : ℤ :=
  ∑ i ∈ S, ∑ j ∈ T, A i j

lemma rectSum_sub (A B : V → V → ℤ) (S T : Finset V) :
    rectSum (fun i j => A i j-B i j) S T=rectSum A S T-rectSum B S T := by
  simp only [rectSum,Finset.sum_sub_distrib]

lemma rectSum_symm (A : V → V → ℤ) (hA : ∀ i j, A i j=A j i) (S T : Finset V) :
    rectSum A S T=rectSum A T S := by
  unfold rectSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  exact hA i j

lemma rectSum_union_right (A : V → V → ℤ) (S T W : Finset V) (h : Disjoint T W) :
    rectSum A S (T ∪ W)=rectSum A S T+rectSum A S W := by
  simp only [rectSum,Finset.sum_union h,Finset.sum_add_distrib]

lemma rectSum_union_left (A : V → V → ℤ) (S T W : Finset V) (h : Disjoint S T) :
    rectSum A (S ∪ T) W=rectSum A S W+rectSum A T W := by
  exact Finset.sum_union h

/-- The square/block identity responsible for the two-unit gap in overlapping
rank rectangles. It is an identity of arbitrary symmetric integer matrices. -/
theorem symmetric_block_identity (A : V → V → ℤ) (hA : ∀ i j, A i j=A j i)
    (S W : Finset V) (hSW : Disjoint S W) :
    2*rectSum A S (S ∪ W)=rectSum A S S+rectSum A (S ∪ W) (S ∪ W)-rectSum A W W := by
  rw [rectSum_union_right A S S W hSW,
    rectSum_union_left A S W (S ∪ W) hSW,
    rectSum_union_right A W S W hSW,
    rectSum_union_right A S S W hSW,
    rectSum_symm A hA W S]
  omega

/-- Diagonal rank gaps are even, so a positive one is at least two. -/
lemma even_gap_ge_two (g : ℤ) (heven : Even g) (hpos : 1 ≤ g) : 2 ≤ g := by
  obtain ⟨a,ha⟩ := heven
  omega

/-- The overlap part of the elementary matching rank step, with all matrix
and diagonal premises visible. No Bruhat theorem or matching conjecture assumed. -/
theorem overlap_rank_gap_ge_two (X Y : V → V → ℤ)
    (hX : ∀ i j, X i j=X j i) (hY : ∀ i j, Y i j=Y j i)
    (S W : Finset V) (hSW : Disjoint S W)
    (hXzero : ∀ i ∈ W, ∀ j ∈ W, X i j=0)
    (hYnonneg : ∀ i ∈ W, ∀ j ∈ W, 0 ≤ Y i j)
    (hS : 2 ≤ rectSum (fun i j => X i j-Y i j) S S)
    (hT : 2 ≤ rectSum (fun i j => X i j-Y i j) (S ∪ W) (S ∪ W)) :
    2 ≤ rectSum (fun i j => X i j-Y i j) S (S ∪ W) := by
  have hG (i j : V) : X i j-Y i j=X j i-Y j i := by rw [hX i j,hY i j]
  have hid := symmetric_block_identity (fun i j => X i j-Y i j) hG S W hSW
  have hXW : rectSum X W W=0 := by
    unfold rectSum
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    exact hXzero i hi j hj
  have hYW : 0 ≤ rectSum Y W W := by
    unfold rectSum
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact hYnonneg i hi j hj
  rw [rectSum_sub X Y W W,hXW,zero_sub] at hid
  omega

/-- A stable finite set under a fixed-point-free involution has even size.
Applied to the internally matched prefix vertices, this is diagonal rank parity. -/
theorem even_card_stable_involution [LinearOrder V] (p : V → V)
    (hp : Function.Involutive p) (S : Finset V)
    (hstable : ∀ v ∈ S, p v ∈ S) (hfree : ∀ v ∈ S, p v ≠ v) : Even S.card := by
  let L := S.filter (fun v => v < p v)
  let H := S.filter (fun v => p v < v)
  have hcard : L.card=H.card := by
    apply Finset.card_bij (fun v _ => p v)
    · intro v hv
      have hh := mem_filter.mp hv
      exact mem_filter.mpr ⟨hstable v hh.1,by simpa only [hp v] using hh.2⟩
    · intro v hv w hw heq
      have hh := congrArg p heq
      simpa only [hp v,hp w] using hh
    · intro w hw
      have hh := mem_filter.mp hw
      refine ⟨p w,?_,hp w⟩
      exact mem_filter.mpr ⟨hstable w hh.1,by simpa only [hp w] using hh.2⟩
  have hdis : Disjoint L H := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hlt := (mem_filter.mp hv).2
    have hgt := (mem_filter.mp hw).2
    exact (not_lt_of_ge (le_of_lt hlt)) hgt
  have hunion : L ∪ H=S := by
    ext v
    simp only [L,H,mem_union,mem_filter]
    constructor
    · intro h
      rcases h with h | h <;> exact h.1
    · intro hv
      rcases lt_or_gt_of_ne (hfree v hv) with h | h
      · exact Or.inr ⟨hv,h⟩
      · exact Or.inl ⟨hv,h⟩
  have hs := Finset.card_union_of_disjoint hdis
  rw [hunion,hcard] at hs
  exact ⟨H.card,hs⟩

/-- The diagonal prefix rank of a perfect matching is even, stated for any
finite label subset rather than just an initial interval. -/
theorem even_internal_partner_count [LinearOrder V] (p : V → V)
    (hp : Function.Involutive p) (hfree : ∀ v, p v ≠ v) (S : Finset V) :
    Even (S.filter (fun v => p v ∈ S)).card := by
  let T := S.filter (fun v => p v ∈ S)
  apply even_card_stable_involution p hp T
  · intro v hv
    have hh := mem_filter.mp hv
    exact mem_filter.mpr ⟨hh.2,by simpa only [hp v] using hh.1⟩
  · intro v hv
    exact hfree v

/-- The ordinary zero-one partner matrix, without any Bruhat definition. -/
def partnerMatrix (p : V → V) (i j : V) : ℤ := if p i=j then 1 else 0

lemma partnerMatrix_symm (p : V → V) (hp : Function.Involutive p) (i j : V) :
    partnerMatrix p i j=partnerMatrix p j i := by
  have heq : p i=j ↔ p j=i := by
    constructor
    · intro h
      rw [← h,hp i]
    · intro h
      rw [← h,hp j]
  simp only [partnerMatrix,heq]

lemma partnerMatrix_nonneg (p : V → V) (i j : V) : 0 ≤ partnerMatrix p i j := by
  unfold partnerMatrix
  split_ifs <;> omega

lemma rectSum_partnerMatrix (p : V → V) (S T : Finset V) :
    rectSum (partnerMatrix p) S T=((S.filter (fun v => p v ∈ T)).card : ℤ) := by
  simp only [rectSum,partnerMatrix]
  rw [Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : p i ∈ T <;> simp [h]

/-- Concrete diagonal rank parity for the zero-one matching matrix. -/
theorem even_diagonal_partner_rank [LinearOrder V] (p : V → V)
    (hp : Function.Involutive p) (hfree : ∀ v, p v ≠ v) (S : Finset V) :
    Even (rectSum (partnerMatrix p) S S) := by
  rw [rectSum_partnerMatrix]
  obtain ⟨a,ha⟩ := even_internal_partner_count p hp hfree S
  refine ⟨(a : ℤ),?_⟩
  rw [ha,Nat.cast_add]

theorem positive_diagonal_gap_ge_two [LinearOrder V] (p q : V → V)
    (hp : Function.Involutive p) (hq : Function.Involutive q)
    (hpf : ∀ v, p v ≠ v) (hqf : ∀ v, q v ≠ v) (S : Finset V)
    (hgap : 1 ≤ rectSum (partnerMatrix p) S S-rectSum (partnerMatrix q) S S) :
    2 ≤ rectSum (partnerMatrix p) S S-rectSum (partnerMatrix q) S S := by
  exact even_gap_ge_two _ ((even_diagonal_partner_rank p hp hpf S).sub
    (even_diagonal_partner_rank q hq hqf S)) hgap

#print axioms positive_diagonal_gap_ge_two
#print axioms rectSum_partnerMatrix
#print axioms even_internal_partner_count
#print axioms even_card_stable_involution
#print axioms overlap_rank_gap_ge_two
end MatchingProofLane
```

### `MatchingRanks.lean`

```lean
import MatchingDefinitions
import MatchingRankStepCore

namespace Matching370688
open Finset
variable {n : ℕ}
def prefixSet (n i : ℕ) : Finset (Fin n) := univ.filter (fun v => v.val < i)
def rank (M : PM n) (i j : ℕ) : ℕ :=
  (univ.filter (fun v => v.val < i ∧ (M.val v).val < j)).card
def cross (M : PM n) (k t : ℕ) : ℕ :=
  (univ.filter (fun v => v.val < k ∧ t ≤ (M.val v).val)).card
def RankLE (M N : PM n) : Prop := ∀ i ≤ n, ∀ j ≤ n, rank N i j ≤ rank M i j
def potential (M N : PM n) : ℕ :=
  ∑ i ∈ range (n+1), ∑ j ∈ range (n+1), (rank M i j - rank N i j)

lemma rank_as_rectSum (M : PM n) (i j : ℕ) :
    (rank M i j : ℤ) = MatchingProofLane.rectSum (MatchingProofLane.partnerMatrix M.val)
      (prefixSet n i) (prefixSet n j) := by
  rw [MatchingProofLane.rectSum_partnerMatrix]
  simp [rank, prefixSet, Finset.filter_filter]

lemma rank_symm (M : PM n) (i j : ℕ) : rank M i j = rank M j i := by
  apply Nat.cast_injective (R := ℤ)
  rw [rank_as_rectSum, rank_as_rectSum]
  exact MatchingProofLane.rectSum_symm _ (MatchingProofLane.partnerMatrix_symm M.val M.property.1) _ _

lemma even_rank_diagonal (M : PM n) (i : ℕ) : Even (rank M i i) := by
  have he := MatchingProofLane.even_internal_partner_count M.val M.property.1 M.property.2 (prefixSet n i)
  convert he using 1
  simp [rank, prefixSet, Finset.filter_filter]

lemma rank_cross (M : PM n) (i j : ℕ) (hi : i ≤ n) :
    rank M i j + cross M i j = i := by
  have hcard : (prefixSet n i).card = i := by
    have hp : prefixSet n i = (Finset.univ : Finset (Fin i)).image (Fin.castLE hi) := by
      ext v
      simp only [prefixSet, mem_filter, mem_univ, true_and, mem_image]
      constructor
      · intro hv
        exact ⟨⟨v.val,hv⟩, by apply Fin.ext; rfl⟩
      · rintro ⟨u, rfl⟩
        exact u.isLt
    rw [hp, card_image_of_injective _ (Fin.castLE_injective hi)]
    simp
  have hp : Disjoint
      (univ.filter (fun v : Fin n => v.val < i ∧ (M.val v).val < j))
      (univ.filter (fun v : Fin n => v.val < i ∧ j ≤ (M.val v).val)) := by
    simp only [Finset.disjoint_filter]
    intro v _ h₁ h₂
    omega
  have hu : (univ.filter (fun v : Fin n => v.val < i ∧ (M.val v).val < j)) ∪
      (univ.filter (fun v : Fin n => v.val < i ∧ j ≤ (M.val v).val)) = prefixSet n i := by
    ext v
    simp only [mem_union, mem_filter, mem_univ, true_and, prefixSet]
    omega
  have hsum := Finset.card_union_of_disjoint hp
  rw [hu, hcard] at hsum
  exact hsum.symm

/-- Rank implication with the entire unproved separator obligation explicit. -/
lemma prec_cross
    (sep : ∀ (M N : PM n) k t, 0 < k → k ≤ t → t < n →
      cross N k t < cross M k t →
      ∃ d, Antitone d ∧ Realizes d M ∧ ¬Realizes d N)
    {N M : PM n} (h : Prec N M) (k t : ℕ) (hk : 0 < k) (hkt : k ≤ t) (ht : t < n) :
    cross M k t ≤ cross N k t := by
  by_contra hn
  obtain ⟨d,hd,hm,hn⟩ := sep M N k t hk hkt ht (by omega)
  exact hn (h d hd hm)

#print axioms rank_symm
#print axioms even_rank_diagonal
#print axioms rank_cross
#print axioms prec_cross
end Matching370688
```

### `MatchingRankBridge.lean`

```lean
import MatchingRanks

namespace Matching370688
open Finset
variable {n : ℕ}

lemma rank_zero_left (M : PM n) (j : ℕ) : rank M 0 j = 0 := by simp [rank]
lemma cross_top (M : PM n) (i : ℕ) : cross M i n = 0 := by
  have hf : (univ.filter (fun v : Fin n => v.val < i ∧ n ≤ (M.val v).val)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro v _ hv
    exact (Nat.not_le_of_gt (M.val v).isLt) hv.2
  rw [cross, hf, card_empty]

lemma prec_rank
    (sep : ∀ (M N : PM n) k t, 0 < k → k ≤ t → t < n →
      cross N k t < cross M k t →
      ∃ d, Antitone d ∧ Realizes d M ∧ ¬Realizes d N)
    {N M : PM n} (h : Prec N M) : RankLE M N := by
  have hu : ∀ i ≤ n, ∀ j ≤ n, i ≤ j → rank N i j ≤ rank M i j := by
    intro i hi j hj hij
    by_cases hi0 : i = 0
    · subst i; simp [rank_zero_left]
    · have hM := rank_cross M i j hi
      have hN := rank_cross N i j hi
      by_cases hjn : j = n
      · subst j
        rw [cross_top] at hM hN
        omega
      · have hc := prec_cross sep h i j (by omega) hij (by omega)
        omega
  intro i hi j hj
  by_cases hij : i ≤ j
  · exact hu i hi j hj hij
  · rw [rank_symm N i j, rank_symm M i j]
    exact hu j hj i hi (by omega)

lemma rank_succ_left (M : PM n) (i j : ℕ) (hi : i < n) :
    rank M (i+1) j = rank M i j + if (M.val ⟨i,hi⟩).val < j then 1 else 0 := by
  let v : Fin n := ⟨i,hi⟩
  let S := univ.filter (fun u : Fin n => u.val < i ∧ (M.val u).val < j)
  have hv : v ∉ S := by simp [S,v]
  by_cases hp : (M.val v).val < j
  · have he : univ.filter (fun u : Fin n => u.val < i+1 ∧ (M.val u).val < j) = insert v S := by
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_insert, S]
      constructor
      · intro hu
        by_cases hui : u.val < i
        · exact Or.inr ⟨hui,hu.2⟩
        · exact Or.inl (Fin.ext (by dsimp [v]; omega))
      · rintro (rfl | hu)
        · exact ⟨by dsimp [v]; omega, hp⟩
        · exact ⟨by omega,hu.2⟩
    change (univ.filter _).card = S.card + _
    rw [he, card_insert_of_notMem hv]
    simp [hp, v] at *
  · have he : univ.filter (fun u : Fin n => u.val < i+1 ∧ (M.val u).val < j) = S := by
      ext u
      simp only [mem_filter, mem_univ, true_and, S]
      constructor
      · intro hu
        have hne : u.val ≠ i := by
          intro heq
          have huv : u = v := Fin.ext heq
          exact hp (huv ▸ hu.2)
        exact ⟨by omega,hu.2⟩
      · intro hu
        exact ⟨by omega,hu.2⟩
    change (univ.filter _).card = S.card + _
    rw [he]
    simp [hp, v] at *

lemma rank_ext {M N : PM n} (h : ∀ i j, rank M i j = rank N i j) : M = N := by
  apply Subtype.ext
  funext v
  apply Fin.ext
  have hh : ∀ j, (if (M.val v).val < j then 1 else 0 : ℕ) =
      (if (N.val v).val < j then 1 else 0 : ℕ) := by
    intro j
    have hm := rank_succ_left M v.val j v.isLt
    have hn := rank_succ_left N v.val j v.isLt
    rw [h, h] at hm
    exact Nat.add_left_cancel (hm.symm.trans hn)
  have h₁ := hh ((M.val v).val+1)
  have h₂ := hh ((N.val v).val+1)
  split_ifs at h₁ h₂ <;> omega

#print axioms prec_rank
#print axioms rank_succ_left
#print axioms rank_ext
end Matching370688
```

### `MatchingAssembly.lean`

```lean
import MatchingRankBridge

namespace Matching370688
variable {n : ℕ}

/-- Formalize the chain induction with the two missing mathematical inputs
visible as parameters. This is conditional and is not Conjecture 11. -/
theorem rank_chain
    (step : ∀ A B : PM n, RankLE A B → A ≠ B →
      ∃ P, IsSwitchOf P A ∧ RankLE P B ∧ potential P B < potential A B)
    (monotone : ∀ A B : PM n, IsSwitchOf A B → Prec A B)
    {M N : PM n} (h : RankLE M N) : ChainConclusion N M := by
  classical
  generalize hm : potential M N = m
  induction m using Nat.strong_induction_on generalizing M with
  | h m ih =>
    by_cases he : M = N
    · subst M
      exact chainConclusion_refl N
    · obtain ⟨P, hs, hp, hlt⟩ := step M N h he
      obtain ⟨L, hl, hhead, hlast, hc⟩ := ih (potential P N) (by omega) hp rfl
      refine ⟨L ++ [M], by simp, ?_, by simp, ?_⟩
      · simp [List.head?_append, hhead]
      · apply List.IsChain.append hc (by simp)
        intro a ha b hb
        have haP : P = a := by simpa [hlast] using ha
        have hbM : M = b := by simpa using hb
        subst a b
        exact ⟨monotone P M hs, hs⟩

/-- Literal endpoint proved only conditional on separator, elementary rank step,
and source Lemma 10(b). There are no hidden axioms standing for these inputs. -/
theorem conjecture_11_of_obligations
    (sep : ∀ (M N : PM n) k t, 0 < k → k ≤ t → t < n →
      cross N k t < cross M k t →
      ∃ d, Antitone d ∧ Realizes d M ∧ ¬Realizes d N)
    (step : ∀ A B : PM n, RankLE A B → A ≠ B →
      ∃ P, IsSwitchOf P A ∧ RankLE P B ∧ potential P B < potential A B)
    (monotone : ∀ A B : PM n, IsSwitchOf A B → Prec A B)
    (N M : PM n) (h : Prec N M) :
    ∃ L : List (PM n), L ≠ [] ∧ L.head? = some N ∧ L.getLast? = some M ∧
      L.Chain' (fun A B => Prec A B ∧ IsSwitchOf A B) :=
  rank_chain step monotone (prec_rank sep h)

#print axioms rank_chain
#print axioms conjecture_11_of_obligations
end Matching370688
```

### `MatchingMiddle.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega

namespace Matching370688
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A deletion graph supported on C, every deleted edge meeting E. -/
def CorrectionSupport (J : SimpleGraph V) (C E : Finset V) : Prop :=
  ∀ u v, J.Adj u v → u ∈ C ∧ v ∈ C ∧ (u ∈ E ∨ v ∈ E)

/-- Pairing an arbitrary even set gives actual simple-graph degrees, not just
an arithmetic degree profile. Uses Mathlib's proved complete-graph matching lemma. -/
theorem even_pairing_graph (S : Finset V) (he : Even S.card) :
    ∃ J : SimpleGraph V, ∃ _ : DecidableRel J.Adj,
      (∀ u v, J.Adj u v → u ∈ S ∧ v ∈ S) ∧
      ∀ v, J.degree v = if v ∈ S then 1 else 0 := by
  classical
  have hc : (⊤ : SimpleGraph V).IsClique (S : Set V) := by
    intro u hu v hv hne
    exact hne
  have hn : Even (S : Set V).ncard := by simpa using he
  obtain ⟨K, hK, hm⟩ := (hc.even_iff_exists_isMatching (Set.toFinite _)).mp hn
  refine ⟨K.spanningCoe, inferInstance, ?_, ?_⟩
  · intro u v huv
    exact ⟨by simpa [hK] using huv.fst_mem, by simpa [hK] using huv.snd_mem⟩
  · intro v
    by_cases hv : v ∈ S
    · simp only [hv, ite_true]
      rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
      exact hm (by simpa [hK] using hv)
    · simp only [hv, ite_false]
      rw [SimpleGraph.degree_eq_zero]
      intro u h
      exact hv (by simpa [hK] using h.fst_mem)

/-- First middle-block case: even E, all extra units canceled. -/
theorem middle_even (C E : Finset V) (hEC : E ⊆ C) (he : Even E.card) :
    ∃ J : SimpleGraph V, ∃ _ : DecidableRel J.Adj,
      CorrectionSupport J C E ∧ ∀ v, J.degree v = if v ∈ E then 1 else 0 := by
  obtain ⟨J, inst, hs, hd⟩ := even_pairing_graph E he
  exact ⟨J, inst, fun u v h => ⟨hEC (hs u v h).1, hEC (hs u v h).2,
    Or.inl (hs u v h).1⟩, hd⟩

/-- Second case: odd E not containing the last vertex. Pair E∪{w};
looplessness forces each deletion to meet E. -/
theorem middle_odd_last_out (C E : Finset V) (w : V) (hEC : E ⊆ C)
    (hwC : w ∈ C) (hwE : w ∉ E) (he : Odd E.card) :
    ∃ J : SimpleGraph V, ∃ _ : DecidableRel J.Adj,
      CorrectionSupport J C E ∧
      ∀ v, J.degree v = if v ∈ insert w E then 1 else 0 := by
  have hev : Even (insert w E).card := by
    rw [card_insert_of_notMem hwE]
    exact he.add_odd (by decide : Odd 1)
  obtain ⟨J, inst, hs, hd⟩ := even_pairing_graph (insert w E) hev
  refine ⟨J, inst, ?_, hd⟩
  intro u v h
  have hu := hs u v h
  have hsub : insert w E ⊆ C := insert_subset hwC hEC
  refine ⟨hsub hu.1, hsub hu.2, ?_⟩
  rcases mem_insert.mp hu.1 with rfl | huE
  · rcases mem_insert.mp hu.2 with rfl | hvE
    · exact False.elim (J.loopless.irrefl _ h)
    · exact Or.inr hvE
  · exact Or.inl huE

/-- A loop-free two-edge star, used in both remaining correction cases. -/
def twoStar (w x y : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((u = w ∧ (v = x ∨ v = y)) ∨ (v = w ∧ (u = x ∨ u = y)))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (w x y : V) : DecidableRel (twoStar w x y).Adj := by
  unfold twoStar
  infer_instance

lemma twoStar_degree (w x y : V) (hwx : w ≠ x) (hwy : w ≠ y) (hxy : x ≠ y)
    (v : V) :
    (twoStar w x y).degree v = if v = w then 2 else if v = x ∨ v = y then 1 else 0 := by
  have hnb : (twoStar w x y).neighborFinset v =
      if v = w then {x,y} else if v = x ∨ v = y then {w} else ∅ := by
    ext u
    simp only [SimpleGraph.mem_neighborFinset]
    split_ifs <;> simp_all [twoStar, Ne.symm]
    rintro (rfl | rfl) <;> assumption
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb]
  split_ifs <;> simp_all

lemma degree_sup_add (J K : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel K.Adj]
    (hdis : ∀ u v, J.Adj u v → ¬ K.Adj u v) (v : V) :
    (J ⊔ K).degree v = J.degree v + K.degree v := by
  have hd : Disjoint (J.neighborFinset v) (K.neighborFinset v) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    exact hdis v u (by simpa using hu) (by simpa using hv)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
    Finset.card_union_of_disjoint hd]
  rfl

/-- Third case: pair E minus the three star vertices, and use the star
at w. The exact disjoint union degree computation is part of this theorem. -/
theorem middle_odd_last_in (C E : Finset V) (w : V) (hEC : E ⊆ C)
    (hwE : w ∈ E) (he : Odd E.card) (hsize : 3 ≤ E.card) :
    ∃ J : SimpleGraph V, ∃ _ : DecidableRel J.Adj,
      CorrectionSupport J C E ∧
      ∀ v, J.degree v = if v = w then 2 else if v ∈ E then 1 else 0 := by
  classical
  have htwo : 1 < (E.erase w).card := by rw [card_erase_of_mem hwE]; omega
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp htwo
  have hxE := (mem_erase.mp hx).2
  have hyE := (mem_erase.mp hy).2
  have hwx : w ≠ x := (mem_erase.mp hx).1.symm
  have hwy : w ≠ y := (mem_erase.mp hy).1.symm
  let T : Finset V := {w,x,y}
  have hTE : T ⊆ E := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact hwE
    · rcases mem_insert.mp hv with rfl | hv
      · exact hxE
      · have hvy := mem_singleton.mp hv
        simpa [hvy] using hyE
  have hTcard : T.card = 3 := by simp [T, hwx, hwy, hxy]
  have hcard := card_sdiff_add_card_eq_card hTE
  rw [hTcard] at hcard
  have hev : Even (E \ T).card := by
    obtain ⟨a, ha⟩ := he
    exact ⟨a-1, by omega⟩
  obtain ⟨K, inst, hK, hdK⟩ := even_pairing_graph (E \ T) hev
  let := inst
  let J := K ⊔ twoStar w x y
  have hdis : ∀ u v, K.Adj u v → ¬ (twoStar w x y).Adj u v := by
    intro u v huv hstar
    have hu := (mem_sdiff.mp (hK u v huv).1).2
    have hv := (mem_sdiff.mp (hK u v huv).2).2
    rcases hstar.2 with hs | hs
    · exact hu (by simp [T, hs.1])
    · exact hv (by simp [T, hs.1])
  refine ⟨J, inferInstance, ?_, ?_⟩
  · intro u v huv
    rcases huv with hk | hs
    · have hu := (mem_sdiff.mp (hK u v hk).1).1
      have hv := (mem_sdiff.mp (hK u v hk).2).1
      exact ⟨hEC hu, hEC hv, Or.inl hu⟩
    · have hu : u ∈ E := by
        rcases hs.2 with hs | hs
        · simpa [hs.1] using hwE
        · rcases hs.2 with rfl | rfl <;> assumption
      have hv : v ∈ E := by
        rcases hs.2 with hs | hs
        · rcases hs.2 with rfl | rfl <;> assumption
        · simpa [hs.1] using hwE
      exact ⟨hEC hu, hEC hv, Or.inl hu⟩
  · intro v
    rw [degree_sup_add K _ hdis, hdK, twoStar_degree w x y hwx hwy hxy]
    by_cases hvw : v = w
    · subst v; simp [T, hwE]
    · by_cases hvx : v = x
      · subst v; simp [T, hxE, hwx.symm]
      · by_cases hvy : v = y
        · subst v; simp [T, hyE, hwy.symm]
        · simp [T, hvw, hvx, hvy]

/-- Fourth case, E={w}: the two-edge star has the required loss of 2
at w and of 1 at the two selected preceding vertices. -/
theorem middle_singleton_last (C : Finset V) (w x y : V)
    (hwC : w ∈ C) (hxC : x ∈ C) (hyC : y ∈ C)
    (hwx : w ≠ x) (hwy : w ≠ y) (hxy : x ≠ y) :
    ∃ J : SimpleGraph V, ∃ _ : DecidableRel J.Adj,
      CorrectionSupport J C {w} ∧
      ∀ v, J.degree v = if v = w then 2 else if v = x ∨ v = y then 1 else 0 := by
  refine ⟨twoStar w x y, inferInstance, ?_, twoStar_degree w x y hwx hwy hxy⟩
  intro u v huv
  rcases huv.2 with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
    simp_all

#print axioms even_pairing_graph
#print axioms middle_even
#print axioms middle_odd_last_out
#print axioms twoStar_degree
#print axioms middle_odd_last_in
#print axioms middle_singleton_last
end Matching370688
```

### `MatchingMiddleProfile.lean`

```lean
import MatchingMiddle
import MatchingDefinitions

set_option linter.unnecessarySeqFocus false
namespace Matching370688
open Finset

def middleBlock (n k t : ℕ) : Finset (Fin n) := univ.filter (fun v => k ≤ v.val ∧ v.val < t)
def middleProfile (t r : ℕ) {n : ℕ} (v : Fin n) : ℤ :=
  if r ≤ v.val then (t : ℤ)-2 else (t : ℤ)-1

lemma middleProfile_antitone (t r : ℕ) {n : ℕ} : Antitone (@middleProfile t r n) := by
  intro u v huv
  unfold middleProfile
  split_ifs <;> omega

lemma middleProfile_gt {n k t r : ℕ} (h3 : k+3 ≤ t) (v : Fin n) :
    (k : ℤ) < middleProfile t r v := by
  unfold middleProfile
  split_ifs <;> omega

/-- All four middle cases assembled as an actual deletion graph with a sorted
two-level degree profile. This theorem contains the parity and singleton cases. -/
theorem middle_correction {n : ℕ} (k t : ℕ) (h3 : k+3 ≤ t) (ht : t ≤ n)
    (E : Finset (Fin n)) (hEC : E ⊆ middleBlock n k t) :
    ∃ J : SimpleGraph (Fin n), ∃ _ : DecidableRel J.Adj,
      CorrectionSupport J (middleBlock n k t) E ∧
      ∃ r : ℕ, k ≤ r ∧ r ≤ t ∧ ∀ v ∈ middleBlock n k t,
        (t : ℤ)-1 + (if v ∈ E then 1 else 0) - (J.degree v : ℤ) = middleProfile t r v := by
  classical
  let w : Fin n := ⟨t-1, by omega⟩
  let x : Fin n := ⟨t-2, by omega⟩
  let y : Fin n := ⟨t-3, by omega⟩
  have hwC : w ∈ middleBlock n k t := by simp [middleBlock, w]; omega
  have hxC : x ∈ middleBlock n k t := by simp [middleBlock, x]; omega
  have hyC : y ∈ middleBlock n k t := by simp [middleBlock, y]; omega
  have hwx : w ≠ x := by intro h; have := congrArg Fin.val h; dsimp [w,x] at this; omega
  have hwy : w ≠ y := by intro h; have := congrArg Fin.val h; dsimp [w,y] at this; omega
  have hxy : x ≠ y := by intro h; have := congrArg Fin.val h; dsimp [x,y] at this; omega
  rcases Nat.even_or_odd E.card with he | ho
  · obtain ⟨J, inst, hs, hd⟩ := middle_even _ E hEC he
    let := inst
    refine ⟨J, inst, hs, t, by omega, le_rfl, ?_⟩
    intro v hv
    have hv' := (mem_filter.mp hv).2
    have hlast : ¬t ≤ v.val := by omega
    rw [hd]
    by_cases hE : v ∈ E <;> simp [hE, middleProfile, hlast]
  · by_cases hwE : w ∈ E
    · by_cases hsize : 3 ≤ E.card
      · obtain ⟨J, inst, hs, hd⟩ := middle_odd_last_in _ E w hEC hwE ho hsize
        let := inst
        refine ⟨J, inst, hs, t-1, by omega, by omega, ?_⟩
        intro v hv
        have hv' := (mem_filter.mp hv).2
        have hvw : v = w ↔ t-1 ≤ v.val := by
          constructor
          · intro h; subst v; simp [w]
          · intro h; apply Fin.ext; dsimp [w]; omega
        rw [hd]
        by_cases hE : v ∈ E <;> by_cases hw : v = w <;>
          simp_all [middleProfile]
      · have hcard : E.card = 1 := by obtain ⟨a, ha⟩ := ho; omega
        have hEs : E = {w} := by
          obtain ⟨z,hz⟩ := card_eq_one.mp hcard
          rw [hz] at hwE ⊢
          have heq : w = z := mem_singleton.mp hwE
          rw [heq]
        obtain ⟨J, inst, hs, hd⟩ := middle_singleton_last _ w x y hwC hxC hyC hwx hwy hxy
        let := inst
        refine ⟨J, inst, by simpa [hEs] using hs, t-3, by omega, by omega, ?_⟩
        intro v hv
        have hv' := (mem_filter.mp hv).2
        have hvw : v = w ↔ v.val = t-1 := Fin.ext_iff
        have hvx : v = x ↔ v.val = t-2 := Fin.ext_iff
        have hvy : v = y ↔ v.val = t-3 := Fin.ext_iff
        rw [hEs, hd]
        simp only [mem_singleton]
        by_cases hw : v = w <;> by_cases hx : v = x <;> by_cases hy : v = y <;>
          simp_all [middleProfile] <;> omega
    · obtain ⟨J, inst, hs, hd⟩ := middle_odd_last_out _ E w hEC hwC hwE ho
      let := inst
      refine ⟨J, inst, hs, t-1, by omega, by omega, ?_⟩
      intro v hv
      have hv' := (mem_filter.mp hv).2
      have hvw : v = w ↔ t-1 ≤ v.val := by
        constructor
        · intro h; subst v; simp [w]
        · intro h; apply Fin.ext; dsimp [w]; omega
      rw [hd]
      by_cases hE : v ∈ E <;> by_cases hw : v = w <;>
        simp_all [middleProfile] <;> omega

#print axioms middle_correction
#print axioms middleProfile_antitone
#print axioms middleProfile_gt
end Matching370688
```

### `MatchingApplyCorrection.lean`

```lean
import MatchingMiddleProfile

namespace Matching370688
open Finset
variable {n : ℕ}

lemma degree_sdiff_add (G J : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    [DecidableRel J.Adj] (hJG : J ≤ G) (v : Fin n) :
    (G \ J).degree v + J.degree v = G.degree v := by
  have hsub : J.neighborFinset v ⊆ G.neighborFinset v := by
    intro u hu
    have ha : J.Adj v u := by simpa using hu
    simpa using hJG ha
  simpa only [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sdiff]
    using Finset.card_sdiff_add_card_eq_card hsub

/-- The constructed middle correction never removes a prescribed matching edge. -/
lemma correction_avoids_matching (M : PM n) (k t : ℕ) (E : Finset (Fin n))
    (hE : ∀ v ∈ E, t ≤ (M.val v).val) (J : SimpleGraph (Fin n))
    (hs : CorrectionSupport J (middleBlock n k t) E) (v : Fin n) :
    ¬ J.Adj v (M.val v) := by
  intro hj
  obtain ⟨hvC,hpC,he⟩ := hs _ _ hj
  have hv := (mem_filter.mp hvC).2.2
  have hp := (mem_filter.mp hpC).2.2
  rcases he with he | he
  · have := hE v he
    omega
  · have hh := hE (M.val v) he
    rw [M.inv] at hh
    omega

/-- Apply the correction to any base graph having the G₀ middle degrees.
The base-graph construction and its other degree counts remain separate inputs. -/
theorem apply_middle_correction (M : PM n) (k t : ℕ) (h3 : k+3 ≤ t) (ht : t ≤ n)
    (E : Finset (Fin n)) (hEC : E ⊆ middleBlock n k t)
    (hE : ∀ v ∈ E, t ≤ (M.val v).val)
    (G₀ : SimpleGraph (Fin n)) [DecidableRel G₀.Adj]
    (hM : ∀ v, G₀.Adj v (M.val v))
    (hclique : ∀ u ∈ middleBlock n k t, ∀ v ∈ middleBlock n k t,
      u ≠ v → G₀.Adj u v)
    (hdeg : ∀ v ∈ middleBlock n k t,
      G₀.degree v = t-1 + if v ∈ E then 1 else 0) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
      ∃ r : ℕ, k ≤ r ∧ r ≤ t ∧
      (∀ v, G.Adj v (M.val v)) ∧
      (∀ v ∈ middleBlock n k t, (G.degree v : ℤ) = middleProfile t r v) ∧
      (∀ v ∉ middleBlock n k t, G.degree v = G₀.degree v) ∧
      (∀ u ∈ middleBlock n k t, ∀ v ∈ middleBlock n k t, u ≤ v → G.degree v ≤ G.degree u) ∧
      (∀ v ∈ middleBlock n k t, k < G.degree v) := by
  classical
  obtain ⟨J, inst, hs, r, hkr, hrt, hd⟩ := middle_correction k t h3 ht E hEC
  let := inst
  have hJG : J ≤ G₀ := by
    intro u v huv
    have hh := hs u v huv
    exact hclique u hh.1 v hh.2.1 huv.ne
  let G := G₀ \ J
  have hdegree (v : Fin n) := degree_sdiff_add G₀ J hJG v
  have hmid : ∀ v ∈ middleBlock n k t, (G.degree v : ℤ) = middleProfile t r v := by
    intro v hv
    have hz : (G.degree v : ℤ) + (J.degree v : ℤ) =
        (t : ℤ)-1 + (if v ∈ E then 1 else 0) := by
      have hh := hdegree v
      rw [hdeg v hv] at hh
      have hcast := congrArg (fun a : ℕ => (a : ℤ)) hh
      by_cases he : v ∈ E <;> simp [he, Nat.cast_sub (by omega : 1 ≤ t)] at hcast ⊢ <;> omega
    have hp := hd v hv
    omega
  refine ⟨G, inferInstance, r, hkr, hrt, ?_, hmid, ?_, ?_, ?_⟩
  · intro v
    exact ⟨hM v, correction_avoids_matching M k t E hE J hs v⟩
  · intro v hv
    have hzero : J.degree v = 0 := by
      rw [SimpleGraph.degree_eq_zero]
      intro u hu
      exact hv (hs v u hu).1
    have hh := hdegree v
    rw [hzero, add_zero] at hh
    exact hh
  · intro u hu v hv huv
    have hp := middleProfile_antitone t r huv
    rw [← hmid u hu, ← hmid v hv] at hp
    exact_mod_cast hp
  · intro v hv
    have hp := middleProfile_gt h3 (r := r) v
    rw [← hmid v hv] at hp
    exact_mod_cast hp

#print axioms correction_avoids_matching
#print axioms apply_middle_correction
end Matching370688
```

### `MatchingBaseGraph.lean`

```lean
import MatchingRankBridge
import MatchingApplyCorrection

namespace Matching370688
open Finset
variable {n : ℕ}

lemma partner_eq_symm (M : PM n) (u v : Fin n) : M.val u = v ↔ M.val v = u := by
  constructor <;> intro h
  · rw [← h, M.inv]
  · rw [← h, M.inv]

/-- G₀: clique on the first t labels, the retained prefix/suffix edges,
and all prescribed matching edges. The last prefix vertex is the only one
whose nonmatching suffix edges are omitted. -/
def baseGraph (M : PM n) (k t : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧
    ((u.val < t ∧ v.val < t) ∨
     (u.val < k ∧ t ≤ v.val ∧ (u.val+1 < k ∨ (M.val v).val < k)) ∨
     (v.val < k ∧ t ≤ u.val ∧ (v.val+1 < k ∨ (M.val u).val < k)) ∨ M.val u = v)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr ((partner_eq_symm M u v).mp h)))⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (M : PM n) (k t : ℕ) : DecidableRel (baseGraph M k t).Adj := by
  unfold baseGraph
  infer_instance

lemma baseGraph_contains (M : PM n) (k t : ℕ) (v : Fin n) :
    (baseGraph M k t).Adj v (M.val v) :=
  ⟨(M.free v).symm, Or.inr (Or.inr (Or.inr rfl))⟩

lemma baseGraph_middle_clique (M : PM n) (k t : ℕ)
    (u : Fin n) (hu : u ∈ middleBlock n k t)
    (v : Fin n) (hv : v ∈ middleBlock n k t) (hne : u ≠ v) :
    (baseGraph M k t).Adj u v :=
  ⟨hne, Or.inl ⟨(mem_filter.mp hu).2.2, (mem_filter.mp hv).2.2⟩⟩

lemma prefixSet_card (i : ℕ) (hi : i ≤ n) : (prefixSet n i).card = i := by
  have hp : prefixSet n i = (Finset.univ : Finset (Fin i)).image (Fin.castLE hi) := by
    ext v
    simp only [prefixSet, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hv
      exact ⟨⟨v.val,hv⟩, by apply Fin.ext; rfl⟩
    · rintro ⟨u,rfl⟩
      exact u.isLt
  rw [hp, card_image_of_injective _ (Fin.castLE_injective hi)]
  simp

lemma baseGraph_middle_neighbors (M : PM n) (k t : ℕ) (v : Fin n)
    (hv : v ∈ middleBlock n k t) :
    (baseGraph M k t).neighborFinset v =
      if t ≤ (M.val v).val then insert (M.val v) ((prefixSet n t).erase v)
      else (prefixSet n t).erase v := by
  have hv' := (mem_filter.mp hv).2
  ext u
  simp only [SimpleGraph.mem_neighborFinset]
  by_cases hp : t ≤ (M.val v).val
  · simp only [hp, ite_true, mem_insert, mem_erase, prefixSet, mem_filter, mem_univ, true_and]
    change (v ≠ u ∧ _) ↔ u = M.val v ∨ u ≠ v ∧ u.val < t
    constructor
    · rintro ⟨hne,hu | hu | hu | hu⟩
      · exact Or.inr ⟨hne.symm,hu.2⟩
      · omega
      · omega
      · exact Or.inl hu.symm
    · rintro (rfl | ⟨hne,hu⟩)
      · exact baseGraph_contains M k t v
      · exact ⟨hne.symm, Or.inl ⟨hv'.2,hu⟩⟩
  · simp only [hp, ite_false, mem_erase, prefixSet, mem_filter, mem_univ, true_and]
    change (v ≠ u ∧ _) ↔ u ≠ v ∧ u.val < t
    constructor
    · rintro ⟨hne,hu | hu | hu | hu⟩
      · exact ⟨hne.symm,hu.2⟩
      · omega
      · omega
      · exact ⟨hne.symm, by rw [← hu]; omega⟩
    · rintro ⟨hne,hu⟩
      exact ⟨hne.symm, Or.inl ⟨hv'.2,hu⟩⟩

lemma baseGraph_middle_degree (M : PM n) (k t : ℕ) (ht : t ≤ n)
    (v : Fin n) (hv : v ∈ middleBlock n k t) :
    (baseGraph M k t).degree v = t-1 + if t ≤ (M.val v).val then 1 else 0 := by
  have hv' := (mem_filter.mp hv).2
  have hvm : v ∈ prefixSet n t := by simp [prefixSet, hv'.2]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, baseGraph_middle_neighbors M k t v hv]
  by_cases hp : t ≤ (M.val v).val
  · have hpm : M.val v ∉ (prefixSet n t).erase v := by
      simp only [mem_erase, prefixSet, mem_filter, mem_univ, true_and, not_and]
      intro _; omega
    simp only [hp, ite_true, card_insert_of_notMem hpm,
      card_erase_of_mem hvm, prefixSet_card t ht]
  · simp only [hp, ite_false, card_erase_of_mem hvm, prefixSet_card t ht, add_zero]

#print axioms baseGraph_contains
#print axioms baseGraph_middle_degree
end Matching370688
```

### `MatchingBaseDegrees.lean`

```lean
import MatchingBaseGraph

namespace Matching370688
open Finset
variable {n : ℕ}

lemma baseGraph_early_degree (M : PM n) (k t : ℕ) (hkt : k ≤ t)
    (v : Fin n) (hv : v.val+1 < k) : (baseGraph M k t).degree v = n-1 := by
  have hnb : (baseGraph M k t).neighborFinset v = univ.erase v := by
    ext u
    simp only [SimpleGraph.mem_neighborFinset, mem_erase, mem_univ, and_true]
    constructor
    · intro h; exact h.1.symm
    · intro hne
      refine ⟨hne.symm, ?_⟩
      by_cases hu : u.val < t
      · exact Or.inl ⟨by omega,hu⟩
      · exact Or.inr (Or.inl ⟨by omega, by omega, Or.inl hv⟩)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb, card_erase_of_mem (mem_univ _)]
  simp

lemma baseGraph_suffix_neighbors (M : PM n) (k t : ℕ) (hk : 0 < k)
    (hkt : k ≤ t) (ht : t ≤ n) (v : Fin n) (hv : t ≤ v.val) :
    (baseGraph M k t).neighborFinset v =
      if (M.val v).val < k then prefixSet n k
      else insert (M.val v) ((prefixSet n k).erase ⟨k-1,by omega⟩) := by
  ext u
  by_cases hp : (M.val v).val < k
  · simp only [hp, ite_true, SimpleGraph.mem_neighborFinset, prefixSet, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hne, hu | hu | hu | hu⟩
      · omega
      · omega
      · exact hu.1
      · rw [← hu]; exact hp
    · intro hu
      refine ⟨by intro h; have := congrArg Fin.val h; omega, ?_⟩
      exact Or.inr (Or.inr (Or.inl ⟨hu,hv,Or.inr hp⟩))
  · simp only [hp, ite_false, SimpleGraph.mem_neighborFinset, mem_insert, mem_erase,
      prefixSet, mem_filter, mem_univ, true_and]
    have huLast : u ≠ (⟨k-1,by omega⟩ : Fin n) ↔ u.val ≠ k-1 := by
      exact not_congr Fin.ext_iff
    rw [huLast]
    constructor
    · rintro ⟨hne, hu | hu | hu | hu⟩
      · omega
      · omega
      · right; omega
      · exact Or.inl hu.symm
    · rintro (rfl | ⟨hne,hu⟩)
      · exact baseGraph_contains M k t v
      · refine ⟨by intro h; have := congrArg Fin.val h; omega, ?_⟩
        exact Or.inr (Or.inr (Or.inl ⟨hu,hv,Or.inl (by omega)⟩))

lemma baseGraph_suffix_degree (M : PM n) (k t : ℕ) (hk : 0 < k)
    (hkt : k ≤ t) (ht : t ≤ n) (v : Fin n) (hv : t ≤ v.val) :
    (baseGraph M k t).degree v = k := by
  let w : Fin n := ⟨k-1,by omega⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    baseGraph_suffix_neighbors M k t hk hkt ht v hv]
  by_cases hp : (M.val v).val < k
  · simp only [hp, ite_true, prefixSet_card (n := n) k (by omega)]
  · have hw : w ∈ prefixSet n k := by simp [prefixSet,w]; omega
    have hpm : M.val v ∉ (prefixSet n k).erase w := by
      simp only [mem_erase, prefixSet, mem_filter, mem_univ, true_and, not_and]
      intro _; exact hp
    simp only [hp, ite_false]
    change (insert (M.val v) ((prefixSet n k).erase w)).card = k
    rw [card_insert_of_notMem hpm, card_erase_of_mem hw, prefixSet_card k (by omega)]
    omega

lemma cross_suffix_count (M : PM n) (k t : ℕ) :
    (univ.filter (fun v : Fin n => t ≤ v.val ∧ (M.val v).val < k)).card = cross M k t := by
  unfold cross
  apply Finset.card_bij (fun v _ => M.val v)
  · intro v hv
    obtain ⟨_,ht,hk⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨mem_univ _, hk, by simpa only [M.inv] using ht⟩
  · intro v hv w hw heq
    have := congrArg M.val heq
    simpa only [M.inv] using this
  · intro w hw
    obtain ⟨_,hk,ht⟩ := mem_filter.mp hw
    refine ⟨M.val w, ?_, M.inv w⟩
    exact mem_filter.mpr ⟨mem_univ _,ht,by simpa only [M.inv] using hk⟩

lemma baseGraph_last_neighbors (M : PM n) (k t : ℕ) (hk : 0 < k)
    (hkt : k ≤ t) (ht : t ≤ n) :
    (baseGraph M k t).neighborFinset ⟨k-1,by omega⟩ =
      (prefixSet n t).erase ⟨k-1,by omega⟩ ∪
      univ.filter (fun v : Fin n => t ≤ v.val ∧ (M.val v).val < k) := by
  let w : Fin n := ⟨k-1,by omega⟩
  have hw : w.val < k := by dsimp [w]; omega
  have hw' : w.val+1 = k := by dsimp [w]; omega
  ext u
  simp only [SimpleGraph.mem_neighborFinset, mem_union, mem_erase, prefixSet,
    mem_filter, mem_univ, true_and]
  change (baseGraph M k t).Adj w u ↔ (u ≠ w ∧ u.val < t) ∨ t ≤ u.val ∧ (M.val u).val < k
  constructor
  · rintro ⟨hne,hu | hu | hu | hu⟩
    · exact Or.inl ⟨hne.symm, hu.2⟩
    · right; omega
    · left; exact ⟨hne.symm,by omega⟩
    · by_cases hut : u.val < t
      · exact Or.inl ⟨hne.symm,hut⟩
      · right
        have hp := (partner_eq_symm M w u).mp hu
        exact ⟨by omega,by simpa [hp] using hw⟩
  · rintro (⟨hne,hu⟩ | ⟨hu,hp⟩)
    · exact ⟨hne.symm, Or.inl ⟨by omega,hu⟩⟩
    · exact ⟨by intro h; have := congrArg Fin.val h; omega,
        Or.inr (Or.inl ⟨hw,hu,Or.inr hp⟩)⟩

lemma baseGraph_last_degree (M : PM n) (k t : ℕ) (hk : 0 < k)
    (hkt : k ≤ t) (ht : t ≤ n) :
    (baseGraph M k t).degree ⟨k-1,by omega⟩ = t-1 + cross M k t := by
  let w : Fin n := ⟨k-1,by omega⟩
  have hw : w ∈ prefixSet n t := by simp [prefixSet,w]; omega
  have hd : Disjoint ((prefixSet n t).erase w)
      (univ.filter (fun v : Fin n => t ≤ v.val ∧ (M.val v).val < k)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    have hv₁ := (mem_filter.mp (mem_erase.mp hv).2).2
    have hv₂ := (mem_filter.mp hv').2.1
    omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    baseGraph_last_neighbors M k t hk hkt ht, Finset.card_union_of_disjoint hd,
    card_erase_of_mem hw, prefixSet_card t ht, cross_suffix_count]

#print axioms baseGraph_suffix_degree
#print axioms baseGraph_last_degree
#print axioms baseGraph_early_degree
end Matching370688
```

### `MatchingLargeMiddle.lean`

```lean
import MatchingBaseGraph

namespace Matching370688
open Finset
variable {n : ℕ}

def extraMiddle (M : PM n) (k t : ℕ) : Finset (Fin n) :=
  (middleBlock n k t).filter (fun v => t ≤ (M.val v).val)

/-- The large-middle correction for the explicit base graph, with no
unproved graph or degree profile premises. It preserves every prescribed
matching edge, makes all middle degrees antitone and greater than k, and
leaves every outside degree unchanged. Prefix/suffix counts and the cut
inequality are separate unfinished obligations. -/
theorem large_middle_graph (M : PM n) (k t : ℕ) (h3 : k+3 ≤ t) (ht : t ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
      ∃ r : ℕ, k ≤ r ∧ r ≤ t ∧
      (∀ v, G.Adj v (M.val v)) ∧
      (∀ v ∈ middleBlock n k t, (G.degree v : ℤ) = middleProfile t r v) ∧
      (∀ v ∉ middleBlock n k t, G.degree v = (baseGraph M k t).degree v) ∧
      (∀ u ∈ middleBlock n k t, ∀ v ∈ middleBlock n k t, u ≤ v → G.degree v ≤ G.degree u) ∧
      (∀ v ∈ middleBlock n k t, k < G.degree v) := by
  apply apply_middle_correction M k t h3 ht (extraMiddle M k t)
    (Finset.filter_subset _ _) (fun v hv => (mem_filter.mp hv).2)
    (baseGraph M k t) (baseGraph_contains M k t) (baseGraph_middle_clique M k t)
  intro v hv
  simpa only [extraMiddle, mem_filter, hv, true_and] using baseGraph_middle_degree M k t ht v hv

#print axioms large_middle_graph
end Matching370688
```

### `MatchingLargeWitness.lean`

```lean
import MatchingLargeMiddle
import MatchingBaseDegrees

namespace Matching370688
open Finset
variable {n : ℕ}

/-- The complete sorted graph witness for a middle block of size ≥3.
The missing cut inequality is needed to show this witness excludes N. -/
theorem large_sorted_witness (M : PM n) (k t : ℕ) (hk : 0 < k)
    (h3 : k+3 ≤ t) (ht : t ≤ n) :
    ∃ d : Fin n → ℕ, Antitone d ∧ Realizes d M ∧
      (∀ v, t ≤ v.val → d v = k) ∧
      (∀ v, v.val+1 < k → d v = n-1) ∧
      d ⟨k-1,by omega⟩ = t-1 + cross M k t ∧
      (∀ v, k ≤ v.val → (d v ≤ k ↔ t ≤ v.val)) := by
  classical
  obtain ⟨G,inst,r,hkr,hrt,hm,hmiddle,hout,hanti,hgt⟩ := large_middle_graph M k t h3 ht
  let := inst
  have hearly (v : Fin n) (hv : v.val+1 < k) : G.degree v = n-1 := by
    rw [hout v (by simp [middleBlock]; omega)]
    exact baseGraph_early_degree M k t (by omega) v hv
  have hsuffix (v : Fin n) (hv : t ≤ v.val) : G.degree v = k := by
    rw [hout v (by simp [middleBlock]; omega)]
    exact baseGraph_suffix_degree M k t hk (by omega) ht v hv
  let w : Fin n := ⟨k-1,by omega⟩
  have hlast : G.degree w = t-1 + cross M k t := by
    rw [hout w (by simp [middleBlock,w]; omega)]
    exact baseGraph_last_degree M k t hk (by omega) ht
  have hmidUpper (v : Fin n) (hv : v ∈ middleBlock n k t) : G.degree v ≤ t-1 := by
    have hz := hmiddle v hv
    unfold middleProfile at hz
    split_ifs at hz <;> omega
  have hsorted : Antitone (fun v => G.degree v) := by
    intro u v huv
    change G.degree v ≤ G.degree u
    have huv' : u.val ≤ v.val := huv
    by_cases hue : u.val+1 < k
    · rw [hearly u hue]
      have hh := G.degree_lt_card_verts v
      simp only [Fintype.card_fin] at hh
      omega
    · by_cases hup : u.val < k
      · have huw : u = w := by apply Fin.ext; dsimp [w]; omega
        rw [huw, hlast]
        by_cases hvp : v.val < k
        · have hvw : v = w := by apply Fin.ext; dsimp [w]; omega
          rw [hvw,hlast]
        · by_cases hvt : v.val < t
          · have hvC : v ∈ middleBlock n k t := by simp [middleBlock]; omega
            have hvdeg := hmidUpper v hvC
            omega
          · rw [hsuffix v (by omega)]
            omega
      · by_cases hut : u.val < t
        · have huC : u ∈ middleBlock n k t := by simp [middleBlock]; omega
          by_cases hvt : v.val < t
          · exact hanti u huC v (by simp [middleBlock]; omega) huv
          · rw [hsuffix v (by omega)]
            exact le_of_lt (hgt u huC)
        · rw [hsuffix u (by omega),hsuffix v (by omega)]
  refine ⟨(fun v => G.degree v), hsorted, ?_, hsuffix, hearly, hlast, ?_⟩
  · refine ⟨G, inferInstance, fun _ => rfl, ?_⟩
    intro e he
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp he
    exact hm v
  · intro v hv
    by_cases hvt : t ≤ v.val
    · simp [hsuffix v hvt, hvt]
    · have hvC : v ∈ middleBlock n k t := by simp [middleBlock]; omega
      have hg := hgt v hvC
      simp [hvt, Nat.not_le_of_gt hg]

#print axioms large_sorted_witness
end Matching370688
```

### `MatchingAudit.lean`

```lean
import MatchingRepresentation
import MatchingSanity
import MatchingSixSanity
import MatchingAssembly
import MatchingLargeWitness

namespace Matching370688
#eval Lean.versionString
#print Realizes
#print Prec
#print IsSwitchOf
#print ChainConclusion
#print Conjecture11
#check all_edge_matchings_represented
#check conjecture_11_four
#check six_incomparable
#check middle_correction
#check large_sorted_witness
#check conjecture_11_of_obligations
#print axioms all_edge_matchings_represented
#print axioms conjecture_11_four
#print axioms six_incomparable
#print axioms middle_correction
#print axioms large_sorted_witness
#print axioms conjecture_11_of_obligations
end Matching370688
```

### `MatchingCutCounts.lean`

```lean
import MatchingBaseGraph

namespace Matching370688
open Finset
variable {n : ℕ}

/-- Neighbors of v within an arbitrary finite set S. -/
def neighborsIn (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n) := S.filter (G.Adj v)

lemma neighborsIn_le_card (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (v : Fin n) : (neighborsIn G S v).card ≤ S.card :=
  card_le_card (filter_subset _ _)

lemma neighborsIn_le_degree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (v : Fin n) : (neighborsIn G S v).card ≤ G.degree v := by
  rw [← G.card_neighborFinset_eq_degree]
  apply card_le_card
  intro u hu
  simpa only [SimpleGraph.mem_neighborFinset] using (mem_filter.mp hu).2

lemma neighborsIn_le_degree_sub_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (v q : Fin n) (hq : G.Adj v q) (hout : q ∉ S) :
    (neighborsIn G S v).card ≤ G.degree v - 1 := by
  have hsub : insert q (neighborsIn G S v) ⊆ G.neighborFinset v := by
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · simpa only [SimpleGraph.mem_neighborFinset] using hq
    · simpa only [SimpleGraph.mem_neighborFinset] using (mem_filter.mp hu).2
  have hnot : q ∉ neighborsIn G S v := fun h => hout (mem_filter.mp h).1
  have hh := card_le_card hsub
  rw [card_insert_of_notMem hnot, G.card_neighborFinset_eq_degree] at hh
  omega

lemma neighborsIn_prefix_internal (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hk : k ≤ n) (v : Fin n) (hv : v.val < k) :
    (neighborsIn G (prefixSet n k) v).card ≤ k-1 := by
  have hsub : neighborsIn G (prefixSet n k) v ⊆ (prefixSet n k).erase v := by
    intro u hu
    obtain ⟨huS,ha⟩ := mem_filter.mp hu
    exact mem_erase.mpr ⟨(G.ne_of_adj ha).symm,huS⟩
  have hh := card_le_card hsub
  rw [card_erase_of_mem (by simp [prefixSet,hv]), prefixSet_card k hk] at hh
  exact hh

lemma degree_split (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (v : Fin n) :
    G.degree v = (neighborsIn G S v).card + (neighborsIn G Sᶜ v).card := by
  rw [← G.card_neighborFinset_eq_degree]
  have hu : neighborsIn G S v ∪ neighborsIn G Sᶜ v = G.neighborFinset v := by
    ext u
    simp only [neighborsIn,mem_union,mem_filter,mem_compl,SimpleGraph.mem_neighborFinset]
    tauto
  have hd : Disjoint (neighborsIn G S v) (neighborsIn G Sᶜ v) := by
    apply disjoint_left.mpr
    intro u hu hv
    exact (mem_compl.mp (mem_filter.mp hv).1) (mem_filter.mp hu).1
  rw [← hu,card_union_of_disjoint hd]

lemma sum_neighborsIn_swap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S T : Finset (Fin n)) :
    ∑ v ∈ S, (neighborsIn G T v).card = ∑ v ∈ T, (neighborsIn G S v).card := by
  simp only [neighborsIn,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  simp only [G.adj_comm]

end Matching370688
```

### `MatchingCut.lean`

```lean
import MatchingCutCounts

namespace Matching370688
open Finset
variable {n : ℕ}

def cutBound (d : Fin n → ℕ) (L : PM n) (k : ℕ) : ℕ :=
  k*(k-1) + (∑ v ∈ univ.filter (fun v : Fin n => k ≤ v.val), min (d v-1) k) +
  (univ.filter (fun v : Fin n =>
    v.val < k ∧ k ≤ (L.val v).val ∧ d (L.val v) ≤ k)).card

lemma cut_correction_count (d : Fin n → ℕ) (L : PM n) (k : ℕ) :
    (univ.filter (fun v : Fin n => k ≤ v.val ∧ (L.val v).val < k ∧ d v ≤ k)).card =
    (univ.filter (fun v : Fin n =>
      v.val < k ∧ k ≤ (L.val v).val ∧ d (L.val v) ≤ k)).card := by
  apply card_bij (fun v _ => L.val v)
  · intro v hv
    obtain ⟨_,hv,hp,hd⟩ := mem_filter.mp hv
    simpa only [mem_filter,mem_univ,true_and,L.inv] using And.intro hp (And.intro hv hd)
  · intro v hv w hw h
    have hh := congrArg L.val h
    simpa only [L.inv] using hh
  · intro w hw
    obtain ⟨_,hw,hp,hd⟩ := mem_filter.mp hw
    refine ⟨L.val w,?_,L.inv w⟩
    simpa only [mem_filter,mem_univ,true_and,L.inv] using And.intro hp (And.intro hw hd)

/-- Matching-sensitive cut necessity, proved directly by counting neighbors. -/
theorem matching_cut {d : Fin n → ℕ} {L : PM n} (h : Realizes d L) {k : ℕ}
    (hk : k ≤ n) :
    (∑ v ∈ univ.filter (fun v : Fin n => v.val < k), d v) ≤ cutBound d L k := by
  classical
  obtain ⟨G,inst,hd,hL⟩ := h
  let := inst
  have hpartner (v : Fin n) : G.Adj v (L.val v) := hL _ (L.edge_mem v)
  have hbound (v : Fin n) :
      (neighborsIn G (prefixSet n k) v).card ≤ min (d v-1) k +
        if (L.val v).val < k ∧ d v ≤ k then 1 else 0 := by
    have hc := neighborsIn_le_card G (prefixSet n k) v
    rw [prefixSet_card k hk] at hc
    have hdv := neighborsIn_le_degree G (prefixSet n k) v
    rw [hd v] at hdv
    by_cases hp : (L.val v).val < k
    · by_cases hlow : d v ≤ k
      · simp only [hp,hlow,and_self,ite_true]
        have he : min (d v-1) k = d v-1 := min_eq_left (by omega)
        rw [he]
        omega
      · simp only [hp,hlow,and_false,ite_false,add_zero]
        rw [min_eq_right (by omega)]
        exact hc
    · have hh := neighborsIn_le_degree_sub_one G (prefixSet n k) v (L.val v)
          (hpartner v) (by simpa [prefixSet] using hp)
      rw [hd v] at hh
      simp only [hp,false_and,ite_false,add_zero]
      exact le_min hh hc
  have hint : (∑ v ∈ prefixSet n k, (neighborsIn G (prefixSet n k) v).card) ≤ k*(k-1) := by
    calc
      _ ≤ ∑ _v ∈ prefixSet n k, (k-1) := by
        apply sum_le_sum
        intro v hv
        exact neighborsIn_prefix_internal G k hk v (mem_filter.mp hv).2
      _ = k*(k-1) := by simp [prefixSet_card k hk]
  have hout : (∑ v ∈ (prefixSet n k)ᶜ, (neighborsIn G (prefixSet n k) v).card) ≤
      (∑ v ∈ univ.filter (fun v : Fin n => k ≤ v.val), min (d v-1) k) +
      (univ.filter (fun v : Fin n =>
        v.val < k ∧ k ≤ (L.val v).val ∧ d (L.val v) ≤ k)).card := by
    calc
      _ ≤ ∑ v ∈ (prefixSet n k)ᶜ,
          (min (d v-1) k + if (L.val v).val < k ∧ d v ≤ k then 1 else 0) :=
        sum_le_sum (fun v _ => hbound v)
      _ = _ := by
        rw [sum_add_distrib]
        have hcomp : (prefixSet n k)ᶜ = univ.filter (fun v : Fin n => k ≤ v.val) := by
          ext v; simp [prefixSet,not_lt]
        rw [hcomp]
        congr 1
        rw [← cut_correction_count d L k]
        simp only [card_eq_sum_ones,sum_filter]
        apply sum_congr rfl
        intro v hv
        by_cases hkv : k ≤ v.val <;> simp [hkv]
  change (∑ v ∈ prefixSet n k, d v) ≤ _
  have hsplit : (∑ v ∈ prefixSet n k, d v) =
      (∑ v ∈ prefixSet n k, (neighborsIn G (prefixSet n k) v).card) +
      (∑ v ∈ (prefixSet n k)ᶜ, (neighborsIn G (prefixSet n k) v).card) := by
    simp_rw [← hd, degree_split G (prefixSet n k)]
    rw [sum_add_distrib, sum_neighborsIn_swap G (prefixSet n k) (prefixSet n k)ᶜ]
  rw [hsplit]
  simpa only [cutBound,add_assoc] using add_le_add hint hout

#print axioms matching_cut
end Matching370688
```

### `MatchingCutEvaluation.lean`

```lean
import MatchingCut
import MatchingLargeWitness
import Mathlib.Tactic.Linarith

namespace Matching370688
open Finset
variable {n : ℕ}

lemma suffixSet_card (t : ℕ) (ht : t ≤ n) :
    (univ.filter (fun v : Fin n => t ≤ v.val)).card = n-t := by
  have he : univ.filter (fun v : Fin n => t ≤ v.val) = (prefixSet n t)ᶜ := by
    ext v; simp [prefixSet,not_lt]
  rw [he,card_compl,prefixSet_card t ht]
  simp

lemma middleBlock_card (k t : ℕ) (hkt : k ≤ t) (ht : t ≤ n) :
    (middleBlock n k t).card = t-k := by
  have he : middleBlock n k t = prefixSet n t \ prefixSet n k := by
    ext v; simp [middleBlock,prefixSet]; omega
  have hsub : prefixSet n k ⊆ prefixSet n t := by
    intro v hv; simp only [prefixSet,mem_filter,mem_univ,true_and] at *; omega
  rw [he,card_sdiff_of_subset hsub,prefixSet_card t ht,prefixSet_card (n := n) k (by omega)]

lemma witness_prefix_sum (M : PM n) (k t : ℕ) (hk : 0 < k) (hkt : k ≤ t)
    (ht : t ≤ n) (d : Fin n → ℕ)
    (hearly : ∀ v, v.val+1 < k → d v = n-1)
    (hlast : d ⟨k-1,by omega⟩ = t-1 + cross M k t) :
    (∑ v ∈ prefixSet n k, d v) = (k-1)*(n-1)+(t-1)+cross M k t := by
  let w : Fin n := ⟨k-1,by omega⟩
  have hw : w ∈ prefixSet n k := by simp [prefixSet,w]; omega
  have he : ∑ v ∈ (prefixSet n k).erase w, d v = (k-1)*(n-1) := by
    calc
      _ = ∑ _v ∈ (prefixSet n k).erase w, (n-1) := by
        apply sum_congr rfl
        intro v hv
        obtain ⟨hne,hv⟩ := mem_erase.mp hv
        have hvk := (mem_filter.mp hv).2
        have hnev : v.val ≠ k-1 := by simpa only [ne_eq,Fin.ext_iff] using hne
        exact hearly v (by omega)
      _ = _ := by simp [card_erase_of_mem hw,prefixSet_card (n := n) k (by omega)]
  have hs := sum_erase_add (prefixSet n k) d hw
  rw [he,hlast] at hs
  omega

lemma witness_cutBound (L : PM n) (k t : ℕ) (hk : 0 < k) (hkt : k ≤ t)
    (ht : t ≤ n) (d : Fin n → ℕ)
    (hsuffix : ∀ v, t ≤ v.val → d v = k)
    (hlow : ∀ v, k ≤ v.val → (d v ≤ k ↔ t ≤ v.val)) :
    cutBound d L k = (k-1)*(n-1)+(t-1)+cross L k t := by
  classical
  have hsum : (∑ v ∈ univ.filter (fun v : Fin n => k ≤ v.val), min (d v-1) k) =
      (t-k)*k+(n-t)*(k-1) := by
    have hu : univ.filter (fun v : Fin n => k ≤ v.val) =
        middleBlock n k t ∪ univ.filter (fun v : Fin n => t ≤ v.val) := by
      ext v; simp [middleBlock]; omega
    have hdis : Disjoint (middleBlock n k t) (univ.filter (fun v : Fin n => t ≤ v.val)) := by
      apply disjoint_left.mpr
      intro v hv hv'
      have := (mem_filter.mp hv).2
      have := (mem_filter.mp hv').2
      omega
    rw [hu,sum_union hdis]
    have hm : (∑ v ∈ middleBlock n k t, min (d v-1) k) = (t-k)*k := by
      calc
        _ = ∑ _v ∈ middleBlock n k t, k := by
          apply sum_congr rfl
          intro v hv
          obtain ⟨_,hv,hvt⟩ := mem_filter.mp hv
          have hh : ¬ d v ≤ k := by rw [hlow v hv]; omega
          exact min_eq_right (by omega)
        _ = _ := by simp [middleBlock_card k t hkt ht]
    have hb : (∑ v ∈ univ.filter (fun v : Fin n => t ≤ v.val), min (d v-1) k) =
        (n-t)*(k-1) := by
      calc
        _ = ∑ _v ∈ univ.filter (fun v : Fin n => t ≤ v.val), (k-1) := by
          apply sum_congr rfl
          intro v hv
          rw [hsuffix v (mem_filter.mp hv).2,min_eq_left (by omega)]
        _ = _ := by simp [suffixSet_card t ht]
    rw [hm,hb]
  have hcorr : (univ.filter (fun v : Fin n =>
      v.val < k ∧ k ≤ (L.val v).val ∧ d (L.val v) ≤ k)).card = cross L k t := by
    unfold cross
    congr 1
    ext v
    simp only [mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨hv,hp,hd⟩
      exact ⟨hv,(hlow _ hp).mp hd⟩
    · rintro ⟨hv,hp⟩
      exact ⟨hv,by omega,(hlow _ (by omega)).mpr hp⟩
  unfold cutBound
  rw [hsum,hcorr]
  have hk1 : k-1+1=k := by omega
  have hn1 : n-1+1=n := by omega
  have ht1 : t-1+1=t := by omega
  have htk : t-k+k=t := by omega
  have hnt : n-t+t=n := by omega
  nlinarith

/-- Any witness with the stated prefix and exact low suffix separates the matchings. -/
theorem witness_separates (M N : PM n) (k t : ℕ) (hk : 0 < k) (hkt : k ≤ t)
    (ht : t ≤ n) (hcross : cross N k t < cross M k t)
    (d : Fin n → ℕ) (hearly : ∀ v, v.val+1 < k → d v = n-1)
    (hlast : d ⟨k-1,by omega⟩ = t-1 + cross M k t)
    (hsuffix : ∀ v, t ≤ v.val → d v = k)
    (hlow : ∀ v, k ≤ v.val → (d v ≤ k ↔ t ≤ v.val)) : ¬ Realizes d N := by
  intro hn
  have hc := matching_cut hn (by omega : k ≤ n)
  change (∑ v ∈ prefixSet n k, d v) ≤ _ at hc
  rw [witness_prefix_sum M k t hk hkt ht d hearly hlast,
    witness_cutBound N k t hk hkt ht d hsuffix hlow] at hc
  omega

theorem large_block_separator (M N : PM n) (k t : ℕ) (hk : 0 < k)
    (h3 : k+3 ≤ t) (ht : t ≤ n) (hcross : cross N k t < cross M k t) :
    ∃ d, Antitone d ∧ Realizes d M ∧ ¬ Realizes d N := by
  obtain ⟨d,ha,hm,hs,he,hl,hlo⟩ := large_sorted_witness M k t hk h3 ht
  exact ⟨d,ha,hm,witness_separates M N k t hk (by omega) ht hcross d he hl hs hlo⟩

#print axioms matching_cut
#print axioms witness_cutBound
#print axioms large_block_separator
end Matching370688
```

### `MatchingSmallWitness.lean`

```lean
import MatchingCutEvaluation

namespace Matching370688
open Finset
variable {n : ℕ}

/-- The uncorrected base graph suffices whenever its middle degrees are sorted
and strictly exceed the suffix degree. These are verified for normalized small blocks. -/
theorem base_sorted_separator (M N : PM n) (k t : ℕ) (hk : 0 < k)
    (hkt : k ≤ t) (ht : t ≤ n) (hcross : cross N k t < cross M k t)
    (hanti : ∀ u ∈ middleBlock n k t, ∀ v ∈ middleBlock n k t, u ≤ v →
      (if t ≤ (M.val v).val then 1 else 0) ≤ (if t ≤ (M.val u).val then 1 else 0))
    (hgt : ∀ v ∈ middleBlock n k t, k < t-1+(if t ≤ (M.val v).val then 1 else 0)) :
    ∃ d, Antitone d ∧ Realizes d M ∧ ¬ Realizes d N := by
  let G := baseGraph M k t
  let d := fun v => G.degree v
  let w : Fin n := ⟨k-1,by omega⟩
  have hearly (v : Fin n) (hv : v.val+1 < k) : d v = n-1 :=
    baseGraph_early_degree M k t hkt v hv
  have hsuffix (v : Fin n) (hv : t ≤ v.val) : d v = k :=
    baseGraph_suffix_degree M k t hk hkt ht v hv
  have hlast : d w = t-1+cross M k t := baseGraph_last_degree M k t hk hkt ht
  have hmiddle (v : Fin n) (hv : v ∈ middleBlock n k t) :
      d v = t-1+(if t ≤ (M.val v).val then 1 else 0) := baseGraph_middle_degree M k t ht v hv
  have hmgt (v : Fin n) (hv : v ∈ middleBlock n k t) : k < d v := by
    rw [hmiddle v hv]; exact hgt v hv
  have hsorted : Antitone d := by
    intro u v huv
    have huv' : u.val ≤ v.val := huv
    by_cases hue : u.val+1 < k
    · rw [hearly u hue]
      have hh := G.degree_lt_card_verts v
      simp only [Fintype.card_fin] at hh
      change d v ≤ _
      dsimp [d]; omega
    · by_cases hup : u.val < k
      · have huw : u = w := by apply Fin.ext; dsimp [w]; omega
        rw [huw,hlast]
        by_cases hvp : v.val < k
        · have hvw : v = w := by apply Fin.ext; dsimp [w]; omega
          rw [hvw,hlast]
        · by_cases hvt : v.val < t
          · rw [hmiddle v (by simp [middleBlock]; omega)]
            split_ifs <;> omega
          · rw [hsuffix v (by omega)]; omega
      · by_cases hut : u.val < t
        · have huC : u ∈ middleBlock n k t := by simp [middleBlock]; omega
          by_cases hvt : v.val < t
          · have hvC : v ∈ middleBlock n k t := by simp [middleBlock]; omega
            rw [hmiddle u huC,hmiddle v hvC]
            exact Nat.add_le_add_left (hanti u huC v hvC huv) _
          · rw [hsuffix v (by omega)]
            exact le_of_lt (hmgt u huC)
        · rw [hsuffix u (by omega),hsuffix v (by omega)]
  have hlow (v : Fin n) (hv : k ≤ v.val) : d v ≤ k ↔ t ≤ v.val := by
    by_cases hvt : t ≤ v.val
    · simp [hsuffix v hvt,hvt]
    · have hvC : v ∈ middleBlock n k t := by simp [middleBlock]; omega
      have hh := hmgt v hvC
      simp [hvt,Nat.not_le_of_gt hh]
  refine ⟨d,hsorted,?_,witness_separates M N k t hk hkt ht hcross d hearly hlast hsuffix hlow⟩
  refine ⟨G,inferInstance,fun _ => rfl,?_⟩
  intro e he
  obtain ⟨v,_,rfl⟩ := mem_image.mp he
  exact baseGraph_contains M k t v

/-- Normalized small blocks: empty; singleton with suffix partner; or sorted
binary increments on a two-vertex block. -/
theorem normalized_small_separator (M N : PM n) (k t : ℕ) (hk : 0 < k)
    (hkt : k ≤ t) (ht : t ≤ n) (hsmall : t ≤ k+2)
    (hcross : cross N k t < cross M k t)
    (hone : t = k+1 → ∀ v : Fin n, v.val = k → t ≤ (M.val v).val)
    (htwo : t = k+2 → ∀ u v : Fin n, u.val = k → v.val = k+1 →
      t ≤ (M.val v).val → t ≤ (M.val u).val) :
    ∃ d, Antitone d ∧ Realizes d M ∧ ¬ Realizes d N := by
  apply base_sorted_separator M N k t hk hkt ht hcross
  · intro u hu v hv huv
    obtain ⟨_,huk,hut⟩ := mem_filter.mp hu
    obtain ⟨_,hvk,hvt⟩ := mem_filter.mp hv
    by_cases heq : u = v
    · subst v; exact le_rfl
    have huv' : u.val < v.val := lt_of_le_of_ne huv (fun h => heq (Fin.ext h))
    have ht2 : t = k+2 := by omega
    have huk' : u.val = k := by omega
    have hvk' : v.val = k+1 := by omega
    by_cases hpv : t ≤ (M.val v).val
    · have hpu := htwo ht2 u v huk' hvk' hpv
      simp [hpv,hpu]
    · simp [hpv]
  · intro v hv
    obtain ⟨_,hvk,hvt⟩ := mem_filter.mp hv
    by_cases ht2 : t = k+2
    · split_ifs <;> omega
    · have ht1 : t = k+1 := by omega
      have hp := hone ht1 v (by omega)
      simp only [hp,ite_true]
      omega

#print axioms normalized_small_separator
end Matching370688
```

### `MatchingBoundaryCounts.lean`

```lean
import MatchingBaseDegrees

namespace Matching370688
open Finset
variable {n : ℕ}

lemma filter_prefix_step (p : Fin n → Prop) [DecidablePred p] (k : ℕ) (hk : k < n) :
    (univ.filter (fun v : Fin n => v.val < k+1 ∧ p v)).card =
      (univ.filter (fun v : Fin n => v.val < k ∧ p v)).card +
        if p ⟨k,hk⟩ then 1 else 0 := by
  classical
  let q : Fin n := ⟨k,hk⟩
  by_cases hp : p q
  · have he : univ.filter (fun v : Fin n => v.val < k+1 ∧ p v) =
        insert q (univ.filter (fun v : Fin n => v.val < k ∧ p v)) := by
      ext v
      simp only [mem_filter,mem_univ,true_and,mem_insert]
      constructor
      · rintro ⟨hv,hpv⟩
        by_cases heq : v.val = k
        · left; apply Fin.ext; exact heq
        · right; exact ⟨by omega,hpv⟩
      · rintro (rfl | ⟨hv,hpv⟩)
        · exact ⟨by dsimp [q]; omega,hp⟩
        · exact ⟨by omega,hpv⟩
    have hnot : q ∉ univ.filter (fun v : Fin n => v.val < k ∧ p v) := by simp [q]
    rw [he,card_insert_of_notMem hnot]
    simp only [show p ⟨k,hk⟩ from hp,ite_true]
  · have he : univ.filter (fun v : Fin n => v.val < k+1 ∧ p v) =
        univ.filter (fun v : Fin n => v.val < k ∧ p v) := by
      ext v
      simp only [mem_filter,mem_univ,true_and]
      constructor
      · rintro ⟨hv,hpv⟩
        have hne : v.val ≠ k := by
          intro heq
          have heq' : v = q := by apply Fin.ext; exact heq
          exact hp (heq' ▸ hpv)
        exact ⟨by omega,hpv⟩
      · rintro ⟨hv,hpv⟩; exact ⟨by omega,hpv⟩
    rw [he]
    simp only [show ¬ p ⟨k,hk⟩ from hp,ite_false,add_zero]

lemma cross_prefix_step (L : PM n) (k t : ℕ) (hk : k < n) :
    cross L (k+1) t = cross L k t + if t ≤ (L.val ⟨k,hk⟩).val then 1 else 0 :=
  filter_prefix_step (fun v => t ≤ (L.val v).val) k hk

lemma cross_suffix_step (L : PM n) (k t : ℕ) (ht : t < n) :
    cross L k t = cross L k (t+1) + if (L.val ⟨t,ht⟩).val < k then 1 else 0 := by
  classical
  have htot (s : ℕ) :
      (univ.filter (fun v : Fin n => v.val < s ∧ (L.val v).val < k)).card + cross L k s = (prefixSet n k).card := by
    rw [← cross_suffix_count]
    have hd : Disjoint
        (univ.filter (fun v : Fin n => v.val < s ∧ (L.val v).val < k))
        (univ.filter (fun v : Fin n => s ≤ v.val ∧ (L.val v).val < k)) := by
      apply disjoint_left.mpr
      intro v hv hv'
      simp only [mem_filter,mem_univ,true_and] at *
      omega
    have hu : (univ.filter (fun v : Fin n => v.val < s ∧ (L.val v).val < k)) ∪
        (univ.filter (fun v : Fin n => s ≤ v.val ∧ (L.val v).val < k)) =
        univ.filter (fun v : Fin n => (L.val v).val < k) := by
      ext v; simp; omega
    rw [← card_union_of_disjoint hd,hu]
    have he : (univ.filter (fun v : Fin n => (L.val v).val < k)).card =
        (prefixSet n k).card := by
      apply card_bij (fun v _ => L.val v)
      · intro v hv; simpa [prefixSet] using (mem_filter.mp hv).2
      · intro v hv w hw heq
        have := congrArg L.val heq
        simpa only [L.inv] using this
      · intro w hw
        exact ⟨L.val w,by simpa [L.inv,prefixSet] using hw,L.inv w⟩
    rw [he]
  have h1 := htot t
  have h2 := htot (t+1)
  have h3 := filter_prefix_step (fun v => (L.val v).val < k) t ht
  omega

end Matching370688
```

### `MatchingSmallBlocks.lean`

```lean
import MatchingSmallWitness
import MatchingBoundaryCounts

namespace Matching370688
variable {n : ℕ}

lemma singleton_block_separator (M N : PM n) (k : ℕ) (hk : 0 < k)
    (ht : k+1 ≤ n) (hcross : cross N k (k+1) < cross M k (k+1)) :
    ∃ d, Antitone d ∧ Realizes d M ∧ ¬ Realizes d N := by
  let u : Fin n := ⟨k,by omega⟩
  by_cases hp : k+1 ≤ (M.val u).val
  · apply normalized_small_separator M N k (k+1) hk (by omega) ht (by omega) hcross
    · intro _ v hv
      have hvu : v = u := by apply Fin.ext; exact hv
      simpa [hvu] using hp
    · intro h; omega
  · have hne := M.free u
    have hne' : (M.val u).val ≠ k := by
      intro heq; exact hne (Fin.ext heq)
    have hpre : (M.val u).val < k := by omega
    have hm := cross_suffix_step M k k (by omega)
    have hn := cross_suffix_step N k k (by omega)
    have hnew : cross N k k < cross M k k := by
      change cross M k k = cross M k (k+1) + (if (M.val u).val < k then 1 else 0) at hm
      rw [ite_eq_left hpre] at hm
      split_ifs at hn <;> omega
    apply normalized_small_separator M N k k hk (by omega) (by omega) (by omega) hnew
    · intro h; omega
    · intro h; omega

lemma double_block_separator (M N : PM n) (k : ℕ) (hk : 0 < k)
    (ht : k+2 ≤ n) (hcross : cross N k (k+2) < cross M k (k+2)) :
    ∃ d, Antitone d ∧ Realizes d M ∧ ¬ Realizes d N := by
  let u : Fin n := ⟨k,by omega⟩
  let v : Fin n := ⟨k+1,by omega⟩
  by_cases hbad : ¬ (k+2 ≤ (M.val v).val → k+2 ≤ (M.val u).val)
  · have hvB : k+2 ≤ (M.val v).val := by tauto
    have huNot : ¬ k+2 ≤ (M.val u).val := by tauto
    have hune : (M.val u).val ≠ k := by
      intro heq; exact M.free u (Fin.ext heq)
    have hunv : (M.val u).val ≠ k+1 := by
      intro heq
      have huv : M.val u = v := Fin.ext heq
      have hvu : M.val v = u := (partner_eq_symm M u v).mp huv
      rw [hvu] at hvB
      dsimp [u] at hvB
      omega
    have huS : (M.val u).val < k := by omega
    by_cases hNu : k+2 ≤ (N.val u).val
    · have hm0 := cross_suffix_step M k k (by omega)
      have hm1 := cross_suffix_step M k (k+1) (by omega)
      have hn0 := cross_suffix_step N k k (by omega)
      have hn1 := cross_suffix_step N k (k+1) (by omega)
      change cross M k k = cross M k (k+1) + (if (M.val u).val < k then 1 else 0) at hm0
      change cross M k (k+1) = cross M k (k+2) + (if (M.val v).val < k then 1 else 0) at hm1
      change cross N k k = cross N k (k+1) + (if (N.val u).val < k then 1 else 0) at hn0
      change cross N k (k+1) = cross N k (k+2) + (if (N.val v).val < k then 1 else 0) at hn1
      rw [ite_eq_left huS] at hm0
      rw [ite_eq_right (by omega)] at hm1 hn0
      have hnew : cross N k k < cross M k k := by
        split_ifs at hn1 <;> omega
      apply normalized_small_separator M N k k hk (by omega) (by omega) (by omega) hnew
      · intro h; omega
      · intro h; omega
    · have hm := cross_prefix_step M k (k+2) (by omega)
      have hn := cross_prefix_step N k (k+2) (by omega)
      change cross M (k+1) (k+2) = cross M k (k+2) + (if k+2 ≤ (M.val u).val then 1 else 0) at hm
      change cross N (k+1) (k+2) = cross N k (k+2) + (if k+2 ≤ (N.val u).val then 1 else 0) at hn
      rw [ite_eq_right huNot] at hm
      rw [ite_eq_right hNu] at hn
      apply singleton_block_separator M N (k+1) (by omega) (by omega)
      simpa only [Nat.add_assoc] using
        (show cross N (k+1) (k+2) < cross M (k+1) (k+2) from by omega)
  · have hgood : k+2 ≤ (M.val v).val → k+2 ≤ (M.val u).val := by tauto
    apply normalized_small_separator M N k (k+2) hk (by omega) ht (by omega) hcross
    · intro h; omega
    · intro _ a b ha hb hpb
      have hau : a = u := Fin.ext ha
      have hbv : b = v := Fin.ext hb
      simpa [hau,hbv] using hgood (by simpa [hbv] using hpb)

/-- Both boundary reductions, with the normalized small-block degree bookkeeping. -/
theorem small_block_separator (M N : PM n) (k t : ℕ) (hk : 0 < k)
    (hkt : k ≤ t) (ht : t ≤ n) (hsmall : t ≤ k+2)
    (hcross : cross N k t < cross M k t) :
    ∃ d, Antitone d ∧ Realizes d M ∧ ¬ Realizes d N := by
  have hc : t = k ∨ t = k+1 ∨ t = k+2 := by omega
  rcases hc with hc | hc | hc
  · subst t
    apply normalized_small_separator M N k k hk hkt ht hsmall hcross
    · intro h; omega
    · intro h; omega
  · subst t
    exact singleton_block_separator M N k hk ht hcross
  · subst t
    exact double_block_separator M N k hk ht hcross

theorem separating_graph (M N : PM n) (k t : ℕ) (hk : 0 < k)
    (hkt : k ≤ t) (ht : t < n) (hcross : cross N k t < cross M k t) :
    ∃ d, Antitone d ∧ Realizes d M ∧ ¬ Realizes d N := by
  by_cases hsmall : t ≤ k+2
  · exact small_block_separator M N k t hk hkt (by omega) hsmall hcross
  · exact large_block_separator M N k t hk (by omega) (by omega) hcross

#print axioms small_block_separator
#print axioms separating_graph
end Matching370688
```

### `MatchingRankConsequences.lean`

```lean
import MatchingSmallBlocks
import MatchingAssembly

namespace Matching370688
variable {n : ℕ}

/-- Literal preorder implies all rank inequalities; no separator premise remains. -/
theorem prec_rank_unconditional {N M : PM n} (h : Prec N M) : RankLE M N :=
  prec_rank separating_graph h

theorem prec_cross_unconditional {N M : PM n} (h : Prec N M)
    (k t : ℕ) (hk : 0 < k) (hkt : k ≤ t) (ht : t < n) :
    cross M k t ≤ cross N k t := prec_cross separating_graph h k t hk hkt ht

/-- The realization preorder is antisymmetric (source Conjecture 12). -/
theorem prec_antisymm {N M : PM n} (hNM : Prec N M) (hMN : Prec M N) : N = M := by
  have h1 := prec_rank_unconditional hNM
  have h2 := prec_rank_unconditional hMN
  apply rank_ext
  intro i j
  have hsat (L : PM n) (i j : ℕ) : rank L i j = rank L (min i n) (min j n) := by
    unfold rank
    congr 1
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    have hv := v.isLt
    have hp := (L.val v).isLt
    omega
  rw [hsat N i j,hsat M i j]
  exact Nat.le_antisymm (h1 _ (Nat.min_le_right _ _) _ (Nat.min_le_right _ _))
    (h2 _ (Nat.min_le_right _ _) _ (Nat.min_le_right _ _))

/-- The separator obligation has been discharged; only the rank step and
source Lemma 10(b) remain as mathematical inputs to Conjecture 11. -/
theorem conjecture_11_of_rank_step_and_10b
    (step : ∀ A B : PM n, RankLE A B → A ≠ B →
      ∃ P, IsSwitchOf P A ∧ RankLE P B ∧ potential P B < potential A B)
    (monotone : ∀ A B : PM n, IsSwitchOf A B → Prec A B)
    (N M : PM n) (h : Prec N M) :
    ∃ L : List (PM n), L ≠ [] ∧ L.head? = some N ∧ L.getLast? = some M ∧
      L.Chain' (fun A B => Prec A B ∧ IsSwitchOf A B) :=
  rank_chain step monotone (prec_rank_unconditional h)

#print axioms prec_rank_unconditional
#print axioms prec_antisymm
#print axioms conjecture_11_of_rank_step_and_10b
end Matching370688
```

### `MatchingFirstDisagreement.lean`

```lean
import MatchingRankBridge

namespace Matching370688
open Finset
variable {n : ℕ}

/-- First disagreement and the first admissible later row, exactly the choices
in the direct rank-defect proof. Labels in this file are zero-based. -/
theorem first_disagreement_choice (M N : PM n) (h : RankLE M N) (hne : M ≠ N) :
    ∃ i j : Fin n,
      (∀ u, u < i → M.val u = N.val u) ∧ M.val i ≠ N.val i ∧
      i < M.val i ∧ M.val i < M.val j ∧ M.val j ≤ N.val i ∧ i < j ∧
      j ≠ M.val i ∧
      (∀ u, i < u → u < j → ¬ (M.val i < M.val u ∧ M.val u ≤ N.val i)) := by
  classical
  let S := univ.filter (fun u : Fin n => M.val u ≠ N.val u)
  have hS : S.Nonempty := by
    by_contra hempty
    apply hne
    apply Subtype.ext
    funext u
    by_contra hu
    exact hempty ⟨u,mem_filter.mpr ⟨mem_univ _,hu⟩⟩
  let i := S.min' hS
  have hiS : i ∈ S := min'_mem S hS
  have hiNe : M.val i ≠ N.val i := (mem_filter.mp hiS).2
  have hbefore (u : Fin n) (hu : u < i) : M.val u = N.val u := by
    by_contra huNe
    have hmem : u ∈ S := mem_filter.mpr ⟨mem_univ _,huNe⟩
    have := min'_le S u hmem
    change i ≤ u at this
    exact (not_le_of_gt hu) this
  have hrank (q : ℕ) : rank M i.val q = rank N i.val q := by
    unfold rank
    congr 1
    ext u
    simp only [mem_filter,mem_univ,true_and]
    by_cases hu : u.val < i.val
    · rw [hbefore u hu]
    · simp [hu]
  have hac : M.val i < N.val i := by
    have hm := rank_succ_left M i.val ((N.val i).val+1) i.isLt
    have hn := rank_succ_left N i.val ((N.val i).val+1) i.isLt
    have hc := h (i.val+1) (by omega) ((N.val i).val+1) (by have := (N.val i).isLt; omega)
    change rank M (i.val+1) ((N.val i).val+1) = rank M i.val ((N.val i).val+1) +
      (if (M.val i).val < (N.val i).val+1 then 1 else 0) at hm
    change rank N (i.val+1) ((N.val i).val+1) = rank N i.val ((N.val i).val+1) +
      (if (N.val i).val < (N.val i).val+1 then 1 else 0) at hn
    rw [hrank] at hm
    have hneval : (M.val i).val ≠ (N.val i).val := fun heq => hiNe (Fin.ext heq)
    split_ifs at hm hn <;> change (M.val i).val < (N.val i).val <;> omega
  have hia : i < M.val i := by
    have hf := M.free i
    by_contra hia
    have hai : M.val i < i := lt_of_le_of_ne (le_of_not_gt hia) hf
    have hh := hbefore (M.val i) hai
    rw [M.inv] at hh
    have hh' := congrArg N.val hh
    rw [N.inv] at hh'
    exact hiNe hh'.symm
  have hic : i < N.val i := lt_trans hia hac
  let j0 := M.val (N.val i)
  have hij0 : i < j0 := by
    by_contra hij
    have hle : j0 ≤ i := le_of_not_gt hij
    by_cases heq : j0 = i
    · have hh := congrArg M.val heq
      dsimp [j0] at hh
      rw [M.inv] at hh
      exact hiNe hh.symm
    · have hh := hbefore j0 (lt_of_le_of_ne hle heq)
      dsimp [j0] at hh
      rw [M.inv] at hh
      have hh' := congrArg N.val hh
      rw [N.inv,N.inv] at hh'
      have : j0 = i := hh'.symm
      exact heq this
  let T := univ.filter (fun u : Fin n => i < u ∧ M.val i < M.val u ∧ M.val u ≤ N.val i)
  have hT : T.Nonempty := by
    refine ⟨j0,mem_filter.mpr ⟨mem_univ _,hij0,?_,?_⟩⟩
    · simpa only [j0,M.inv] using hac
    · simp only [j0,M.inv,le_refl]
  let j := T.min' hT
  have hjT := (mem_filter.mp (min'_mem T hT)).2
  change i < j ∧ M.val i < M.val j ∧ M.val j ≤ N.val i at hjT
  have hjna : j ≠ M.val i := by
    intro heq
    have hh := hjT.2.1
    rw [heq,M.inv] at hh
    exact (not_lt_of_gt hia) hh
  refine ⟨i,j,hbefore,hiNe,hia,hjT.2.1,hjT.2.2,hjT.1,hjna,?_⟩
  intro u hiu huj hu
  have huT : u ∈ T := mem_filter.mpr ⟨mem_univ _,hiu,hu⟩
  have := min'_le T u huT
  change j ≤ u at this
  exact (not_le_of_gt huj) this

#print axioms first_disagreement_choice
end Matching370688
```

### `MatchingRewire.lean`

```lean
import MatchingBaseGraph
import Mathlib.Logic.Equiv.Basic

namespace Matching370688
open Finset
variable {n : ℕ}

/-- Conjugating the partner involution by a transposition stays a perfect matching. -/
def rewire (M : PM n) (i j : Fin n) : PM n :=
  ⟨fun v => Equiv.swap i j (M.val (Equiv.swap i j v)), by
    constructor
    · intro v
      simp only [Equiv.swap_apply_self,M.inv]
    · intro v hv
      have hh := congrArg (Equiv.swap i j) hv
      simp only [Equiv.swap_apply_self] at hh
      exact M.free _ hh⟩

lemma rewire_apply (M : PM n) (i j : Fin n) (hij : i ≠ j)
    (haj : M.val i ≠ j) (hbi : M.val j ≠ i) (v : Fin n) :
    (rewire M i j).val v =
      if v=i then M.val j else if v=j then M.val i else
      if v=M.val i then j else if v=M.val j then i else M.val v := by
  have hab : M.val i ≠ M.val j := fun h => hij (M.property.1.injective h)
  have hai := M.free i
  have hbj := M.free j
  by_cases hvi : v=i
  · subst v
    simp [rewire,Equiv.swap_apply_of_ne_of_ne,hbi,hbj]
  · by_cases hvj : v=j
    · subst v
      simp [rewire,Equiv.swap_apply_of_ne_of_ne,hai,haj,hij.symm]
    · by_cases hva : v=M.val i
      · subst v
        simp [rewire,Equiv.swap_apply_of_ne_of_ne,hai,haj,M.inv]
      · by_cases hvb : v=M.val j
        · subst v
          simp [rewire,Equiv.swap_apply_of_ne_of_ne,hbi,hbj,hab.symm,M.inv]
        · have hpi : M.val v ≠ i := by
            intro heq
            have := congrArg M.val heq
            rw [M.inv] at this
            exact hva this
          have hpj : M.val v ≠ j := by
            intro heq
            have := congrArg M.val heq
            rw [M.inv] at this
            exact hvb this
          simp [rewire,Equiv.swap_apply_of_ne_of_ne,hvi,hvj,hva,hvb,hpi,hpj]

/-- Exact removed and inserted edge sets, before classifying their label order. -/
lemma rewire_differences (M : PM n) (i j : Fin n) (hij : i ≠ j)
    (haj : M.val i ≠ j) (hbi : M.val j ≠ i) :
    M.E \ (rewire M i j).E = {s(i,M.val i),s(j,M.val j)} ∧
    (rewire M i j).E \ M.E = {s(i,M.val j),s(j,M.val i)} := by
  have hab : M.val i ≠ M.val j := fun h => hij (M.property.1.injective h)
  have hai := M.free i
  have hbj := M.free j
  have hia := hai.symm
  have hjb := hbj.symm
  have hja := haj.symm
  have hib := hbi.symm
  constructor <;> ext e <;> induction e using Sym2.ind with
  | _ u v =>
    simp only [mem_sdiff,PM.mem_E_iff,mem_insert,mem_singleton,Sym2.eq_iff,
      rewire_apply M i j hij haj hbi]
    by_cases hui : u=i
    · subst u; simp_all; aesop
    · by_cases huj : u=j
      · subst u; simp_all; aesop
      · by_cases hua : u=M.val i
        · subst u; simp_all [M.inv]; aesop
        · by_cases hub : u=M.val j
          · subst u; simp_all [M.inv]; aesop
          · simp_all

/-- Every first-disagreement rewiring is one of the three literal source switches. -/
theorem rewire_isSwitch (M : PM n) (i j : Fin n) (hia : i < M.val i)
    (hab : M.val i < M.val j) (hij : i < j) (hja : j ≠ M.val i) :
    IsSwitchOf (rewire M i j) M := by
  have hbi : M.val j ≠ i := ne_of_gt (lt_trans hia hab)
  obtain ⟨hrem,hadd⟩ := rewire_differences M i j (ne_of_lt hij) hja.symm hbi
  have hjb := M.free j
  rcases lt_or_gt_of_ne hja with hja | haj
  · refine ⟨i,j,M.val i,M.val j,hij,hja,hab,Or.inr (Or.inl ?_)⟩
    exact ⟨hrem,by simpa [Finset.pair_comm] using hadd⟩
  · rcases lt_or_gt_of_ne hjb.symm with hjb | hbj
    · refine ⟨i,M.val i,j,M.val j,hia,haj,hjb,Or.inr (Or.inr ?_)⟩
      exact ⟨hrem,by simpa [Sym2.eq_swap,Finset.pair_comm] using hadd⟩
    · refine ⟨i,M.val i,M.val j,j,hia,hab,hbj,Or.inl ?_⟩
      exact ⟨by simpa [Sym2.eq_swap] using hrem,
        by simpa [Sym2.eq_swap] using hadd⟩

#print axioms rewire_isSwitch
end Matching370688
```

### `MatchingRankSum.lean`

```lean
import MatchingRanks
import Mathlib.Tactic.Ring

namespace Matching370688
open Finset
variable {n : ℕ}

/-- Integer indicator; ranks themselves retain their original natural definition. -/
def bit (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

lemma bit_and (p q : Prop) [Decidable p] [Decidable q] : bit (p ∧ q) = bit p * bit q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bit,hp,hq]

lemma bit_interval (a b h : ℕ) (hab : a < b) :
    bit (a < h) - bit (b < h) = bit (a < h ∧ h ≤ b) := by
  unfold bit
  split_ifs <;> omega

lemma rank_integer_sum (M : PM n) (h k : ℕ) :
    (rank M h k : ℤ) = ∑ v : Fin n, bit (v.val < h) * bit ((M.val v).val < k) := by
  simp only [rank,card_eq_sum_ones,sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,bit]
  apply sum_congr rfl
  intro v hv
  split_ifs <;> omega

end Matching370688
```

### `MatchingRankRectangle.lean`

```lean
import MatchingRewire
import MatchingRankSum

namespace Matching370688
open Finset
variable {n : ℕ}

/-- The exact two-rectangle change under a rewiring, with strict-prefix endpoints. -/
theorem rewire_rank_identity (M : PM n) (i j : Fin n) (hia : i < M.val i)
    (hab : M.val i < M.val j) (hij : i < j) (hja : j ≠ M.val i) (h k : ℕ) :
    (rank M h k : ℤ) - (rank (rewire M i j) h k : ℤ) =
      bit (i.val < h ∧ h ≤ j.val ∧ (M.val i).val < k ∧ k ≤ (M.val j).val) +
      bit ((M.val i).val < h ∧ h ≤ (M.val j).val ∧ i.val < k ∧ k ≤ j.val) := by
  have hbi : M.val j ≠ i := ne_of_gt (lt_trans hia hab)
  have hiaNe := ne_of_lt hia
  have hijNe := ne_of_lt hij
  have habNe := ne_of_lt hab
  have hjb := M.free j
  have hai := M.free i
  let a := M.val i
  let b := M.val j
  let A := bit (i.val<h)*(bit (a.val<k)-bit (b.val<k))
  let B := bit (j.val<h)*(bit (b.val<k)-bit (a.val<k))
  let C := bit (a.val<h)*(bit (i.val<k)-bit (j.val<k))
  let D := bit (b.val<h)*(bit (j.val<k)-bit (i.val<k))
  have hrow (v : Fin n) :
      bit (v.val<h)*bit ((M.val v).val<k) - bit (v.val<h)*bit (((rewire M i j).val v).val<k) =
      (if v=i then A else 0) + (if v=j then B else 0) +
      (if v=a then C else 0) + (if v=b then D else 0) := by
    rw [rewire_apply M i j hijNe hja.symm hbi]
    by_cases hvi : v=i
    · subst v
      simp [hijNe,hiaNe,hbi.symm,A,a,b]
      ring
    · by_cases hvj : v=j
      · subst v
        simp [hijNe.symm,hja,hjb.symm,B,a,b]
        ring
      · by_cases hva : v=a
        · subst v
          simp [a,b,hai,hja.symm,habNe,M.inv,C]
          ring
        · by_cases hvb : v=b
          · subst v
            simp [a,b,hbi,hjb,habNe.symm,M.inv,D]
            ring
          · simp only [a,b] at hva hvb
            simp [a,b,hvi,hvj,hva,hvb]
  have hsum : (rank M h k : ℤ) - (rank (rewire M i j) h k : ℤ) = A+B+C+D := by
    rw [rank_integer_sum,rank_integer_sum,← sum_sub_distrib]
    simp_rw [hrow]
    simp only [sum_add_distrib]
    simp
  rw [hsum]
  have he : A+B+C+D =
      (bit (i.val<h)-bit (j.val<h))*(bit ((M.val i).val<k)-bit ((M.val j).val<k)) +
      (bit ((M.val i).val<h)-bit ((M.val j).val<h))*(bit (i.val<k)-bit (j.val<k)) := by
    dsimp [A,B,C,D,a,b]
    ring
  rw [he,bit_interval i.val j.val h hij,bit_interval (M.val i).val (M.val j).val k hab,
    bit_interval (M.val i).val (M.val j).val h hab,bit_interval i.val j.val k hij]
  simp only [bit_and,mul_assoc]

#print axioms rewire_rank_identity
end Matching370688
```

### `MatchingRectangleGap.lean`

```lean
import MatchingRankRectangle

namespace Matching370688
open Finset
variable {n : ℕ}

/-- A one-unit rank gap on the first rectangle, proved by comparing columns
with the partner of the first disagreeing row. -/
theorem first_rectangle_gap (M N : PM n) (hrank : RankLE M N) (i j : Fin n)
    (hbefore : ∀ u, u < i → M.val u = N.val u)
    (hab : M.val i < M.val j) (hbc : M.val j ≤ N.val i)
    (_hij : i < j)
    (hminimal : ∀ u, i < u → u < j → ¬ (M.val i < M.val u ∧ M.val u ≤ N.val i))
    (h k : ℕ) (hrect : i.val < h ∧ h ≤ j.val ∧ (M.val i).val < k ∧ k ≤ (M.val j).val) :
    1 ≤ (rank M h k : ℤ) - (rank N h k : ℤ) := by
  let c := (N.val i).val+1
  let T := fun u : Fin n =>
    bit (u.val<h) * (bit ((M.val u).val<k) - bit ((N.val u).val<k) -
      bit ((M.val u).val<c) + bit ((N.val u).val<c))
  have hkc : k ≤ (N.val i).val := le_trans hrect.2.2.2 hbc
  have hpoint (u : Fin n) : 0 ≤ T u := by
    by_cases huh : u.val < h
    · by_cases hui : u < i
      · dsimp [T]
        rw [hbefore u hui]
        ring_nf
        exact le_rfl
      · by_cases heq : u=i
        · subst u
          dsimp [T,c,bit]
          split_ifs <;> omega
        · have hiu : i < u := lt_of_le_of_ne (le_of_not_gt hui) (Ne.symm heq)
          have huj : u < j := by change u.val < j.val; omega
          have hmin := hminimal u hiu huj
          have hmin' : ¬ ((M.val i).val < (M.val u).val ∧ (M.val u).val ≤ (N.val i).val) := hmin
          dsimp [T,c,bit]
          split_ifs <;> omega
    · dsimp [T]
      simp [bit,huh]
  have hi : T i = 1 := by
    dsimp [T,c,bit]
    split_ifs <;> omega
  have hsum : 1 ≤ ∑ u : Fin n, T u := by
    have hh := single_le_sum (fun u _ => hpoint u) (mem_univ i)
    rw [hi] at hh
    exact hh
  have hid : (∑ u : Fin n, T u) =
      ((rank M h k : ℤ) - (rank N h k : ℤ)) -
      ((rank M h c : ℤ) - (rank N h c : ℤ)) := by
    simp_rw [rank_integer_sum]
    simp only [← sum_sub_distrib]
    apply sum_congr rfl
    intro u hu
    dsimp [T]
    ring
  rw [hid] at hsum
  have hc := hrank h (by have := j.isLt; omega) c (by dsimp [c]; have := (N.val i).isLt; omega)
  omega

end Matching370688
```

### `MatchingOverlapGap.lean`

```lean
import MatchingRectangleGap

namespace Matching370688
open Finset
open MatchingProofLane
variable {n : ℕ}

/-- The concrete two-unit overlap bound, including absence of internal matching
edges on the intervening block. -/
theorem overlapping_rectangles_gap (M N : PM n) (hrank : RankLE M N) (i j : Fin n)
    (hbefore : ∀ u, u < i → M.val u = N.val u)
    (hia : i < M.val i) (hab : M.val i < M.val j) (hbc : M.val j ≤ N.val i)
    (hij : i < j)
    (hminimal : ∀ u, i < u → u < j → ¬ (M.val i < M.val u ∧ M.val u ≤ N.val i))
    (h k : ℕ)
    (hh : (M.val i).val < h ∧ h ≤ j.val ∧ h ≤ (M.val j).val)
    (hk : (M.val i).val < k ∧ k ≤ j.val ∧ k ≤ (M.val j).val) :
    2 ≤ (rank M h k : ℤ) - (rank N h k : ℤ) := by
  classical
  have hdiag (s : ℕ) (hs : (M.val i).val < s ∧ s ≤ j.val ∧ s ≤ (M.val j).val) :
      2 ≤ (rank M s s : ℤ) - (rank N s s : ℤ) := by
    have hpos := first_rectangle_gap M N hrank i j hbefore hab hbc hij hminimal s s
      (by have hia' : i.val < (M.val i).val := hia; omega)
    have hp := positive_diagonal_gap_ge_two M.val N.val M.property.1 N.property.1
      M.property.2 N.property.2 (prefixSet n s)
    rw [← rank_as_rectSum,← rank_as_rectSum] at hp
    exact hp hpos
  have hordered : ∀ h k : ℕ,
      (M.val i).val < h ∧ h ≤ j.val ∧ h ≤ (M.val j).val →
      (M.val i).val < k ∧ k ≤ j.val ∧ k ≤ (M.val j).val → h ≤ k →
      2 ≤ (rank M h k : ℤ) - (rank N h k : ℤ) := by
    intro h k hh hk hhk
    let S := prefixSet n h
    let W := prefixSet n k \ S
    have hsub : S ⊆ prefixSet n k := by
      intro u hu
      have := (mem_filter.mp hu).2
      simp only [prefixSet,mem_filter,mem_univ,true_and]
      omega
    have hu : S ∪ W = prefixSet n k := union_sdiff_of_subset hsub
    have hd : Disjoint S W := disjoint_sdiff_self_right
    have hzero : ∀ u ∈ W, ∀ v ∈ W, partnerMatrix M.val u v = 0 := by
      intro u hu v hv
      obtain ⟨huk,hunh⟩ := mem_sdiff.mp hu
      obtain ⟨hvk,hvnh⟩ := mem_sdiff.mp hv
      have huk' := (mem_filter.mp huk).2
      have hvk' := (mem_filter.mp hvk).2
      have huh : h ≤ u.val := by simpa [S,prefixSet,not_lt] using hunh
      have hvh : h ≤ v.val := by simpa [S,prefixSet,not_lt] using hvnh
      have hiu : i < u := by change i.val < u.val; have hia' : i.val < (M.val i).val := hia; omega
      have huj : u < j := by change u.val < j.val; omega
      have hmin := hminimal u hiu huj
      have hne : M.val u ≠ v := by
        intro heq
        apply hmin
        rw [heq]
        constructor
        · change (M.val i).val < v.val; omega
        · change v.val ≤ (N.val i).val
          have hbc' : (M.val j).val ≤ (N.val i).val := hbc
          omega
      simp only [partnerMatrix,ite_eq_right hne]
    have hS := hdiag h hh
    have hT := hdiag k hk
    rw [rank_as_rectSum,rank_as_rectSum] at hS hT
    have ho := overlap_rank_gap_ge_two (partnerMatrix M.val) (partnerMatrix N.val)
      (partnerMatrix_symm M.val M.property.1) (partnerMatrix_symm N.val N.property.1)
      S W hd hzero (fun u _ v _ => partnerMatrix_nonneg N.val u v)
    have hs : 2 ≤ rectSum (fun u v => partnerMatrix M.val u v-partnerMatrix N.val u v) S S := by
      rw [rectSum_sub]; exact hS
    have ht : 2 ≤ rectSum (fun u v => partnerMatrix M.val u v-partnerMatrix N.val u v) (S ∪ W) (S ∪ W) := by
      rw [hu,rectSum_sub]; exact hT
    have hg := ho hs ht
    rw [hu,rectSum_sub] at hg
    change 2 ≤ rectSum (partnerMatrix M.val) (prefixSet n h) (prefixSet n k) -
      rectSum (partnerMatrix N.val) (prefixSet n h) (prefixSet n k) at hg
    simpa only [← rank_as_rectSum] using hg
  by_cases hhk : h ≤ k
  · exact hordered h k hh hk hhk
  · rw [rank_symm M h k,rank_symm N h k]
    exact hordered k h hk hh (by omega)

#print axioms overlapping_rectangles_gap
end Matching370688
```

### `MatchingRankStep.lean`

```lean
import MatchingFirstDisagreement
import MatchingOverlapGap

namespace Matching370688
open Finset
variable {n : ℕ}

/-- The direct first-disagreement step, with natural rank potential decreasing.
Strictness uses one changed rank cell rather than summing rectangle areas. -/
theorem first_disagreement_rank_step (M N : PM n) (hrank : RankLE M N) (hne : M ≠ N) :
    ∃ P, IsSwitchOf P M ∧ RankLE P N ∧ potential P N < potential M N := by
  classical
  obtain ⟨i,j,hbefore,hne_i,hia,hab,hbc,hij,hja,hminimal⟩ := first_disagreement_choice M N hrank hne
  let P := rewire M i j
  have hia' : i.val < (M.val i).val := hia
  have hab' : (M.val i).val < (M.val j).val := hab
  have hij' : i.val < j.val := hij
  have hbc' : (M.val j).val ≤ (N.val i).val := hbc
  have hidentity (h k : ℕ) := rewire_rank_identity M i j hia hab hij hja h k
  have hupper (h k : ℕ) : rank P h k ≤ rank M h k := by
    have hh := hidentity h k
    change (rank M h k : ℤ)-(rank P h k : ℤ) = _ at hh
    unfold bit at hh
    split_ifs at hh <;> omega
  have hlower : RankLE P N := by
    intro h hn k kn
    have hh := hidentity h k
    change (rank M h k : ℤ)-(rank P h k : ℤ) = _ at hh
    have hbase := hrank h hn k kn
    by_cases hR : i.val < h ∧ h ≤ j.val ∧ (M.val i).val < k ∧ k ≤ (M.val j).val
    · by_cases hT : (M.val i).val < h ∧ h ≤ (M.val j).val ∧ i.val < k ∧ k ≤ j.val
      · have hg := overlapping_rectangles_gap M N hrank i j hbefore hia hab hbc hij hminimal h k
          (by omega) (by omega)
        simp [bit,hR,hT] at hh
        omega
      · have hg := first_rectangle_gap M N hrank i j hbefore hab hbc hij hminimal h k hR
        simp [bit,hR,hT] at hh
        omega
    · by_cases hT : (M.val i).val < h ∧ h ≤ (M.val j).val ∧ i.val < k ∧ k ≤ j.val
      · have hg := first_rectangle_gap M N hrank i j hbefore hab hbc hij hminimal k h (by omega)
        rw [rank_symm M k h,rank_symm N k h] at hg
        simp [bit,hR,hT] at hh
        omega
      · simp [bit,hR,hT] at hh
        omega
  have hstrict : rank P (i.val+1) ((M.val i).val+1) < rank M (i.val+1) ((M.val i).val+1) := by
    have hh := hidentity (i.val+1) ((M.val i).val+1)
    change (rank M (i.val+1) ((M.val i).val+1) : ℤ) -
      (rank P (i.val+1) ((M.val i).val+1) : ℤ) = _ at hh
    have hR : i.val < i.val+1 ∧ i.val+1 ≤ j.val ∧
        (M.val i).val < (M.val i).val+1 ∧ (M.val i).val+1 ≤ (M.val j).val := by omega
    have hT : ¬ ((M.val i).val < i.val+1 ∧ i.val+1 ≤ (M.val j).val ∧
        i.val < (M.val i).val+1 ∧ (M.val i).val+1 ≤ j.val) := by omega
    simp [bit,hR] at hh
    omega
  refine ⟨P,rewire_isSwitch M i j hia hab hij hja,hlower,?_⟩
  unfold potential
  apply sum_lt_sum
  · intro h hh
    apply sum_le_sum
    intro k hk
    exact Nat.sub_le_sub_right (hupper h k) _
  · refine ⟨i.val+1,mem_range.mpr (by omega),?_⟩
    apply sum_lt_sum
    · intro k hk
      exact Nat.sub_le_sub_right (hupper _ k) _
    · refine ⟨(M.val i).val+1,mem_range.mpr (by have := (M.val i).isLt; omega),?_⟩
      have hh := hlower (i.val+1) (by omega) ((M.val i).val+1) (by have := (M.val i).isLt; omega)
      omega

#print axioms first_disagreement_rank_step
end Matching370688
```

### `MatchingNeighborExchange.lean`

```lean
import MatchingDefinitions

namespace Matching370688
open Finset
variable {n : ℕ}

/-- The auxiliary neighbor used in source Lemma 10(b), excluding the possible
edge between the two compared vertices before comparing their degrees. -/
theorem auxiliary_neighbor (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x y z : Fin n) (hxz_ne : x ≠ z) (hxz : ¬ G.Adj x z) (hyz : G.Adj y z)
    (hdeg : G.degree y ≤ G.degree x) :
    ∃ q, q ≠ x ∧ q ≠ y ∧ q ≠ z ∧ G.Adj x q ∧ ¬ G.Adj y q := by
  classical
  let X := (G.neighborFinset x).erase y
  let Y := (G.neighborFinset y).erase x
  have hcard : Y.card ≤ X.card := by
    by_cases hAdj : G.Adj x y
    · have hAdj' := hAdj.symm
      have hx : y ∈ G.neighborFinset x := by simpa using hAdj
      have hy : x ∈ G.neighborFinset y := by simpa using hAdj'
      dsimp [X,Y]
      rw [card_erase_of_mem hx,card_erase_of_mem hy,G.card_neighborFinset_eq_degree,
        G.card_neighborFinset_eq_degree]
      omega
    · have hAdj' : ¬ G.Adj y x := by simpa only [G.adj_comm] using hAdj
      have hx : y ∉ G.neighborFinset x := by simpa using hAdj
      have hy : x ∉ G.neighborFinset y := by simpa using hAdj'
      simpa [X,Y,erase_eq_of_notMem hx,erase_eq_of_notMem hy] using hdeg
  have hzY : z ∈ Y := by
    have hzx : z ≠ x := hxz_ne.symm
    exact mem_erase.mpr ⟨hzx,by simpa using hyz⟩
  have hzX : z ∉ X := by
    intro hz
    exact hxz (by simpa using (mem_erase.mp hz).2)
  have hnot : ¬ X ⊆ Y := by
    intro hsub
    have hproper : X ⊂ Y := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by intro heq; exact hzX (heq ▸ hzY)⟩
    have hh := card_lt_card hproper
    omega
  obtain ⟨q,hqX,hqY⟩ := not_subset.mp hnot
  obtain ⟨hqy,hqadj⟩ := mem_erase.mp hqX
  have hxq : G.Adj x q := by simpa using hqadj
  have hqx : q ≠ x := (G.ne_of_adj hxq).symm
  have hnyq : ¬ G.Adj y q := by
    intro ha
    exact hqY (mem_erase.mpr ⟨hqx,by simpa using ha⟩)
  have hqz : q ≠ z := by intro heq; subst q; exact hxz hxq
  exact ⟨q,hqx,hqy,hqz,hxq,hnyq⟩

#print axioms auxiliary_neighbor
end Matching370688
```

### `MatchingGraphExchange.lean`

```lean
import MatchingNeighborExchange
import Mathlib.Logic.Equiv.Basic

namespace Matching370688
open Finset
variable {n : ℕ}

/-- Delete ab,cd and insert ac,bd. The inequality guards simplicity even
without assumptions on the four arguments. -/
def graphExchange (G : SimpleGraph (Fin n)) (a b c d : Fin n) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((G.Adj u v ∧ s(u,v) ≠ s(a,b) ∧ s(u,v) ≠ s(c,d)) ∨
    s(u,v) = s(a,c) ∨ s(u,v) = s(b,d))
  symm := ⟨by
    intro u v h
    simpa only [Sym2.eq_swap,ne_comm,G.adj_comm] using h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b c d : Fin n) :
    DecidableRel (graphExchange G a b c d).Adj := by
  unfold graphExchange
  infer_instance

lemma degree_eq_of_neighbor_swap (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (v a b : Fin n)
    (h : ∀ u, H.Adj v u ↔ G.Adj v (Equiv.swap a b u)) : H.degree v = G.degree v := by
  rw [← H.card_neighborFinset_eq_degree,← G.card_neighborFinset_eq_degree]
  apply card_bij (fun u _ => Equiv.swap a b u)
  · intro u hu
    simpa only [SimpleGraph.mem_neighborFinset] using (h u).mp (by simpa using hu)
  · intro u hu w hw heq
    exact (Equiv.swap a b).injective heq
  · intro w hw
    refine ⟨Equiv.swap a b w,?_,Equiv.swap_apply_self a b w⟩
    rw [SimpleGraph.mem_neighborFinset,h,Equiv.swap_apply_self]
    simpa using hw

/-- A genuine alternating four-cycle preserves every labelled degree. -/
theorem graphExchange_degree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habG : G.Adj a b) (hcdG : G.Adj c d)
    (hacG : ¬ G.Adj a c) (hbdG : ¬ G.Adj b d) (v : Fin n) :
    (graphExchange G a b c d).degree v = G.degree v := by
  have hrel (v u : Fin n) :
      (graphExchange G a b c d).Adj v u ↔
      G.Adj v ((if v=a then Equiv.swap b c else if v=b then Equiv.swap a d else
        if v=c then Equiv.swap d a else if v=d then Equiv.swap c b else Equiv.refl _) u) := by
    by_cases hva : v=a <;> by_cases hvb : v=b <;> by_cases hvc : v=c <;> by_cases hvd : v=d <;>
      by_cases hua : u=a <;> by_cases hub : u=b <;> by_cases huc : u=c <;> by_cases hud : u=d <;>
      simp_all [graphExchange,Equiv.swap_apply_def,G.adj_comm] <;>
      aesop (add safe G.ne_of_adj)
  by_cases hva : v=a
  · apply degree_eq_of_neighbor_swap G _ v b c
    intro u; simpa only [ite_eq_left hva] using hrel v u
  · by_cases hvb : v=b
    · apply degree_eq_of_neighbor_swap G _ v a d
      intro u; simpa only [ite_eq_right hva,ite_eq_left hvb] using hrel v u
    · by_cases hvc : v=c
      · apply degree_eq_of_neighbor_swap G _ v d a
        intro u; simpa only [ite_eq_right hva,ite_eq_right hvb,ite_eq_left hvc] using hrel v u
      · by_cases hvd : v=d
        · apply degree_eq_of_neighbor_swap G _ v c b
          intro u; simpa only [ite_eq_right hva,ite_eq_right hvb,ite_eq_right hvc,ite_eq_left hvd] using hrel v u
        · apply degree_eq_of_neighbor_swap G _ v v v
          intro u; simpa [hva,hvb,hvc,hvd] using hrel v u

#print axioms graphExchange_degree
end Matching370688
```

### `MatchingExchangeEdges.lean`

```lean
import MatchingGraphExchange

namespace Matching370688
variable {n : ℕ}

lemma graphExchange_mem (G : SimpleGraph (Fin n)) (a b c d : Fin n)
    (e : Sym2 (Fin n)) (he : ¬ e.IsDiag) :
    e ∈ (graphExchange G a b c d).edgeSet ↔
      (e ∈ G.edgeSet ∧ e ≠ s(a,b) ∧ e ≠ s(c,d)) ∨ e = s(a,c) ∨ e = s(b,d) := by
  induction e using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := by simpa only [Sym2.mk_isDiag_iff] using he
    change (graphExchange G a b c d).Adj u v ↔
      ((G.Adj u v ∧ s(u,v) ≠ s(a,b) ∧ s(u,v) ≠ s(c,d)) ∨
        s(u,v) = s(a,c) ∨ s(u,v) = s(b,d))
    exact and_iff_right huv

lemma graphExchange_retains (G : SimpleGraph (Fin n)) (N : PM n) (a b c d : Fin n)
    (hab : s(a,b) ∉ N.E) (hcd : s(c,d) ∉ N.E) :
    ∀ e ∈ G.edgeSet, e ∈ N.E → e ∈ (graphExchange G a b c d).edgeSet := by
  intro e heG heN
  apply (graphExchange_mem G a b c d e (N.not_diag e heN)).mpr
  exact Or.inl ⟨heG,by intro heq; exact hab (heq ▸ heN),by intro heq; exact hcd (heq ▸ heN)⟩

end Matching370688
```

### `MatchingSwitchRealizes.lean`

```lean
import MatchingExchangeEdges

namespace Matching370688
open Finset
variable {n : ℕ}

/-- The graph alternation argument uniformly for two disjoint matching edges.
Only the two relevant degree comparisons are used. -/
theorem ordered_exchange_realizes (M N : PM n) (i a j b : Fin n)
    (hia : i ≠ a) (hij : i ≠ j) (hib : i ≠ b)
    (haj : a ≠ j) (hab : a ≠ b) (hjb : j ≠ b)
    (hrem : M.E \ N.E = {s(i,a),s(j,b)})
    (hadd : N.E \ M.E = {s(i,b),s(j,a)})
    (d : Fin n → ℕ) (hdi : d j ≤ d i) (hda : d b ≤ d a) (hreal : Realizes d M) :
    Realizes d N := by
  classical
  obtain ⟨G,inst,hd,hM⟩ := hreal
  let := inst
  have hOld1 : s(i,a) ∈ M.E ∧ s(i,a) ∉ N.E := by
    apply mem_sdiff.mp
    rw [hrem]; simp
  have hOld2 : s(j,b) ∈ M.E ∧ s(j,b) ∉ N.E := by
    apply mem_sdiff.mp
    rw [hrem]; simp
  have hNew1 : s(i,b) ∈ N.E := by
    have hh : s(i,b) ∈ N.E \ M.E := by rw [hadd]; simp
    exact (mem_sdiff.mp hh).1
  have hNew2 : s(j,a) ∈ N.E := by
    have hh : s(j,a) ∈ N.E \ M.E := by rw [hadd]; simp
    exact (mem_sdiff.mp hh).1
  have hiA : G.Adj i a := hM _ hOld1.1
  have hjB : G.Adj j b := hM _ hOld2.1
  have build (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
      (hdegree : ∀ v, H.degree v = G.degree v)
      (hret : ∀ e ∈ G.edgeSet, e ∈ N.E → e ∈ H.edgeSet)
      (hIb : H.Adj i b) (hJa : H.Adj j a) : Realizes d N := by
    refine ⟨H,inferInstance,fun v => (hdegree v).trans (hd v),?_⟩
    intro e he
    by_cases hem : e ∈ M.E
    · exact hret e (hM e hem) he
    · have hh : e ∈ N.E \ M.E := mem_sdiff.mpr ⟨he,hem⟩
      rw [hadd] at hh
      rcases mem_insert.mp hh with rfl | hh
      · exact hIb
      · have heq := mem_singleton.mp hh
        subst e
        exact hJa
  by_cases hIb : G.Adj i b
  · by_cases hJa : G.Adj j a
    · exact build G (fun _ => rfl) (fun _ he _ => he) hIb hJa
    · have haJ : ¬ G.Adj a j := by simpa only [G.adj_comm] using hJa
      obtain ⟨q,hqa,hqb,hqj,haq,hnbq⟩ := auxiliary_neighbor G a b j haj haJ hjB.symm
        (by rw [hd,hd]; exact hda)
      have haqn : s(a,q) ∉ N.E := by
        intro he
        have hNa : N.val a = j := (N.mem_E_iff a j).mp (by simpa only [Sym2.eq_swap] using hNew2)
        have hNaq := (N.mem_E_iff a q).mp he
        exact hqj (hNaq.symm.trans hNa)
      have hbjN : s(b,j) ∉ N.E := by simpa only [Sym2.eq_swap] using hOld2.2
      let H := graphExchange G a q j b
      have hret := graphExchange_retains G N a q j b haqn hOld2.2
      have hdegree (v : Fin n) : H.degree v = G.degree v :=
        graphExchange_degree G a q j b hqa.symm haj hab hqj hqb hjb haq hjB haJ
          (by simpa only [G.adj_comm] using hnbq) v
      apply build H hdegree hret (hret _ hIb hNew1)
      change (graphExchange G a q j b).Adj j a
      exact ⟨haj.symm,Or.inr (Or.inl (Sym2.eq_swap))⟩
  · by_cases hJa : G.Adj j a
    · obtain ⟨q,hqi,hqj,hqb,hiq,hnjq⟩ := auxiliary_neighbor G i j b hib hIb hjB
        (by rw [hd,hd]; exact hdi)
      have hiqn : s(i,q) ∉ N.E := by
        intro he
        have hNi : N.val i = b := (N.mem_E_iff i b).mp hNew1
        have hNiq := (N.mem_E_iff i q).mp he
        exact hqb (hNiq.symm.trans hNi)
      let H := graphExchange G i q b j
      have hbjN : s(b,j) ∉ N.E := by simpa only [Sym2.eq_swap] using hOld2.2
      have hret := graphExchange_retains G N i q b j hiqn hbjN
      have hdegree (v : Fin n) : H.degree v = G.degree v :=
        graphExchange_degree G i q b j hqi.symm hib hij hqb hqj hjb.symm hiq hjB.symm hIb
          (by simpa only [G.adj_comm] using hnjq) v
      apply build H hdegree hret ?_ (hret _ hJa hNew2)
      exact ⟨hib,Or.inr (Or.inl rfl)⟩
    · let H := graphExchange G i a b j
      have hbjN : s(b,j) ∉ N.E := by simpa only [Sym2.eq_swap] using hOld2.2
      have hret := graphExchange_retains G N i a b j hOld1.2 hbjN
      have hdegree (v : Fin n) : H.degree v = G.degree v :=
        graphExchange_degree G i a b j hia hib hij hab haj hjb.symm hiA hjB.symm hIb
          (by simpa only [G.adj_comm] using hJa) v
      apply build H hdegree hret
      · exact ⟨hib,Or.inr (Or.inl rfl)⟩
      · exact ⟨haj.symm,Or.inr (Or.inr Sym2.eq_swap)⟩

#print axioms ordered_exchange_realizes
end Matching370688
```

### `MatchingSwitchMonotone.lean`

```lean
import MatchingSwitchRealizes

namespace Matching370688
variable {n : ℕ}

/-- Source Lemma 10(b), for all three literal switch types. -/
theorem lemma_10b (M N : PM n) (h : IsSwitchOf N M) : Prec N M := by
  obtain ⟨w,x,y,z,hwx,hxy,hyz,hcases⟩ := h
  have hwy := lt_trans hwx hxy
  have hxz := lt_trans hxy hyz
  have hwz := lt_trans hwy hyz
  intro d hd hr
  rcases hcases with ⟨hrem,hadd⟩ | ⟨hrem,hadd⟩ | ⟨hrem,hadd⟩
  · apply ordered_exchange_realizes M N w x z y (ne_of_lt hwx) (ne_of_lt hwz)
      (ne_of_lt hwy) (ne_of_lt hxz) (ne_of_lt hxy) (ne_of_gt hyz)
    · simpa only [Sym2.eq_swap] using hrem
    · simpa only [Sym2.eq_swap] using hadd
    · exact hd hwz.le
    · exact hd hxy.le
    · exact hr
  · exact ordered_exchange_realizes M N w y x z (ne_of_lt hwy) (ne_of_lt hwx)
      (ne_of_lt hwz) (ne_of_gt hxy) (ne_of_lt hyz) (ne_of_lt hxz)
      hrem hadd d (hd hwx.le) (hd hyz.le) hr
  · apply ordered_exchange_realizes M N w x y z (ne_of_lt hwx) (ne_of_lt hwy)
      (ne_of_lt hwz) (ne_of_lt hxy) (ne_of_lt hxz) (ne_of_lt hyz) hrem
    · simpa only [Sym2.eq_swap] using hadd
    · exact hd hwy.le
    · exact hd hxz.le
    · exact hr

#print axioms lemma_10b
end Matching370688
```

### `MatchingStage2Assembly.lean`

```lean
import MatchingRankConsequences
import MatchingRankStep

namespace Matching370688
variable {n : ℕ}

/-- Conditional only on source Lemma 10(b). The separator and direct rank step
are now theorems, and are no longer assumptions of the assembly. -/
theorem conjecture_11_of_lemma_10b
    (monotone : ∀ A B : PM n, IsSwitchOf A B → Prec A B)
    (N M : PM n) (h : Prec N M) :
    ∃ L : List (PM n), L ≠ [] ∧ L.head? = some N ∧ L.getLast? = some M ∧
      L.Chain' (fun A B => Prec A B ∧ IsSwitchOf A B) :=
  rank_chain first_disagreement_rank_step monotone (prec_rank_unconditional h)

#print axioms conjecture_11_of_lemma_10b
end Matching370688
```

### `MatchingConjecture.lean`

```lean
import MatchingStage2Assembly
import MatchingSwitchMonotone

namespace Matching370688
variable {n : ℕ}

/-- Briggs–McDonald–Shan Conjecture 11, with literal graph realizability,
weakly decreasing degrees, the three source switches, and both chain conjuncts. -/
theorem conjecture_11 (N M : PM n) (h : Prec N M) :
    ∃ L : List (PM n), L ≠ [] ∧ L.head? = some N ∧ L.getLast? = some M ∧
      L.Chain' (fun A B => Prec A B ∧ IsSwitchOf A B) :=
  conjecture_11_of_lemma_10b (fun A B hs => lemma_10b B A hs) N M h

/-- Six-label specialization of the general proof, not an independent table computation. -/
theorem conjecture_11_six (N M : PM 6) (h : Prec N M) :
    ∃ L : List (PM 6), L ≠ [] ∧ L.head? = some N ∧ L.getLast? = some M ∧
      L.Chain' (fun A B => Prec A B ∧ IsSwitchOf A B) := conjecture_11 N M h

#print conjecture_11
#print axioms conjecture_11
#print axioms conjecture_11_six
end Matching370688
```

### `MatchingStage2Audit.lean`

```lean
import MatchingAudit
import MatchingStage2Assembly
import MatchingConjecture

namespace Matching370688
#eval Lean.versionString
#print matching_cut
#print separating_graph
#print prec_rank_unconditional
#print prec_antisymm
#print first_disagreement_rank_step
#print auxiliary_neighbor
#print conjecture_11_of_lemma_10b
#print lemma_10b
#print conjecture_11
#print axioms matching_cut
#print axioms large_block_separator
#print axioms small_block_separator
#print axioms separating_graph
#print axioms prec_rank_unconditional
#print axioms prec_antisymm
#print axioms first_disagreement_rank_step
#print axioms auxiliary_neighbor
#print axioms conjecture_11_of_lemma_10b
#print axioms lemma_10b
#print axioms conjecture_11
end Matching370688
```

### `MatchingLiteralEndpoint.lean`

```lean
import MatchingConjecture
import MatchingRepresentation

namespace Matching370688
namespace EdgePM
variable {n : ℕ}

/-- Literal simple-graph realization for the review's finite-edge matching. -/
def Realizes (d : Fin n → ℕ) (M : EdgePM n) : Prop :=
  ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
    (∀ v, G.degree v = d v) ∧ ∀ e ∈ M.E, e ∈ G.edgeSet

/-- Literal preorder over all weakly decreasing natural degree vectors. -/
def Prec (N M : EdgePM n) : Prop :=
  ∀ d : Fin n → ℕ, Antitone d → Realizes d M → Realizes d N

/-- Exactly the three source switches, on finite edge-set matchings. -/
def IsSwitchOf (N M : EdgePM n) : Prop :=
  ∃ w x y z : Fin n, w < x ∧ x < y ∧ y < z ∧
    ((M.E \ N.E = {s(w,x), s(y,z)} ∧ N.E \ M.E = {s(w,y), s(x,z)}) ∨
     (M.E \ N.E = {s(w,y), s(x,z)} ∧ N.E \ M.E = {s(w,z), s(x,y)}) ∨
     (M.E \ N.E = {s(w,x), s(y,z)} ∧ N.E \ M.E = {s(w,z), s(x,y)}))

lemma ext_edges {M N : EdgePM n} (h : M.E = N.E) : M = N := by
  cases M
  cases N
  cases h
  rfl

lemma toPM_toEdgePM (M : EdgePM n) : M.toPM.toEdgePM = M :=
  ext_edges M.toPM_edges

lemma realizes_toPM (d : Fin n → ℕ) (M : EdgePM n) :
    Matching370688.Realizes d M.toPM ↔ Realizes d M := by
  unfold Matching370688.Realizes Realizes
  rw [M.toPM_edges]

lemma prec_toPM (N M : EdgePM n) :
    Matching370688.Prec N.toPM M.toPM ↔ Prec N M := by
  simp only [Matching370688.Prec, Prec, realizes_toPM]

/-- The source endpoint directly on arbitrary loop-free covering edge sets.
The partner representation is eliminated from the theorem statement. -/
theorem conjecture_11 (N M : EdgePM n) (h : Prec N M) :
    ∃ L : List (EdgePM n), L ≠ [] ∧ L.head? = some N ∧ L.getLast? = some M ∧
      L.Chain' (fun A B => Prec A B ∧ IsSwitchOf A B) := by
  obtain ⟨L, hne, hhead, hlast, hchain⟩ :=
    Matching370688.conjecture_11 N.toPM M.toPM ((prec_toPM N M).mpr h)
  refine ⟨L.map PM.toEdgePM, by simpa using hne, ?_, ?_, ?_⟩
  · simp only [List.head?_map, hhead, Option.map_some, toPM_toEdgePM]
  · simp only [List.getLast?_map, hlast, Option.map_some, toPM_toEdgePM]
  · exact List.isChain_map_of_isChain PM.toEdgePM (fun A B hAB => hAB) hchain

#print conjecture_11
#print axioms conjecture_11
end EdgePM
end Matching370688
```

### `MatchingRankCharacterization.lean`

```lean
import MatchingConjecture

namespace Matching370688
variable {n : ℕ}

/-- The reverse direction uses the proved direct rank step and source Lemma 10(b). -/
theorem rank_prec {N M : PM n} (h : RankLE M N) : Prec N M := by
  classical
  generalize hm : potential M N = m
  induction m using Nat.strong_induction_on generalizing M with
  | h m ih =>
    by_cases he : M = N
    · subst M
      exact prec_refl N
    · obtain ⟨P, hs, hp, hlt⟩ := first_disagreement_rank_step M N h he
      exact prec_trans (ih (potential P N) (by omega) hp rfl) (lemma_10b M P hs)

/-- All rank tests are equivalent to the literal graph-realization preorder. -/
theorem prec_iff_rank (N M : PM n) : Prec N M ↔ RankLE M N :=
  ⟨prec_rank_unconditional, rank_prec⟩

/-- Finite test used only for the small-order sanity table. -/
def finiteRankTest (M N : PM n) : Prop :=
  ∀ i j : Fin (n+1), rank N i.val j.val ≤ rank M i.val j.val

instance (M N : PM n) : Decidable (finiteRankTest M N) := by
  unfold finiteRankTest
  infer_instance

lemma rankLE_iff_finite (M N : PM n) : RankLE M N ↔ finiteRankTest M N := by
  constructor
  · intro h i j
    exact h i.val (by omega) j.val (by omega)
  · intro h i hi j hj
    exact h ⟨i, by omega⟩ ⟨j, by omega⟩

#print axioms rank_prec
#print axioms prec_iff_rank
end Matching370688
```

### `MatchingSixEnumeration.lean`

```lean
import MatchingSixObjects

namespace Matching370688

def sixMatch : Fin 15 → PM 6 := ![m6_0,m6_1,m6_2,m6_3,m6_4,m6_5,m6_6,m6_7,m6_8,m6_9,m6_10,m6_11,m6_12,m6_13,m6_14]

lemma six_label_cases (v : Fin 6) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by
  have h : ∀ v : Fin 6, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by decide
  exact h v

theorem sixMatch_complete (M : PM 6) : ∃ i : Fin 15, M = sixMatch i := by
  rcases six_label_cases (M.val 0) with h0 | h0 | h0 | h0 | h0 | h0
  · exact (M.free 0 h0).elim
  · have h1 : M.val 1 = 0 := by simpa only [h0] using M.inv 0
    rcases six_label_cases (M.val 2) with h2 | h2 | h2 | h2 | h2 | h2
    · have hh := M.inv 2
      rw [h2, h0] at hh
      exact ((by decide : (1 : Fin 6) ≠ 2) hh).elim
    · have hh := M.inv 2
      rw [h2, h1] at hh
      exact ((by decide : (0 : Fin 6) ≠ 2) hh).elim
    · exact (M.free 2 h2).elim
    · have h3 : M.val 3 = 2 := by simpa only [h2] using M.inv 2
      rcases six_label_cases (M.val 4) with h4 | h4 | h4 | h4 | h4 | h4
      · have hh := M.inv 4
        rw [h4, h0] at hh
        exact ((by decide : (1 : Fin 6) ≠ 4) hh).elim
      · have hh := M.inv 4
        rw [h4, h1] at hh
        exact ((by decide : (0 : Fin 6) ≠ 4) hh).elim
      · have hh := M.inv 4
        rw [h4, h2] at hh
        exact ((by decide : (3 : Fin 6) ≠ 4) hh).elim
      · have hh := M.inv 4
        rw [h4, h3] at hh
        exact ((by decide : (2 : Fin 6) ≠ 4) hh).elim
      · exact (M.free 4 h4).elim
      · have h5 : M.val 5 = 4 := by simpa only [h4] using M.inv 4
        refine ⟨0, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    · have h4 : M.val 4 = 2 := by simpa only [h2] using M.inv 2
      rcases six_label_cases (M.val 3) with h3 | h3 | h3 | h3 | h3 | h3
      · have hh := M.inv 3
        rw [h3, h0] at hh
        exact ((by decide : (1 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h1] at hh
        exact ((by decide : (0 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h2] at hh
        exact ((by decide : (4 : Fin 6) ≠ 3) hh).elim
      · exact (M.free 3 h3).elim
      · have hh := M.inv 3
        rw [h3, h4] at hh
        exact ((by decide : (2 : Fin 6) ≠ 3) hh).elim
      · have h5 : M.val 5 = 3 := by simpa only [h3] using M.inv 3
        refine ⟨1, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    · have h5 : M.val 5 = 2 := by simpa only [h2] using M.inv 2
      rcases six_label_cases (M.val 3) with h3 | h3 | h3 | h3 | h3 | h3
      · have hh := M.inv 3
        rw [h3, h0] at hh
        exact ((by decide : (1 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h1] at hh
        exact ((by decide : (0 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h2] at hh
        exact ((by decide : (5 : Fin 6) ≠ 3) hh).elim
      · exact (M.free 3 h3).elim
      · have h4 : M.val 4 = 3 := by simpa only [h3] using M.inv 3
        refine ⟨2, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      · have hh := M.inv 3
        rw [h3, h5] at hh
        exact ((by decide : (2 : Fin 6) ≠ 3) hh).elim
  · have h2 : M.val 2 = 0 := by simpa only [h0] using M.inv 0
    rcases six_label_cases (M.val 1) with h1 | h1 | h1 | h1 | h1 | h1
    · have hh := M.inv 1
      rw [h1, h0] at hh
      exact ((by decide : (2 : Fin 6) ≠ 1) hh).elim
    · exact (M.free 1 h1).elim
    · have hh := M.inv 1
      rw [h1, h2] at hh
      exact ((by decide : (0 : Fin 6) ≠ 1) hh).elim
    · have h3 : M.val 3 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 4) with h4 | h4 | h4 | h4 | h4 | h4
      · have hh := M.inv 4
        rw [h4, h0] at hh
        exact ((by decide : (2 : Fin 6) ≠ 4) hh).elim
      · have hh := M.inv 4
        rw [h4, h1] at hh
        exact ((by decide : (3 : Fin 6) ≠ 4) hh).elim
      · have hh := M.inv 4
        rw [h4, h2] at hh
        exact ((by decide : (0 : Fin 6) ≠ 4) hh).elim
      · have hh := M.inv 4
        rw [h4, h3] at hh
        exact ((by decide : (1 : Fin 6) ≠ 4) hh).elim
      · exact (M.free 4 h4).elim
      · have h5 : M.val 5 = 4 := by simpa only [h4] using M.inv 4
        refine ⟨3, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    · have h4 : M.val 4 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 3) with h3 | h3 | h3 | h3 | h3 | h3
      · have hh := M.inv 3
        rw [h3, h0] at hh
        exact ((by decide : (2 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h1] at hh
        exact ((by decide : (4 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h2] at hh
        exact ((by decide : (0 : Fin 6) ≠ 3) hh).elim
      · exact (M.free 3 h3).elim
      · have hh := M.inv 3
        rw [h3, h4] at hh
        exact ((by decide : (1 : Fin 6) ≠ 3) hh).elim
      · have h5 : M.val 5 = 3 := by simpa only [h3] using M.inv 3
        refine ⟨4, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    · have h5 : M.val 5 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 3) with h3 | h3 | h3 | h3 | h3 | h3
      · have hh := M.inv 3
        rw [h3, h0] at hh
        exact ((by decide : (2 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h1] at hh
        exact ((by decide : (5 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h2] at hh
        exact ((by decide : (0 : Fin 6) ≠ 3) hh).elim
      · exact (M.free 3 h3).elim
      · have h4 : M.val 4 = 3 := by simpa only [h3] using M.inv 3
        refine ⟨5, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      · have hh := M.inv 3
        rw [h3, h5] at hh
        exact ((by decide : (1 : Fin 6) ≠ 3) hh).elim
  · have h3 : M.val 3 = 0 := by simpa only [h0] using M.inv 0
    rcases six_label_cases (M.val 1) with h1 | h1 | h1 | h1 | h1 | h1
    · have hh := M.inv 1
      rw [h1, h0] at hh
      exact ((by decide : (3 : Fin 6) ≠ 1) hh).elim
    · exact (M.free 1 h1).elim
    · have h2 : M.val 2 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 4) with h4 | h4 | h4 | h4 | h4 | h4
      · have hh := M.inv 4
        rw [h4, h0] at hh
        exact ((by decide : (3 : Fin 6) ≠ 4) hh).elim
      · have hh := M.inv 4
        rw [h4, h1] at hh
        exact ((by decide : (2 : Fin 6) ≠ 4) hh).elim
      · have hh := M.inv 4
        rw [h4, h2] at hh
        exact ((by decide : (1 : Fin 6) ≠ 4) hh).elim
      · have hh := M.inv 4
        rw [h4, h3] at hh
        exact ((by decide : (0 : Fin 6) ≠ 4) hh).elim
      · exact (M.free 4 h4).elim
      · have h5 : M.val 5 = 4 := by simpa only [h4] using M.inv 4
        refine ⟨6, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    · have hh := M.inv 1
      rw [h1, h3] at hh
      exact ((by decide : (0 : Fin 6) ≠ 1) hh).elim
    · have h4 : M.val 4 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 2) with h2 | h2 | h2 | h2 | h2 | h2
      · have hh := M.inv 2
        rw [h2, h0] at hh
        exact ((by decide : (3 : Fin 6) ≠ 2) hh).elim
      · have hh := M.inv 2
        rw [h2, h1] at hh
        exact ((by decide : (4 : Fin 6) ≠ 2) hh).elim
      · exact (M.free 2 h2).elim
      · have hh := M.inv 2
        rw [h2, h3] at hh
        exact ((by decide : (0 : Fin 6) ≠ 2) hh).elim
      · have hh := M.inv 2
        rw [h2, h4] at hh
        exact ((by decide : (1 : Fin 6) ≠ 2) hh).elim
      · have h5 : M.val 5 = 2 := by simpa only [h2] using M.inv 2
        refine ⟨7, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    · have h5 : M.val 5 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 2) with h2 | h2 | h2 | h2 | h2 | h2
      · have hh := M.inv 2
        rw [h2, h0] at hh
        exact ((by decide : (3 : Fin 6) ≠ 2) hh).elim
      · have hh := M.inv 2
        rw [h2, h1] at hh
        exact ((by decide : (5 : Fin 6) ≠ 2) hh).elim
      · exact (M.free 2 h2).elim
      · have hh := M.inv 2
        rw [h2, h3] at hh
        exact ((by decide : (0 : Fin 6) ≠ 2) hh).elim
      · have h4 : M.val 4 = 2 := by simpa only [h2] using M.inv 2
        refine ⟨8, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      · have hh := M.inv 2
        rw [h2, h5] at hh
        exact ((by decide : (1 : Fin 6) ≠ 2) hh).elim
  · have h4 : M.val 4 = 0 := by simpa only [h0] using M.inv 0
    rcases six_label_cases (M.val 1) with h1 | h1 | h1 | h1 | h1 | h1
    · have hh := M.inv 1
      rw [h1, h0] at hh
      exact ((by decide : (4 : Fin 6) ≠ 1) hh).elim
    · exact (M.free 1 h1).elim
    · have h2 : M.val 2 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 3) with h3 | h3 | h3 | h3 | h3 | h3
      · have hh := M.inv 3
        rw [h3, h0] at hh
        exact ((by decide : (4 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h1] at hh
        exact ((by decide : (2 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h2] at hh
        exact ((by decide : (1 : Fin 6) ≠ 3) hh).elim
      · exact (M.free 3 h3).elim
      · have hh := M.inv 3
        rw [h3, h4] at hh
        exact ((by decide : (0 : Fin 6) ≠ 3) hh).elim
      · have h5 : M.val 5 = 3 := by simpa only [h3] using M.inv 3
        refine ⟨9, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    · have h3 : M.val 3 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 2) with h2 | h2 | h2 | h2 | h2 | h2
      · have hh := M.inv 2
        rw [h2, h0] at hh
        exact ((by decide : (4 : Fin 6) ≠ 2) hh).elim
      · have hh := M.inv 2
        rw [h2, h1] at hh
        exact ((by decide : (3 : Fin 6) ≠ 2) hh).elim
      · exact (M.free 2 h2).elim
      · have hh := M.inv 2
        rw [h2, h3] at hh
        exact ((by decide : (1 : Fin 6) ≠ 2) hh).elim
      · have hh := M.inv 2
        rw [h2, h4] at hh
        exact ((by decide : (0 : Fin 6) ≠ 2) hh).elim
      · have h5 : M.val 5 = 2 := by simpa only [h2] using M.inv 2
        refine ⟨10, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    · have hh := M.inv 1
      rw [h1, h4] at hh
      exact ((by decide : (0 : Fin 6) ≠ 1) hh).elim
    · have h5 : M.val 5 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 2) with h2 | h2 | h2 | h2 | h2 | h2
      · have hh := M.inv 2
        rw [h2, h0] at hh
        exact ((by decide : (4 : Fin 6) ≠ 2) hh).elim
      · have hh := M.inv 2
        rw [h2, h1] at hh
        exact ((by decide : (5 : Fin 6) ≠ 2) hh).elim
      · exact (M.free 2 h2).elim
      · have h3 : M.val 3 = 2 := by simpa only [h2] using M.inv 2
        refine ⟨11, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      · have hh := M.inv 2
        rw [h2, h4] at hh
        exact ((by decide : (0 : Fin 6) ≠ 2) hh).elim
      · have hh := M.inv 2
        rw [h2, h5] at hh
        exact ((by decide : (1 : Fin 6) ≠ 2) hh).elim
  · have h5 : M.val 5 = 0 := by simpa only [h0] using M.inv 0
    rcases six_label_cases (M.val 1) with h1 | h1 | h1 | h1 | h1 | h1
    · have hh := M.inv 1
      rw [h1, h0] at hh
      exact ((by decide : (5 : Fin 6) ≠ 1) hh).elim
    · exact (M.free 1 h1).elim
    · have h2 : M.val 2 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 3) with h3 | h3 | h3 | h3 | h3 | h3
      · have hh := M.inv 3
        rw [h3, h0] at hh
        exact ((by decide : (5 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h1] at hh
        exact ((by decide : (2 : Fin 6) ≠ 3) hh).elim
      · have hh := M.inv 3
        rw [h3, h2] at hh
        exact ((by decide : (1 : Fin 6) ≠ 3) hh).elim
      · exact (M.free 3 h3).elim
      · have h4 : M.val 4 = 3 := by simpa only [h3] using M.inv 3
        refine ⟨12, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      · have hh := M.inv 3
        rw [h3, h5] at hh
        exact ((by decide : (0 : Fin 6) ≠ 3) hh).elim
    · have h3 : M.val 3 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 2) with h2 | h2 | h2 | h2 | h2 | h2
      · have hh := M.inv 2
        rw [h2, h0] at hh
        exact ((by decide : (5 : Fin 6) ≠ 2) hh).elim
      · have hh := M.inv 2
        rw [h2, h1] at hh
        exact ((by decide : (3 : Fin 6) ≠ 2) hh).elim
      · exact (M.free 2 h2).elim
      · have hh := M.inv 2
        rw [h2, h3] at hh
        exact ((by decide : (1 : Fin 6) ≠ 2) hh).elim
      · have h4 : M.val 4 = 2 := by simpa only [h2] using M.inv 2
        refine ⟨13, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      · have hh := M.inv 2
        rw [h2, h5] at hh
        exact ((by decide : (0 : Fin 6) ≠ 2) hh).elim
    · have h4 : M.val 4 = 1 := by simpa only [h1] using M.inv 1
      rcases six_label_cases (M.val 2) with h2 | h2 | h2 | h2 | h2 | h2
      · have hh := M.inv 2
        rw [h2, h0] at hh
        exact ((by decide : (5 : Fin 6) ≠ 2) hh).elim
      · have hh := M.inv 2
        rw [h2, h1] at hh
        exact ((by decide : (4 : Fin 6) ≠ 2) hh).elim
      · exact (M.free 2 h2).elim
      · have h3 : M.val 3 = 2 := by simpa only [h2] using M.inv 2
        refine ⟨14, ?_⟩
        apply Subtype.ext
        funext v
        rcases six_label_cases v with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      · have hh := M.inv 2
        rw [h2, h4] at hh
        exact ((by decide : (1 : Fin 6) ≠ 2) hh).elim
      · have hh := M.inv 2
        rw [h2, h5] at hh
        exact ((by decide : (0 : Fin 6) ≠ 2) hh).elim
    · have hh := M.inv 1
      rw [h1, h5] at hh
      exact ((by decide : (0 : Fin 6) ≠ 1) hh).elim

#print axioms sixMatch_complete
end Matching370688
```

### `MatchingSixTable.lean`

```lean
import MatchingRankCharacterization
import MatchingSixEnumeration

namespace Matching370688
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sixPreorderPairs : Finset (Fin 15 × Fin 15) :=
  {(0,0), (1,0), (1,1), (2,0), (2,1), (2,2), (3,0), (3,3), (4,0), (4,1), (4,3), (4,4), (5,0), (5,1), (5,2), (5,3), (5,4), (5,5), (6,0), (6,3), (6,6), (7,0), (7,1), (7,2), (7,3), (7,4), (7,6), (7,7), (8,0), (8,1), (8,2), (8,3), (8,4), (8,5), (8,6), (8,7), (8,8), (9,0), (9,1), (9,3), (9,4), (9,6), (9,9), (10,0), (10,1), (10,2), (10,3), (10,4), (10,6), (10,7), (10,9), (10,10), (11,0), (11,1), (11,2), (11,3), (11,4), (11,5), (11,6), (11,7), (11,8), (11,9), (11,10), (11,11), (12,0), (12,1), (12,2), (12,3), (12,4), (12,5), (12,6), (12,9), (12,12), (13,0), (13,1), (13,2), (13,3), (13,4), (13,5), (13,6), (13,7), (13,8), (13,9), (13,10), (13,12), (13,13), (14,0), (14,1), (14,2), (14,3), (14,4), (14,5), (14,6), (14,7), (14,8), (14,9), (14,10), (14,11), (14,12), (14,13), (14,14)}

theorem six_rank_table : ∀ i j : Fin 15,
    finiteRankTest (sixMatch j) (sixMatch i) ↔ (i,j) ∈ sixPreorderPairs := by decide

theorem six_pair_count : sixPreorderPairs.card = 101 := by decide

theorem six_preorder_table (i j : Fin 15) :
    Prec (sixMatch i) (sixMatch j) ↔ (i,j) ∈ sixPreorderPairs := by
  rw [prec_iff_rank, rankLE_iff_finite]
  exact six_rank_table i j

theorem six_complete_preorder_table (N M : PM 6) :
    Prec N M ↔ ∃ i j : Fin 15,
      N = sixMatch i ∧ M = sixMatch j ∧ (i,j) ∈ sixPreorderPairs := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := sixMatch_complete N
    obtain ⟨j, rfl⟩ := sixMatch_complete M
    exact ⟨i,j,rfl,rfl,(six_preorder_table i j).mp h⟩
  · rintro ⟨i,j,rfl,rfl,h⟩
    exact (six_preorder_table i j).mpr h

#print axioms six_rank_table
#print axioms six_complete_preorder_table
end Matching370688
```

