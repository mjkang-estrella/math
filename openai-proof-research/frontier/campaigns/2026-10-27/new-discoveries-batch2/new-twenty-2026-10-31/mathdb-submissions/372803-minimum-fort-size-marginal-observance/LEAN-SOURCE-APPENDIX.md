# Lean source appendix for MathDB 372803

The modules below are listed in import order.

### `FortObservance.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find

namespace FortObservance

open Finset

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The domination step of the power domination process. -/
def initial (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∪ S.biUnion (fun x => G.neighborFinset x)

theorem mem_initial (S : Finset (Fin n)) (y : Fin n) :
    y ∈ initial G S ↔ y ∈ S ∨ ∃ x ∈ S, G.Adj x y := by
  simp [initial]

/-- A legal zero force adds the sole unobserved neighbor of an observed vertex. -/
def CanForce (B : Finset (Fin n)) (x y : Fin n) : Prop :=
  x ∈ B ∧ G.neighborFinset x \ B = {y}

/-- A terminal observation set admits no legal zero force. -/
def Closed (B : Finset (Fin n)) : Prop :=
  ∀ x ∈ B, ((G.neighborFinset x) \ B).card ≠ 1

theorem closed_iff_no_force (B : Finset (Fin n)) :
    Closed G B ↔ ∀ x y, ¬ CanForce G B x y := by
  constructor
  · intro h x y ⟨hx, heq⟩
    exact h x hx (by rw [heq, card_singleton])
  · intro h x hx hc
    obtain ⟨y, hy⟩ := card_eq_one.mp hc
    exact h x y ⟨hx, hy⟩

theorem force_target (B : Finset (Fin n)) {x y : Fin n} (h : CanForce G B x y) :
    y ∈ G.neighborFinset x ∧ y ∉ B :=
  mem_sdiff.mp (h.2.symm ▸ mem_singleton_self y)

theorem force_mem_of_closed {B C : Finset (Fin n)} {x y : Fin n} (hBC : B ⊆ C)
    (hC : Closed G C) (hf : CanForce G B x y) : y ∈ C := by
  by_contra hy
  apply (closed_iff_no_force G C).mp hC x y
  refine ⟨hBC hf.1, Subset.antisymm ?_ ?_⟩
  · calc
      G.neighborFinset x \ C ⊆ G.neighborFinset x \ B := fun z hz =>
        mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1, fun hzB => (mem_sdiff.mp hz).2 (hBC hzB)⟩
      _ = {y} := hf.2
  · exact singleton_subset_iff.mpr (mem_sdiff.mpr ⟨(force_target G B hf).1, hy⟩)

/-- Intersection of all terminal supersets of the initial observations. -/
noncomputable def obsClosure (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact univ.filter fun y => ∀ B : Finset (Fin n), initial G S ⊆ B → Closed G B → y ∈ B

theorem mem_obsClosure (S : Finset (Fin n)) (y : Fin n) :
    y ∈ obsClosure G S ↔
      ∀ B : Finset (Fin n), initial G S ⊆ B → Closed G B → y ∈ B := by
  classical
  simp [obsClosure]

theorem initial_subset_obsClosure (S : Finset (Fin n)) : initial G S ⊆ obsClosure G S :=
  fun y hy => (mem_obsClosure G S y).mpr fun _ h _ => h hy

theorem obsClosure_least {S B : Finset (Fin n)} (h : initial G S ⊆ B)
    (hc : Closed G B) : obsClosure G S ⊆ B :=
  fun y hy => (mem_obsClosure G S y).mp hy B h hc

theorem obsClosure_closed (S : Finset (Fin n)) : Closed G (obsClosure G S) := by
  rw [closed_iff_no_force]
  intro x y hf
  apply (force_target G _ hf).2
  apply (mem_obsClosure G S y).mpr
  intro B hB hc
  exact force_mem_of_closed G (obsClosure_least G hB hc) hc hf

/-- A finite sequence of zero forces, starting at B and ending at C. -/
inductive Run : Finset (Fin n) → Finset (Fin n) → Prop
  | refl (B) : Run B B
  | step {B C} {x y} : CanForce G B x y → Run (insert y B) C → Run B C

theorem run_subset_closed {B C D : Finset (Fin n)} (run : Run G B C)
    (hBD : B ⊆ D) (hD : Closed G D) : C ⊆ D := by
  induction run with
  | refl => exact hBD
  | step hf _ ih =>
      exact ih (insert_subset_iff.mpr ⟨force_mem_of_closed G hBD hD hf, hBD⟩)

theorem run_grows {B C : Finset (Fin n)} (run : Run G B C) : B ⊆ C := by
  induction run with
  | refl => exact Subset.rfl
  | step _ _ ih => exact (subset_insert _ _).trans ih

theorem exists_terminal_run (B : Finset (Fin n)) :
    ∃ C, Run G B C ∧ Closed G C := by
  classical
  by_cases h : Closed G B
  · exact ⟨B, Run.refl _, h⟩
  · rw [closed_iff_no_force] at h
    push Not at h
    obtain ⟨x, y, hxy⟩ := h
    have hy := (force_target G B hxy).2
    have hcard : (insert y B).card ≤ n := by
      simpa using card_le_univ (insert y B)
    obtain ⟨C, hrun, hC⟩ := exists_terminal_run (insert y B)
    exact ⟨C, Run.step hxy hrun, hC⟩
termination_by n - B.card
decreasing_by
  rw [card_insert_of_notMem hy] at hcard ⊢
  omega

theorem terminal_run_eq_obsClosure {S B : Finset (Fin n)}
    (run : Run G (initial G S) B) (hB : Closed G B) : B = obsClosure G S :=
  Subset.antisymm
    (run_subset_closed G run (initial_subset_obsClosure G S) (obsClosure_closed G S))
    (obsClosure_least G (run_grows G run) hB)

theorem obsClosure_run (S : Finset (Fin n)) : Run G (initial G S) (obsClosure G S) := by
  obtain ⟨B, hrun, hB⟩ := exists_terminal_run G (initial G S)
  rwa [terminal_run_eq_obsClosure G hrun hB] at hrun

/-- Maximum number of observed vertices over all k-element sensor sets. -/
noncomputable def maxObs (k : ℕ) : ℕ :=
  (univ : Finset (Fin n)).powersetCard k |>.sup fun S => (obsClosure G S).card

theorem card_obsClosure_le_maxObs {k : ℕ} {S : Finset (Fin n)} (h : S.card = k) :
    (obsClosure G S).card ≤ maxObs G k :=
  le_sup (f := fun T => (obsClosure G T).card) (mem_powersetCard.mpr ⟨subset_univ _, h⟩)

theorem maxObs_le {k b : ℕ} (h : ∀ S : Finset (Fin n), S.card = k →
    (obsClosure G S).card ≤ b) : maxObs G k ≤ b :=
  Finset.sup_le fun S hS => h S (mem_powersetCard.mp hS).2

theorem maxObs_attained {k : ℕ} (hk : k ≤ n) :
    ∃ S : Finset (Fin n), S.card = k ∧ (obsClosure G S).card = maxObs G k := by
  let placements := (univ : Finset (Fin n)).powersetCard k
  have hne : placements.Nonempty := powersetCard_nonempty.mpr (by simpa using hk)
  obtain ⟨S, hS, he⟩ := exists_mem_eq_sup placements hne (fun T => (obsClosure G T).card)
  exact ⟨S, (mem_powersetCard.mp hS).2, he.symm⟩

/-- A placement power dominates when its observed set is the whole graph. -/
def IsPowerDominatingSet (S : Finset (Fin n)) : Prop :=
  obsClosure G S = univ

theorem maxObs_eq_order_iff {k : ℕ} (hk : k ≤ n) :
    maxObs G k = n ↔ ∃ S : Finset (Fin n), S.card = k ∧ IsPowerDominatingSet G S := by
  constructor
  · intro h
    obtain ⟨S, hs, hc⟩ := maxObs_attained G hk
    refine ⟨S, hs, (card_eq_iff_eq_univ _).mp ?_⟩
    simpa using hc.trans h
  · rintro ⟨S, hs, hS⟩
    apply le_antisymm (maxObs_le G fun T _ => by simpa using card_le_univ (obsClosure G T))
    change obsClosure G S = univ at hS
    simpa [hS] using card_obsClosure_le_maxObs G hs

theorem maxObs_order : maxObs G n = n := by
  refine le_antisymm (maxObs_le G fun S _ => by simpa using card_le_univ (obsClosure G S)) ?_
  have hu : initial G univ = univ := by simp [initial]
  have hobs : obsClosure G univ = univ :=
    Subset.antisymm (subset_univ _) (by simpa only [hu] using initial_subset_obsClosure G univ)
  have h := card_obsClosure_le_maxObs G (S := univ) (k := n) (by simp)
  simpa [hobs] using h

theorem maxObs_zero : maxObs G 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply maxObs_le G
  intro S h
  have hS : S = ∅ := card_eq_zero.mp h
  have hsub : obsClosure G S ⊆ ∅ := obsClosure_least G (by simp [hS, initial])
    (by simp [Closed])
  simp [Subset.antisymm hsub (empty_subset _)]

/-- The least sensor count for which maximum observance is the graph order. -/
noncomputable def γP : ℕ := by
  classical
  exact Nat.find (show ∃ k, maxObs G k = n from ⟨n, maxObs_order G⟩)

theorem maxObs_γP : maxObs G (γP G) = n := by
  classical
  exact Nat.find_spec (⟨n, maxObs_order G⟩ : ∃ k, maxObs G k = n)

theorem γP_le {k : ℕ} (h : maxObs G k = n) : γP G ≤ k := by
  classical
  exact Nat.find_min' (⟨n, maxObs_order G⟩ : ∃ k, maxObs G k = n) h

/-- Marginal observance at index i. -/
noncomputable def MObs (i : ℕ) : ℤ :=
  (maxObs G i : ℤ) - (maxObs G (i - 1) : ℤ)

/-- A fort is nonempty, with no outside vertex adjacent to exactly one member. -/
def IsFort (F : Finset (Fin n)) : Prop :=
  F.Nonempty ∧ ∀ x ∉ F, (G.neighborFinset x ∩ F).card ≠ 1

/-- Minimum fort size. The infimum is infinity for the empty graph. -/
noncomputable def minFort : WithTop ℕ := by
  classical
  exact (univ.powerset.filter (IsFort G)).inf fun F => (F.card : WithTop ℕ)

theorem le_minFort {b : ℕ} (h : ∀ F : Finset (Fin n), IsFort G F → b ≤ F.card) :
    (b : WithTop ℕ) ≤ minFort G := by
  classical
  unfold minFort
  exact Finset.le_inf fun F hF => by simpa using h F (mem_filter.mp hF).2

theorem minFort_le {F : Finset (Fin n)} (h : IsFort G F) :
    minFort G ≤ (F.card : WithTop ℕ) := by
  classical
  unfold minFort
  exact inf_le (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), h⟩)

theorem minFort_attained (hn : 0 < n) :
    ∃ F : Finset (Fin n), IsFort G F ∧ minFort G = (F.card : WithTop ℕ) := by
  classical
  let forts := (univ : Finset (Fin n)).powerset.filter (IsFort G)
  have hu : IsFort G univ := by
    refine ⟨card_pos.mp (by simpa using hn), ?_⟩
    simp
  have hne : forts.Nonempty := ⟨univ, mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hu⟩⟩
  obtain ⟨F, hF, he⟩ := exists_mem_eq_inf forts hne (fun F => (F.card : WithTop ℕ))
  exact ⟨F, (mem_filter.mp hF).2, he⟩

end FortObservance
```

### `FortWitnessGraph.lean`

```lean
import FortObservance

namespace FortObservance.Witness

open Finset

abbrev V := Fin 25

/--
Local labels 1–7 are the points, and 8–12 are the lines. Label 0 is the
shared hub. In the second copy add 12 to every nonzero local label.
-/
def localNeighbors : Fin 12 → List V
  | 0 => [8, 12]
  | 1 => [8, 9]
  | 2 => [9, 10]
  | 3 => [8, 10, 11]
  | 4 => [9, 11, 12]
  | 5 => [10, 12]
  | 6 => [11]
  | 7 => [0, 1, 2, 4]
  | 8 => [0, 2, 3, 5]
  | 9 => [0, 3, 4, 6]
  | 10 => [0, 4, 5, 7]
  | 11 => [0, 1, 5, 6]

def inCopy (v : V) (labels : List V) : List V :=
  if v.val ≤ 12 then labels else labels.map fun x => if x = 0 then 0 else x + 12

def neighbors (v : V) : List V :=
  if v = 0 then [8, 9, 10, 11, 12, 20, 21, 22, 23, 24]
  else inCopy v (localNeighbors (Fin.ofNat 12 (v.val - 1)))

def adjacency (v w : V) : Prop := w ∈ neighbors v

instance : DecidableRel adjacency := fun v w => inferInstanceAs (Decidable (w ∈ neighbors v))

private theorem adjacency_symm : ∀ v w, adjacency v w → adjacency w v := by decide
private theorem adjacency_irrefl : ∀ v, ¬ adjacency v v := by decide

def graph : SimpleGraph V where
  Adj := adjacency
  symm := ⟨adjacency_symm⟩
  loopless := ⟨adjacency_irrefl⟩

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel adjacency)

theorem neighbor_eq (v : V) : graph.neighborFinset v = (neighbors v).toFinset := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, List.mem_toFinset]
  rfl

theorem closed_of_check {B : Finset V}
    (h : ∀ v ∈ B, ((neighbors v).toFinset \ B).card ≠ 1) : Closed graph B := by
  intro v hv
  simpa only [neighbor_eq] using h v hv

theorem initial_single (v : V) :
    initial graph {v} = insert v (neighbors v).toFinset := by
  simp [initial, neighbor_eq]

theorem initial_pair (v w : V) :
    initial graph {v, w} =
      insert v (neighbors v).toFinset ∪ insert w (neighbors w).toFinset := by
  ext x
  simp only [initial, neighbor_eq, mem_union, mem_insert, mem_singleton, mem_biUnion]
  constructor
  · rintro ((rfl | rfl) | ⟨y, rfl | rfl, hy⟩)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (Or.inr hy)
    · exact Or.inr (Or.inr hy)
  · rintro ((rfl | hx) | (rfl | hx))
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr ⟨v, Or.inl rfl, hx⟩
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨w, Or.inr rfl, hx⟩

end FortObservance.Witness
```

### `FortWitnessMinimum.lean`

```lean
import FortWitnessGraph
import Mathlib.Tactic.FinCases

namespace FortObservance.Witness

open Finset

private theorem inter_eq_filter (x : V) (F : Finset V) :
    graph.neighborFinset x ∩ F = F.filter (adjacency x) := by
  ext y
  rw [mem_inter, SimpleGraph.mem_neighborFinset, mem_filter]
  exact and_comm

private def violatesFort (F : Finset V) (x : V) : Prop :=
  x ∉ F ∧ (F.filter (adjacency x)).card = 1

private instance (F : Finset V) (x : V) : Decidable (violatesFort F x) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def hasViolation (F : Finset V) : Bool :=
  (List.finRange 25).any fun x => decide (violatesFort F x)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check_sorted_triples (a : V) :
    ∀ b c : V, a ≤ b → b ≤ c → hasViolation {a, b, c} = true := by
  fin_cases a <;> decide

private theorem sorted_triple_certificate (a b c : V) (hab : a ≤ b) (hbc : b ≤ c) :
    ¬ IsFort graph {a, b, c} := by
  obtain ⟨x, _, hx⟩ := List.any_eq_true.mp (check_sorted_triples a b c hab hbc)
  have hv := of_decide_eq_true hx
  intro h
  apply h.2 x hv.1
  rw [inter_eq_filter]
  exact hv.2

private theorem triple_not_fort (a b c : V) : ¬ IsFort graph {a, b, c} := by
  have reorder (u v w : V)
      (he : ({a, b, c} : Finset V) = {u, v, w}) (huv : u ≤ v) (hvw : v ≤ w) :
      ¬ IsFort graph {a, b, c} :=
    he ▸ sorted_triple_certificate u v w huv hvw
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact sorted_triple_certificate a b c hab hbc
    · rcases le_total a c with hac | hca
      · apply reorder a c b _ hac hcb
        ext x
        simp [or_comm]
      · apply reorder c a b _ hca hab
        ext x
        simp [or_comm, or_left_comm]
  · rcases le_total a c with hac | hca
    · exact reorder b a c (insert_comm _ _ _) hba hac
    · rcases le_total b c with hbc | hcb
      · apply reorder b c a _ hbc hca
        ext x
        simp [or_comm, or_left_comm]
      · apply reorder c b a _ hcb hba
        ext x
        simp [or_comm, or_left_comm]

private theorem card_ge_four_of_fort (F : Finset V) (hf : IsFort graph F) : 4 ≤ F.card := by
  have hp := card_pos.mpr hf.1
  by_contra! h
  have hcases : F.card = 1 ∨ F.card = 2 ∨ F.card = 3 := by omega
  rcases hcases with h1 | h2 | h3
  · obtain ⟨a, rfl⟩ := card_eq_one.mp h1
    exact triple_not_fort a a a (by simpa using hf)
  · obtain ⟨a, b, _, rfl⟩ := card_eq_two.mp h2
    exact triple_not_fort a a b (by simpa using hf)
  · obtain ⟨a, b, c, _, _, _, rfl⟩ := card_eq_three.mp h3
    exact triple_not_fort a b c hf

private def fourFort : Finset V := {1, 2, 3, 6}

private theorem fourFort_isFort : IsFort graph fourFort := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  have h : ∀ x : V, ¬ violatesFort fourFort x := by decide
  intro x hx hc
  exact h x ⟨hx, (inter_eq_filter x fourFort) ▸ hc⟩

theorem minFort_graph : minFort graph = 4 := by
  refine le_antisymm ?_ (le_minFort graph card_ge_four_of_fort)
  have h := minFort_le graph fourFort_isFort
  have hc : fourFort.card = 4 := by decide
  change minFort graph ≤ ((4 : ℕ) : WithTop ℕ)
  simpa only [hc] using h

end FortObservance.Witness
```

### `FortWitnessOptimum.lean`

```lean
import FortWitnessGraph
import Mathlib.Tactic.FinCases

namespace FortObservance.Witness

open Finset

private def localSingleBound : Fin 12 → List V
  | 0 => [0, 1, 8, 12]
  | 1 => [0, 2, 8, 9]
  | 2 => [0, 3, 9, 10]
  | 3 => [0, 4, 8, 10, 11]
  | 4 => [0, 5, 9, 11, 12]
  | 5 => [0, 6, 10, 12]
  | 6 => [0, 7, 11]
  | 7 => [0, 1, 2, 4, 8, 9, 12]
  | 8 => [0, 2, 3, 5, 8, 9, 10]
  | 9 => [0, 3, 4, 6, 9, 10, 12]
  | 10 => [0, 4, 5, 7, 11]
  | 11 => [0, 1, 5, 6, 8, 10, 12]

private def closedNeighborhood (a : V) : Finset V :=
  insert a (neighbors a).toFinset

private def singleBound (a : V) : Finset V :=
  if a = 0 then closedNeighborhood a
  else (inCopy a (localSingleBound (Fin.ofNat 12 (a.val - 1)))).toFinset

private def pairBound (a b : V) : Finset V :=
  if a = 0 then closedNeighborhood a ∪ closedNeighborhood b
  else if a.val ≤ 12 ∧ b.val ≤ 12 then
    (List.finRange 25 |>.filter fun v => v.val ≤ 12).toFinset
  else if 12 < a.val ∧ 12 < b.val then
    (List.finRange 25 |>.filter fun v => v = 0 ∨ 12 < v.val).toFinset
  else singleBound a ∪ singleBound b

private def boundCheck (A B : Finset V) (m : ℕ) : Prop :=
  A ⊆ B ∧ B.card ≤ m ∧ ∀ x ∈ B, ((neighbors x).toFinset \ B).card ≠ 1

private instance (A B : Finset V) (m : ℕ) : Decidable (boundCheck A B m) :=
  inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 10000 in
private theorem single_check :
    ∀ a : V, boundCheck (closedNeighborhood a) (singleBound a) 11 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pair_check (a : V) :
    ∀ b : V, a ≤ b →
      boundCheck (closedNeighborhood a ∪ closedNeighborhood b) (pairBound a b) 14 := by
  fin_cases a <;> decide

private theorem upper_of_bound {S A B : Finset V} {m : ℕ} (hA : initial graph S = A)
    (hb : boundCheck A B m) : (obsClosure graph S).card ≤ m :=
  (card_le_card (obsClosure_least graph (hA ▸ hb.1) (closed_of_check hb.2.2))).trans hb.2.1

private theorem pair_upper (a b : V) : (obsClosure graph {a, b}).card ≤ 14 := by
  rcases le_total a b with hab | hba
  · exact upper_of_bound (initial_pair a b) (pair_check a b hab)
  · have he : ({a, b} : Finset V) = {b, a} := by
      ext x
      simp [or_comm]
    rw [he]
    exact upper_of_bound (initial_pair b a) (pair_check b a hba)

theorem maxObs_one : maxObs graph 1 = 11 := by
  apply le_antisymm
  · apply maxObs_le graph
    intro S hS
    obtain ⟨a, rfl⟩ := card_eq_one.mp hS
    exact upper_of_bound (initial_single a) (single_check a)
  · have h := card_obsClosure_le_maxObs graph (S := {0}) (card_singleton _)
    have hcard : (closedNeighborhood 0).card = 11 := by decide
    have h' := card_le_card (initial_subset_obsClosure graph {0})
    rw [initial_single] at h'
    change (closedNeighborhood 0).card ≤ _ at h'
    rw [hcard] at h'
    exact h'.trans h

theorem maxObs_two : maxObs graph 2 = 14 := by
  apply le_antisymm
  · apply maxObs_le graph
    intro S hS
    obtain ⟨a, b, _, rfl⟩ := card_eq_two.mp hS
    exact pair_upper a b
  · have hsize : ({0, 8} : Finset V).card = 2 := by decide
    have h := card_obsClosure_le_maxObs graph hsize
    have hcard : (closedNeighborhood 0 ∪ closedNeighborhood 8).card = 14 := by decide
    have h' := card_le_card (initial_subset_obsClosure graph {0, 8})
    rw [initial_pair] at h'
    change (closedNeighborhood 0 ∪ closedNeighborhood 8).card ≤ _ at h'
    rw [hcard] at h'
    exact h'.trans h

end FortObservance.Witness
```

### `FortCounterexample.lean`

```lean
import FortWitnessMinimum
import FortWitnessOptimum

namespace FortObservance

open Witness

theorem three_le_γP_graph : 3 ≤ γP graph := by
  have hfull := maxObs_γP graph
  change maxObs graph (γP graph) = 25 at hfull
  by_contra! h
  have hcases : γP graph = 0 ∨ γP graph = 1 ∨ γP graph = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · simp [h0, maxObs_zero] at hfull
  · simp [h1, maxObs_one] at hfull
  · simp [h2, maxObs_two] at hfull

theorem MObs_two_graph : MObs graph 2 = 3 := by
  change (maxObs graph 2 : ℤ) - (maxObs graph 1 : ℤ) = 3
  rw [maxObs_two, maxObs_one]
  decide

/-- The literal negation of the minimum-fort-size conjecture. -/
theorem minimumFort_marginalObs_refuted :
    ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : ℕ),
      4 ≤ minFort G → 1 ≤ i → i ≤ γP G → 4 ≤ MObs G i) := by
  intro conjecture
  have hfort : 4 ≤ minFort graph := by rw [minFort_graph]
  have htwo : 2 ≤ γP graph := (by decide : 2 ≤ 3).trans three_le_γP_graph
  have h := @conjecture 25 graph _ 2 hfort (by decide) htwo
  rw [MObs_two_graph] at h
  omega

#check terminal_run_eq_obsClosure
#check obsClosure_run
#check minFort_graph
#check maxObs_one
#check maxObs_two
#check three_le_γP_graph
#check MObs_two_graph
#check minimumFort_marginalObs_refuted

#print axioms terminal_run_eq_obsClosure
#print axioms obsClosure_run
#print axioms minFort_graph
#print axioms maxObs_one
#print axioms maxObs_two
#print axioms three_le_γP_graph
#print axioms MObs_two_graph
#print axioms minimumFort_marginalObs_refuted

end FortObservance
```
