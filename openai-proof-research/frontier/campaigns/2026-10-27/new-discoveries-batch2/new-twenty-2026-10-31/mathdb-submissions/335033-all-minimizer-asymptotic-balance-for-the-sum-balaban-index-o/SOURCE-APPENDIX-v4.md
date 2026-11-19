# Complete local production source closure v4

All 55 local modules, including every one of the 48 reused dependency SOURCES, follow literally. No olean content substitutes for source. Source provenance, source/olean SHA256 and imports: SOURCE-MAP-v4.json. Pinned upstream library/toolchain identifiers: PINS.json. Honest reuse: only the seven r4 modules were freshly compiled/checked here. Independent acceptance MUST rebuild/check ALL 55 modules freshly in a NEW authorized task without these project oleans.

## Extraction and rebuild

Markers include UTF-8 byte length and SHA256. Read exactly that byte count after a BEGIN marker, verify its hash, then require the END marker. Reject path traversal, duplicate module names, marker collisions, and unexpected modules. Write only to a fresh authorized src directory through that task writer. Compare SOURCE-MAP-v4.json. Build order:

Dumbbell, Distances, Transmissions, IndexTarget, GeometryCounts, EdgeCounts, EdgeFormula, SourceIdentities, PathPolynomial, Angular, ShiftedTransmission, GlobalBounds, Coercivity, Annulus, EdgeSums, FiveSums, ActualFive, PathEdges, PathError, PathKernel, PathSumError, ReferenceIntegral, ReferenceRectangle, ReferenceValue, TransmissionLower, MovingInterval, TrialBound, ActualRectangle, TrialExistence, MinimizerAnnulus, PathFirstCorrection, CliquePolynomials, CliqueError, CliqueTaylor, RadialCost, CliqueSumCorrection, OptimalTrial, Prefactor, ActualPrefactor, EdgeFirstCorrection, OptimalTrialEventually, NormalizedBounds, ProductCorrection, ClusterSelection, MixedProduct, UniformExpansion, UniformEndpoint, AuditV3, TrialLimits, TrialExpansion, MinimizerComparison, EventualComparison, MinimizingCluster, SourceEndpoint, AuditV4

Use the pinned Lean 4.34.1 executables/libraries from PINS.json and immutable check32.sh/checker32.sh wrappers with unique labels, j1, M3500, warningsAsErrors and one Lean thread. For EACH module in order, run taskset -c 0,1 bash ./check32.sh MODULE UNIQUE_LABEL, then taskset -c 0,1 bash ./checker32.sh MODULE UNIQUE_LABEL. That independent task needs its OWN adequate call budget (at least 110 calls), source/artifact grants and resource wrapper. Do not run raw Lean or reuse campaign oleans. This is a rebuild specification, not a claim that this replay occurred.

Literal marker grammar: BEGIN line is `@@SB335033_LITERAL_SOURCE_V4 BEGIN NAME BYTES SHA256@@`; payload follows one newline, exactly BYTES UTF-8 bytes; then a newline and `@@SB335033_LITERAL_SOURCE_V4 END NAME@@`. Nothing inside a payload is executable extraction metadata.

@@SB335033_LITERAL_SOURCE_V4 BEGIN Dumbbell 2719 28c9d92f7501f256cad414117931369400cbf6edb0a4859b6d5e6dfad08c3b6d@@
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Sum

namespace SumBalaban
abbrev Vertex (a b d : ℕ) := Fin a ⊕ (Fin b ⊕ Fin d)
abbrev left {a b d : ℕ} (i : Fin a) : Vertex a b d := Sum.inl i
abbrev path {a b d : ℕ} (i : Fin b) : Vertex a b d := Sum.inr (Sum.inl i)
abbrev right {a b d : ℕ} (i : Fin d) : Vertex a b d := Sum.inr (Sum.inr i)

def Adj {a b d : ℕ} : Vertex a b d → Vertex a b d → Prop
  | .inl i, .inl j => i ≠ j
  | .inl _, .inr (.inl j) => j.val = 0
  | .inr (.inl i), .inl _ => i.val = 0
  | .inr (.inl i), .inr (.inl j) => i.val + 1 = j.val ∨ j.val + 1 = i.val
  | .inr (.inl i), .inr (.inr _) => i.val + 1 = b
  | .inr (.inr _), .inr (.inl j) => j.val + 1 = b
  | .inr (.inr i), .inr (.inr j) => i ≠ j
  | _, _ => False

def graph (a b d : ℕ) : SimpleGraph (Vertex a b d) where
  Adj := Adj
  symm := by
    constructor
    intro u v h
    rcases u with i | i <;> rcases v with j | j
    · exact Ne.symm h
    · rcases j with j | j
      · exact h
      · exact False.elim h
    · rcases i with i | i
      · exact h
      · exact False.elim h
    · rcases i with i | i <;> rcases j with j | j
      · simpa only [Adj, or_comm] using h
      · exact h
      · exact h
      · exact Ne.symm h
  loopless := by
    constructor
    intro u
    rcases u with i | i
    · simp [Adj]
    · rcases i with i | i
      · simp [Adj]
      · simp [Adj]

instance (a b d : ℕ) : DecidableRel (graph a b d).Adj := by
  intro u v
  change Decidable (Adj u v)
  unfold Adj
  split <;> infer_instance

theorem path_reachable {a b d : ℕ} (hb : 0 < b) (i : ℕ) (hi : i < b) :
    (graph a b d).Reachable (path ⟨0,hb⟩) (path ⟨i,hi⟩) := by
  induction i with
  | zero => exact .refl _
  | succ i ih =>
    exact (ih (by omega)).trans (SimpleGraph.Adj.reachable (by
      change @Adj a b d (path ⟨i,by omega⟩) (path ⟨i+1,hi⟩)
      simp [Adj]))

theorem reachable_from_start {a b d : ℕ} (hb : 0 < b) (u : Vertex a b d) :
    (graph a b d).Reachable (path ⟨0,hb⟩) u := by
  rcases u with i | i
  · exact SimpleGraph.Adj.reachable (by change @Adj a b d (path ⟨0,hb⟩) (left i); rfl)
  · rcases i with i | i
    · exact path_reachable hb i.val i.isLt
    · exact (path_reachable (a:=a) (d:=d) hb (b-1) (by omega)).trans
        (SimpleGraph.Adj.reachable (by change @Adj a b d (path ⟨b-1,by omega⟩) (right i); simp [Adj]; omega))

theorem preconnected {a b d : ℕ} (hb : 0 < b) : (graph a b d).Preconnected := by
  intro u v
  exact (reachable_from_start hb u).symm.trans (reachable_from_start hb v)

#print axioms graph
#print axioms path_reachable
#print axioms preconnected
#eval Lean.versionString
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END Dumbbell@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN Distances 5582 5a6cc4a767140b9a131cfe29cbc4b8f842becd0089e36a7592efa9f5bf00c2ea@@
import Dumbbell
namespace SumBalaban

theorem connected {a b d : ℕ} (hb : 0 < b) : (graph a b d).Connected := by
  let : Nonempty (Vertex a b d) := ⟨path ⟨0,hb⟩⟩
  exact ⟨preconnected hb⟩

def coordinate {a b d : ℕ} : Vertex a b d → ℕ
  | .inl _ => 0
  | .inr (.inl i) => i.val + 1
  | .inr (.inr _) => b + 1

theorem coordinate_step {a b d : ℕ} {u v : Vertex a b d}
    (h : (graph a b d).Adj u v) : coordinate v ≤ coordinate u + 1 := by
  rcases u with i | i <;> rcases v with j | j
  · simp [coordinate]
  · rcases j with j | j
    · change j.val = 0 at h
      simp only [coordinate]
      omega
    · exact False.elim h
  · rcases i with i | i
    · simp only [coordinate]
      omega
    · exact False.elim h
  · rcases i with i | i <;> rcases j with j | j
    · change i.val+1=j.val ∨ j.val+1=i.val at h
      simp only [coordinate]
      omega
    · change i.val+1=b at h
      simp only [coordinate]
      omega
    · change j.val+1=b at h
      simp only [coordinate]
      omega
    · simp [coordinate]

theorem coordinate_walk {a b d : ℕ} {u v : Vertex a b d}
    (p : (graph a b d).Walk u v) : coordinate v ≤ coordinate u + p.length := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have hs := coordinate_step h
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem coordinate_dist {a b d : ℕ} (hb : 0 < b) (u v : Vertex a b d) :
    coordinate v ≤ coordinate u + (graph a b d).dist u v := by
  obtain ⟨p,hp⟩ := (connected (a:=a) (d:=d) hb).exists_walk_length_eq_dist u v
  simpa [hp] using coordinate_walk p

theorem path_dist_le {a b d : ℕ} (hb : 0 < b) (i j : Fin b) (hij : i.val ≤ j.val) :
    (graph a b d).dist (path i) (path j) ≤ j.val-i.val := by
  obtain ⟨j,hj⟩ := j
  induction j with
  | zero =>
    have he : i = ⟨0,hj⟩ := Fin.ext (by dsimp (config := { failIfUnchanged := false }) only at *; omega)
    subst i
    simp
  | succ j ih =>
    by_cases he : i.val = j+1
    · have he' : i = ⟨j+1,hj⟩ := Fin.ext he
      subst i
      simp
    · have hj' : j < b := by dsimp (config := { failIfUnchanged := false }) only at *; omega
      have hsmall := ih hj' (by dsimp (config := { failIfUnchanged := false }) only at *; omega)
      have ha : (graph a b d).Adj (path ⟨j,hj'⟩) (path ⟨j+1,hj⟩) := by
        change @Adj a b d (path ⟨j,hj'⟩) (path ⟨j+1,hj⟩)
        simp [Adj]
      have hone := SimpleGraph.dist_eq_one_iff_adj.mpr ha
      have ht := (connected (a:=a) (d:=d) hb).dist_triangle
        (u:=path i) (v:=path ⟨j,hj'⟩) (w:=path ⟨j+1,hj⟩)
      dsimp (config := { failIfUnchanged := false }) only at *
      omega

theorem path_dist_of_le {a b d : ℕ} (hb : 0 < b) (i j : Fin b) (hij : i.val ≤ j.val) :
    (graph a b d).dist (path i) (path j) = j.val-i.val := by
  have hu := path_dist_le (a:=a) (d:=d) hb i j hij
  have hl := coordinate_dist (a:=a) (d:=d) hb (path i) (path j)
  simp only [coordinate] at hl
  omega

theorem left_path_dist {a b d : ℕ} (hb : 0 < b) (u : Fin a) (i : Fin b) :
    (graph a b d).dist (left u) (path i) = i.val+1 := by
  have ha : (graph a b d).Adj (left u) (path ⟨0,hb⟩) := by rfl
  have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ha
  have hp := path_dist_of_le (a:=a) (d:=d) hb ⟨0,hb⟩ i (by dsimp (config := { failIfUnchanged := false }) only at *; omega)
  have ht := (connected (a:=a) (d:=d) hb).dist_triangle
    (u:=left u) (v:=path ⟨0,hb⟩) (w:=path i)
  have hl := coordinate_dist (a:=a) (d:=d) hb (left u) (path i)
  simp only [coordinate] at hl
  omega

theorem path_right_dist {a b d : ℕ} (hb : 0 < b) (i : Fin b) (u : Fin d) :
    (graph a b d).dist (path i) (right u) = b-i.val := by
  have ha : (graph a b d).Adj (path ⟨b-1,by omega⟩) (right u) := by
    change @Adj a b d (path ⟨b-1,by omega⟩) (right u)
    simp only [Adj]; omega
  have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ha
  have hp := path_dist_of_le (a:=a) (d:=d) hb i ⟨b-1,by omega⟩ (by change i.val ≤ b-1; omega)
  have ht := (connected (a:=a) (d:=d) hb).dist_triangle
    (u:=path i) (v:=path ⟨b-1,by dsimp (config := { failIfUnchanged := false }) only at *; omega⟩) (w:=right u)
  have hl := coordinate_dist (a:=a) (d:=d) hb (path i) (right u)
  simp only [coordinate] at hl
  omega

theorem left_right_dist {a b d : ℕ} (hb : 0 < b) (u : Fin a) (v : Fin d) :
    (graph a b d).dist (left u) (right v) = b+1 := by
  have hp := left_path_dist (d:=d) hb u (⟨b-1,by omega⟩ : Fin b)
  have hr := path_right_dist (a:=a) hb (⟨b-1,by dsimp (config := { failIfUnchanged := false }) only at *; omega⟩ : Fin b) v
  have ht := (connected (a:=a) (d:=d) hb).dist_triangle
    (u:=left u) (v:=path ⟨b-1,by dsimp (config := { failIfUnchanged := false }) only at *; omega⟩) (w:=right v)
  have hl := coordinate_dist (a:=a) (d:=d) hb (left u) (right v)
  simp only [coordinate] at hl
  omega

theorem left_left_dist {a b d : ℕ} (u v : Fin a) :
    (graph a b d).dist (left u) (left v) = if u=v then 0 else 1 := by
  split_ifs with h
  · subst v; exact SimpleGraph.dist_self
  · apply SimpleGraph.dist_eq_one_iff_adj.mpr
    exact h

theorem right_right_dist {a b d : ℕ} (u v : Fin d) :
    (graph a b d).dist (right u) (right v) = if u=v then 0 else 1 := by
  split_ifs with h
  · subst v; exact SimpleGraph.dist_self
  · apply SimpleGraph.dist_eq_one_iff_adj.mpr
    exact h

#print axioms coordinate_dist
#print axioms path_dist_of_le
#print axioms left_path_dist
#print axioms path_right_dist
#print axioms left_right_dist
#print axioms left_left_dist
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END Distances@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN Transmissions 2951 718fbc5092ff7391f9f8210c74b55abb02fde3a5925e574021449cc3cf1d553c@@
import Distances
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
namespace SumBalaban
open scoped BigOperators
noncomputable def transmission {a b d : ℕ} (u : Vertex a b d) : ℕ :=
  ∑ v : Vertex a b d, (graph a b d).dist u v

theorem clique_sum (a : ℕ) (u : Fin a) :
    (∑ v : Fin a, if u=v then (0:ℕ) else 1) = a-1 := by
  classical
  simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    smul_eq_mul, mul_one]
  have he : Finset.univ.filter (fun v : Fin a => ¬u=v) = Finset.univ.erase u := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      and_true]
    exact ne_comm
  rw [he, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]

theorem left_transmission_sum {a b d : ℕ} (hb : 0 < b) (u : Fin a) :
    transmission (d:=d) (left u : Vertex a b d) =
      (a-1) + (∑ i : Fin b, (i.val+1)) + d*(b+1) := by
  classical
  unfold transmission
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  simp only [left_left_dist, left_path_dist hb, left_right_dist hb]
  rw [clique_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

theorem right_transmission_sum {a b d : ℕ} (hb : 0 < b) (u : Fin d) :
    transmission (a:=a) (right u : Vertex a b d) =
      (d-1) + (∑ i : Fin b, (b-i.val)) + a*(b+1) := by
  classical
  unfold transmission
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hl : ∀ v : Fin a, (graph a b d).dist (right u) (left v) = b+1 := by
    intro v
    rw [SimpleGraph.dist_comm]
    exact left_right_dist hb v u
  have hp : ∀ i : Fin b, (graph a b d).dist (right u) (path i) = b-i.val := by
    intro i
    rw [SimpleGraph.dist_comm]
    exact path_right_dist hb i u
  simp only [hl, hp, right_right_dist, clique_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

theorem path_dist {a b d : ℕ} (hb : 0 < b) (i j : Fin b) :
    (graph a b d).dist (path i) (path j) =
      if i.val ≤ j.val then j.val-i.val else i.val-j.val := by
  split_ifs with h
  · exact path_dist_of_le hb i j h
  · rw [SimpleGraph.dist_comm]
    exact path_dist_of_le hb j i (by omega)

theorem path_transmission_sum {a b d : ℕ} (hb : 0 < b) (i : Fin b) :
    transmission (path i : Vertex a b d) =
      a*(i.val+1) +
      (∑ j : Fin b, if i.val ≤ j.val then j.val-i.val else i.val-j.val) +
      d*(b-i.val) := by
  classical
  unfold transmission
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hl : ∀ v : Fin a, (graph a b d).dist (path i) (left v) = i.val+1 := by
    intro v
    rw [SimpleGraph.dist_comm]
    exact left_path_dist hb v i
  simp only [hl, path_dist hb, path_right_dist hb, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

#print axioms left_transmission_sum
#print axioms right_transmission_sum
#print axioms path_transmission_sum
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END Transmissions@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN IndexTarget 3208 a8ef3f60b90a719eb77b6377471397e8da4a6fb4a18b32eb82252503ae276871@@
import Transmissions
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Positivity

namespace SumBalaban
open scoped BigOperators
noncomputable def edgeWeight {a b d : ℕ} : Sym2 (Vertex a b d) → ℝ :=
  Sym2.lift ⟨fun u v => 1 / Real.sqrt ((transmission u : ℝ) + (transmission v : ℝ)),
    by intro u v; dsimp only; rw [add_comm]⟩

noncomputable def edgeCount (a b d : ℕ) : ℕ := by
  classical
  exact (graph a b d).edgeFinset.card

noncomputable def SJ (a b d : ℕ) : ℝ := by
  classical
  exact (edgeCount a b d : ℝ) /
    ((edgeCount a b d : ℝ) - (a+b+d : ℕ) + 2) *
    ∑ e ∈ (graph a b d).edgeFinset, edgeWeight e

noncomputable def Q : ℝ := Real.sqrt 2 * Real.log (1+Real.sqrt 2)
noncomputable def c : ℝ := Real.sqrt (Real.sqrt Q)

theorem Q_pos : 0 < Q := by
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  exact mul_pos hs (Real.log_pos (by linarith))
theorem c_pos : 0 < c := Real.sqrt_pos.2 (Real.sqrt_pos.2 Q_pos)

abbrev Triple := ℕ × ℕ × ℕ
def admissible (n : ℕ) (t : Triple) : Prop :=
  0<t.1 ∧ 0<t.2.1 ∧ 0<t.2.2 ∧ t.1+t.2.1+t.2.2=n ∧ t.1≤t.2.2
instance (n : ℕ) : DecidablePred (admissible n) := fun t => by
  unfold admissible
  infer_instance
noncomputable def objective (t : Triple) : ℝ := SJ t.1 t.2.1 t.2.2

def minimizes (n : ℕ) (t : Triple) : Prop :=
  admissible n t ∧ ∀ s, admissible n s → objective t ≤ objective s

def candidates (n : ℕ) : Finset Triple :=
  ((Finset.range (n+1)).product ((Finset.range (n+1)).product (Finset.range (n+1)))).filter
    (fun t => admissible n t)

@[simp] theorem mem_candidates (n : ℕ) (t : Triple) : t ∈ candidates n ↔ admissible n t := by
  rw [candidates, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    have hh := h
    unfold admissible at hh
    refine ⟨Finset.mem_product.mpr ⟨?_,Finset.mem_product.mpr ⟨?_,?_⟩⟩,h⟩
    all_goals apply Finset.mem_range.mpr; omega

theorem minimum_attained (n : ℕ) (hn : 3≤n) : ∃ t, minimizes n t := by
  classical
  have h : admissible n (1,n-2,1) := by simp only [admissible]; omega
  have hs : (candidates n).Nonempty := ⟨(1,n-2,1),(mem_candidates _ _).2 h⟩
  obtain ⟨t,ht,hm⟩ := (candidates n).exists_min_image objective hs
  exact ⟨t,(mem_candidates _ _).1 ht, fun s hs => hm s ((mem_candidates _ _).2 hs)⟩

-- Exact sequential source target: a proposition, not an asserted theorem.
-- Every eventually minimizing choice over ALL positive triples modulo reversal.
def SourceTarget : Prop :=
  ∀ f : ℕ → Triple,
    (∀ᶠ n in Filter.atTop, minimizes n (f n)) →
    Filter.Tendsto (fun n => ((f n).1 : ℝ) / Real.sqrt n) Filter.atTop (nhds c) ∧
    Filter.Tendsto (fun n => ((f n).2.2 : ℝ) / Real.sqrt n) Filter.atTop (nhds c) ∧
    Filter.Tendsto (fun n => ((f n).2.1 : ℝ) / n) Filter.atTop (nhds 1)

#print axioms SJ
#print axioms Q_pos
#print axioms c_pos
#print axioms minimum_attained
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END IndexTarget@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN GeometryCounts 2979 6631ee67abd95f1e8a51e125ba4e88df3e88a765ee4e100aa0a275999b51f26c@@
import IndexTarget
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
namespace SumBalaban
open scoped BigOperators

theorem twice_sum_path_orders (b : ℕ) :
    2*(∑ i : Fin b, (i.val+1)) = b*(b+1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Fin.sum_univ_succ]
    have he : (∑ i : Fin b, (i.succ.val+1)) =
        (∑ i : Fin b, (i.val+1)) + b := by
      simp only [Fin.val_succ]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
    rw [he]
    simp only [Fin.val_zero]
    nlinarith

theorem twice_left_transmission {a b d : ℕ} (hb : 0 < b) (u : Fin a) :
    2*transmission (left u : Vertex a b d) =
      2*(a-1) + b*(b+1) + 2*d*(b+1) := by
  rw [left_transmission_sum hb]
  have hs := twice_sum_path_orders b
  nlinarith

theorem vertex_count (a b d : ℕ) : Fintype.card (Vertex a b d) = a+b+d := by
  simp only [Vertex, Fintype.card_sum, Fintype.card_fin]
  omega

theorem cycle_denominator_pos {a b d : ℕ} (hb : 0 < b) :
    0 < (edgeCount a b d : ℝ) - (a+b+d : ℕ) + 2 := by
  classical
  have h := (connected (a:=a) (d:=d) hb).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, vertex_count,
    ←SimpleGraph.edgeFinset_card] at h
  change a+b+d ≤ edgeCount a b d+1 at h
  have hc : ((a+b+d : ℕ) : ℝ) ≤ (edgeCount a b d : ℝ)+1 := by exact_mod_cast h
  linarith

theorem edgeWeight_formula {a b d : ℕ} (u v : Vertex a b d) :
    edgeWeight (s(u,v)) = 1/Real.sqrt ((transmission u : ℝ)+(transmission v : ℝ)) := rfl

-- Exact actual-edge partition, before evaluating the five cardinalities.
def edgeClass {a b d : ℕ} : Sym2 (Vertex a b d) → ℕ :=
  Sym2.lift ⟨fun u v => match u,v with
    | .inl _, .inl _ => 0
    | .inl _, .inr (.inl _) | .inr (.inl _), .inl _ => 1
    | .inr (.inl _), .inr (.inl _) => 2
    | .inr (.inr _), .inr (.inl _) | .inr (.inl _), .inr (.inr _) => 3
    | .inr (.inr _), .inr (.inr _) => 4
    | _,_ => 5,
    by
      intro u v
      rcases u with i|i <;> rcases v with j|j
      · rfl
      · rcases j <;> rfl
      · rcases i <;> rfl
      · rcases i <;> rcases j <;> rfl⟩

theorem edge_class_lt_five {a b d : ℕ} (e : Sym2 (Vertex a b d))
    (he : e ∈ (graph a b d).edgeSet) : edgeClass e < 5 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    have ha : (graph a b d).Adj u v := he
    rcases u with i|i <;> rcases v with j|j
    · norm_num [edgeClass, Sym2.lift_mk]
    · rcases j with j|j
      · norm_num [edgeClass, Sym2.lift_mk]
      · exact False.elim ha
    · rcases i with i|i
      · norm_num [edgeClass, Sym2.lift_mk]
      · exact False.elim ha
    · rcases i <;> rcases j <;> norm_num [edgeClass, Sym2.lift_mk]

#print axioms twice_left_transmission
#print axioms cycle_denominator_pos
#print axioms edge_class_lt_five
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END GeometryCounts@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN EdgeCounts 3190 9890d88fc063e728f816b2a15d744756f84e513a5cca4c267a04ae11e87bbdb0@@
import GeometryCounts
import Mathlib.Algebra.BigOperators.Ring.Finset
namespace SumBalaban
open scoped BigOperators

theorem degree_as_sum {a b d : ℕ} (u : Vertex a b d) :
    (graph a b d).degree u = ∑ v : Vertex a b d, if (graph a b d).Adj u v then 1 else 0 := by
  classical
  have hf : Finset.univ.filter ((graph a b d).Adj u) = (graph a b d).neighborFinset u := by
    ext v
    simp
  rw [←SimpleGraph.card_neighborFinset_eq_degree, ←hf]
  exact (Finset.sum_boole ((graph a b d).Adj u) Finset.univ).symm

theorem left_degree {a b d : ℕ} (hb : 0<b) (u : Fin a) :
    (graph a b d).degree (left u) = a := by
  classical
  rw [degree_as_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hin (v : Fin a) : (if (graph a b d).Adj (left u) (left v) then 1 else 0 : ℕ) =
      if u=v then 0 else 1 := by
    split_ifs <;> simp_all [graph, Adj]
  have hp (j : Fin b) : (if (graph a b d).Adj (left u) (path j) then 1 else 0 : ℕ) =
      if j=⟨0,hb⟩ then 1 else 0 := by
    split_ifs <;> simp_all [graph, Adj, Fin.ext_iff]
  have hr (v : Fin d) : (if (graph a b d).Adj (left u) (right v) then 1 else 0 : ℕ) = 0 := rfl
  simp_rw [hin, hp, hr]
  rw [clique_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero]
  have ha := u.isLt
  omega

theorem right_degree {a b d : ℕ} (hb : 0<b) (u : Fin d) :
    (graph a b d).degree (right u) = d := by
  classical
  rw [degree_as_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hin (v : Fin d) : (if (graph a b d).Adj (right u) (right v) then 1 else 0 : ℕ) =
      if u=v then 0 else 1 := by
    split_ifs <;> simp_all [graph, Adj]
  have hp (j : Fin b) : (if (graph a b d).Adj (right u) (path j) then 1 else 0 : ℕ) =
      if j=⟨b-1,by omega⟩ then 1 else 0 := by
    split_ifs <;> simp_all [graph, Adj, Fin.ext_iff] <;> omega
  have hl (v : Fin a) : (if (graph a b d).Adj (right u) (left v) then 1 else 0 : ℕ) = 0 := rfl
  simp_rw [hin, hp, hl]
  rw [clique_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, zero_add]
  have hd := u.isLt
  omega

theorem path_degree_sum {a b d : ℕ} (i : Fin b) :
    (graph a b d).degree (path i) =
      (if i.val=0 then a else 0) +
      (∑ j : Fin b, if i.val+1=j.val ∨ j.val+1=i.val then 1 else 0) +
      (if i.val+1=b then d else 0) := by
  classical
  rw [degree_as_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hl (v : Fin a) : (if (graph a b d).Adj (path i) (left v) then 1 else 0 : ℕ) =
      if i.val=0 then 1 else 0 := by
    split_ifs <;> simp_all [graph, Adj]
  have hr (v : Fin d) : (if (graph a b d).Adj (path i) (right v) then 1 else 0 : ℕ) =
      if i.val+1=b then 1 else 0 := by
    split_ifs <;> simp_all [graph, Adj]
  have hp (j : Fin b) : (if (graph a b d).Adj (path i) (path j) then 1 else 0 : ℕ) =
      if i.val+1=j.val ∨ j.val+1=i.val then 1 else 0 := by
    split_ifs <;> simp_all [graph, Adj]
  simp_rw [hl,hr,hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [mul_ite,mul_one,mul_zero]
  omega
#print axioms left_degree
#print axioms right_degree
#print axioms path_degree_sum
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END EdgeCounts@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN EdgeFormula 3362 9139f72e1c8c8d5787390c65af52cd15a190874a64e2300f0cce1320931f5958@@
import EdgeCounts
namespace SumBalaban
open scoped BigOperators

theorem path_neighbor_count {b : ℕ} (i : Fin b) :
    (∑ j : Fin b, if i.val+1=j.val ∨ j.val+1=i.val then (1:ℕ) else 0) =
      (if i.val + 1 < b then 1 else 0) + (if (0 : ℕ) < i.val then 1 else 0) := by
  classical
  have hs (j : Fin b) :
      (if i.val+1=j.val ∨ j.val+1=i.val then (1:ℕ) else 0) =
      (if i.val+1=j.val then 1 else 0) + (if j.val+1=i.val then 1 else 0) := by
    split_ifs <;> omega
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  have hnext : (∑ j : Fin b, if i.val+1=j.val then (1:ℕ) else 0) =
      if i.val + 1 < b then 1 else 0 := by
    by_cases h : i.val + 1 < b
    · have he (j : Fin b) : i.val+1=j.val ↔ j=⟨i.val+1,h⟩ := by
        constructor <;> intro he
        · exact Fin.ext he.symm
        · subst j; rfl
      simp_rw [he]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, h]
    · have he (j : Fin b) : ¬i.val+1=j.val := by have := j.isLt; omega
      simp only [he, h, ite_false, Finset.sum_const_zero]
  have hprev : (∑ j : Fin b, if j.val+1=i.val then (1:ℕ) else 0) =
      if (0 : ℕ) < i.val then 1 else 0 := by
    by_cases h : (0 : ℕ) < i.val
    · have he (j : Fin b) : j.val+1=i.val ↔ j=⟨i.val-1,by omega⟩ := by
        constructor <;> intro he
        · apply Fin.ext; dsimp only; omega
        · subst j; dsimp only; omega
      simp_rw [he]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, h]
    · have he (j : Fin b) : ¬j.val+1=i.val := by omega
      simp only [he, h, ite_false, Finset.sum_const_zero]
  rw [hnext,hprev]

theorem sum_path_degrees {a b d : ℕ} (hb : 0<b) :
    (∑ i : Fin b, (graph a b d).degree (path i)) = a+d+2*(b-1) := by
  classical
  have hzero (i : Fin b) : i.val=0 ↔ i=⟨0,hb⟩ := by
    constructor
    · exact fun h => Fin.ext h
    · intro h; subst i; rfl
  have hlast (i : Fin b) : i.val+1=b ↔ i=⟨b-1,by omega⟩ := by
    constructor
    · intro h; apply Fin.ext; dsimp only; omega
    · intro h; subst i; dsimp only; omega
  have hnext (i : Fin b) : (if i.val + 1 < b then (1:ℕ) else 0) =
      if (⟨b-1,by omega⟩ : Fin b)=i then 0 else 1 := by
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  have hprev (i : Fin b) : (if (0 : ℕ) < i.val then (1:ℕ) else 0) =
      if (⟨0,hb⟩ : Fin b)=i then 0 else 1 := by
    split_ifs <;> simp_all [Fin.ext_iff]
  simp_rw [path_degree_sum, path_neighbor_count, hzero, hlast, hnext, hprev]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, clique_sum]
  omega

theorem twice_edge_count {a b d : ℕ} (hb : 0<b) :
    2*edgeCount a b d = a*a+d*d+a+d+2*(b-1) := by
  classical
  have h := (graph a b d).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  have hl : (∑ u : Fin a, (graph a b d).degree (left u)) = a*a := by
    simp only [left_degree hb,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hr : (∑ u : Fin d, (graph a b d).degree (right u)) = d*d := by
    simp only [right_degree hb,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  rw [hl,hr,sum_path_degrees hb] at h
  change a*a+(a+d+2*(b-1)+d*d)=2*edgeCount a b d at h
  omega

#print axioms path_neighbor_count
#print axioms sum_path_degrees
#print axioms twice_edge_count
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END EdgeFormula@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN SourceIdentities 1726 3a6c8ca788663705751bacc6c5a30e751222b665545dd29f6a7bfd0aa4963b0b@@
import EdgeFormula
import Mathlib.Data.Fin.Rev
namespace SumBalaban
open scoped BigOperators

theorem edge_count_formula {a b d : ℕ} (hb : 0<b) :
    edgeCount a b d = (a+b+d)-1+(a*a+d*d-a-d)/2 := by
  have h := twice_edge_count (a:=a) (d:=d) hb
  have ha := Nat.le_mul_self a
  have hd := Nat.le_mul_self d
  omega

theorem natural_cycle_formula {a b d : ℕ} (hb : 0<b) :
    edgeCount a b d + 2 - (a+b+d) = 1+(a*a+d*d-a-d)/2 := by
  rw [edge_count_formula hb]
  omega

theorem reverse_path_sum (b : ℕ) :
    (∑ i : Fin b, (b - i.val)) = (∑ i : Fin b, (i.val+1)) := by
  have h := Equiv.sum_comp (Fin.revPerm (n:=b)) (fun i : Fin b => b-i.val)
  have he (i : Fin b) : b-(Fin.revPerm i).val = i.val+1 := by
    change b-i.rev.val=i.val+1
    simp only [Fin.val_rev]
    have := i.isLt
    omega
  simpa only [he] using h.symm

theorem twice_right_transmission {a b d : ℕ} (hb : 0<b) (u : Fin d) :
    2*transmission (right u : Vertex a b d) =
      2*(d-1)+b*(b+1)+2*a*(b+1) := by
  rw [right_transmission_sum hb, reverse_path_sum]
  have hs := twice_sum_path_orders b
  nlinarith

-- Real identity has no natural subtraction ambiguity.
theorem real_edge_count_formula {a b d : ℕ} (hb : 0<b) :
    (edgeCount a b d : ℝ) = (a+b+d : ℕ)-1+
      (((a:ℝ)^2+(d:ℝ)^2-a-d)/2) := by
  have h := twice_edge_count (a:=a) (d:=d) hb
  have hr : (2:ℝ)*edgeCount a b d =
      (a:ℝ)*a+(d:ℝ)*d+a+d+2*(b-1:ℕ) := by exact_mod_cast h
  have hb' : (b:ℝ)-1 = (b-1:ℕ) := by
    rw [Nat.cast_sub (by omega : 1≤b)]
    norm_num
  push_cast
  nlinarith

#print axioms edge_count_formula
#print axioms natural_cycle_formula
#print axioms twice_right_transmission
#print axioms real_edge_count_formula
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END SourceIdentities@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN PathPolynomial 1315 4daa38dbec1337a0c0c0b8885d1951db24babcf2f15c84669f327973dc49332e@@
import SourceIdentities
namespace SumBalaban
open scoped BigOperators

theorem twice_path_distance_sum (b i : ℕ) (hi : i<b) :
    2*(∑ j : Fin b, (if i≤j.val then j.val-i else i-j.val)) =
      i*(i+1)+(b-1-i)*(b-i) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases h : i<b
    · have hs := ih h
      have he : b-i=(b-1-i)+1 := by omega
      have hle : i≤b := by omega
      simp only [hle,ite_true]
      have h1 : b+1-1-i=b-i := by omega
      have h2 : b+1-i=(b-i)+1 := by omega
      rw [h1,h2,he]
      rw [he] at hs
      nlinarith
    · have he : i=b := by omega
      subst i
      have hf (j : Fin b) : ¬b≤j.val := by have := j.isLt; omega
      simp only [hf,ite_false,le_refl,ite_true,Nat.sub_self,add_zero]
      rw [reverse_path_sum]
      have hs := twice_sum_path_orders b
      simpa using hs

theorem twice_path_transmission {a b d : ℕ} (hb : 0<b) (i : Fin b) :
    2*transmission (path i : Vertex a b d) =
      i.val*(i.val+1)+(b-1-i.val)*(b-i.val)+
      2*a*(i.val+1)+2*d*(b-i.val) := by
  rw [path_transmission_sum hb]
  have hs := twice_path_distance_sum b i.val i.isLt
  nlinarith

#print axioms twice_path_distance_sum
#print axioms twice_path_transmission
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END PathPolynomial@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN Angular 1130 a081817cb51b54d172904c382d2d6bc71ac229b1baecc9013d7114e8eaf75eaa@@
import PathPolynomial
namespace SumBalaban
-- Algebraic selection lemma only; this does not assert the missing uniform expansion.
theorem angular_cubic {x y c : ℝ} (hx : 0≤x) (hy : 0≤y) (hc : 0<c)
    (hq : x^2+y^2=2*c^2) :
    2*c^3 ≤ x^3+y^3 ∧ (x^3+y^3=2*c^3 ↔ x=c ∧ y=c) := by
  have hs : 0<x+y := by nlinarith [sq_nonneg (x-y)]
  have hxy : 0≤x*y := mul_nonneg hx hy
  have hb : x+y≤2*c := by nlinarith [sq_nonneg (x-y)]
  have hp : 0<(x+y)^2+2*c*(x+y)-2*c^2 := by
    have hm : 0<2*c*(x+y) := mul_pos (by linarith) hs
    nlinarith
  have hid : 2*(x^3+y^3-2*c^3) =
      (2*c-x-y)*((x+y)^2+2*c*(x+y)-2*c^2) := by
    have hm := congrArg (fun t : ℝ => (x+y)*t) hq
    nlinarith
  have hn := mul_nonneg (by linarith : 0≤2*c-x-y) (le_of_lt hp)
  constructor
  · nlinarith
  · constructor
    · intro he
      have hz : 2*c-x-y=0 := by
        have hpz : (2*c-x-y)*((x+y)^2+2*c*(x+y)-2*c^2)=0 := by nlinarith
        exact (mul_eq_zero.mp hpz).resolve_right (ne_of_gt hp)
      constructor <;> nlinarith [sq_nonneg (x-y)]
    · rintro ⟨rfl,rfl⟩
      ring
#print axioms angular_cubic
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END Angular@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN ShiftedTransmission 928 30f52196035dc27c9901ad572c690a9e5147287de4c7a4f13b854c8f6b108d3d@@
import Angular
namespace SumBalaban

theorem shifted_actual_transmission {a b d : ℕ} (hb : 0<b) (i : Fin b) :
    (transmission (path i : Vertex a b d) : ℝ) =
      ((i.val+a:ℕ):ℝ)^2 - ((a+b+d:ℕ)-1:ℝ)*((i.val+a:ℕ):ℝ) +
      ((a+b+d:ℕ):ℝ)*((a+b+d:ℕ)-1:ℝ)/2 -
      (((a:ℝ)^2+(d:ℝ)^2-a-d)/2) := by
  have h := twice_path_transmission (a:=a) (d:=d) hb i
  have hr : (2:ℝ)*transmission (path i : Vertex a b d) =
      (i.val:ℝ)*(i.val+1) + ((b-1-i.val:ℕ):ℝ)*((b-i.val:ℕ):ℝ) +
      2*a*(i.val+1) + 2*d*((b-i.val:ℕ):ℝ) := by exact_mod_cast h
  have h1 : ((b-i.val:ℕ):ℝ)=(b:ℝ)-i.val := by
    rw [Nat.cast_sub (by omega : i.val≤b)]
  have h2 : ((b-1-i.val:ℕ):ℝ)=(b:ℝ)-1-i.val := by
    rw [Nat.cast_sub (by omega : i.val≤b-1), Nat.cast_sub (by omega : 1≤b)]
    norm_num
  rw [h1,h2] at hr
  push_cast
  nlinarith
#print axioms shifted_actual_transmission
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END ShiftedTransmission@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN GlobalBounds 2773 8c1ab6f0ffbc249608cba887ebca228caa27abf23d199c9ecaa51260a0be3d96@@
import ShiftedTransmission
namespace SumBalaban
open scoped BigOperators

theorem distance_le_order {a b d : ℕ} (hb : 0 < b) (u v : Vertex a b d) :
    (graph a b d).dist u v ≤ a+b+d := by
  rcases u with i | i <;> rcases v with j | j
  · rw [left_left_dist]; split_ifs <;> omega
  · rcases j with j | j
    · rw [left_path_dist hb]; have := j.isLt; omega
    · rw [left_right_dist hb]; have := i.isLt; have := j.isLt; omega
  · rcases i with i | i
    · rw [SimpleGraph.dist_comm, left_path_dist hb]; have := i.isLt; omega
    · rw [SimpleGraph.dist_comm, left_right_dist hb]; have := i.isLt; have := j.isLt; omega
  · rcases i with i | i <;> rcases j with j | j
    · rw [path_dist hb]; split_ifs <;> (have := i.isLt; have := j.isLt; omega)
    · rw [path_right_dist hb]; omega
    · rw [SimpleGraph.dist_comm, path_right_dist hb]; omega
    · rw [right_right_dist]; split_ifs <;> omega

theorem transmission_le_order_sq {a b d : ℕ} (hb : 0 < b) (u : Vertex a b d) :
    transmission u ≤ (a+b+d)^2 := by
  calc
    transmission u ≤ ∑ _v : Vertex a b d, (a+b+d) :=
      Finset.sum_le_sum (fun v _ => distance_le_order hb u v)
    _ = (a+b+d)^2 := by simp [pow_two, Nat.add_assoc]

theorem transmission_pos_of_adj {a b d : ℕ} {u v : Vertex a b d}
    (h : (graph a b d).Adj u v) : 0 < transmission u := by
  have hs : (graph a b d).dist u v ≤ transmission u :=
    Finset.single_le_sum (fun x _ => Nat.zero_le ((graph a b d).dist u x)) (Finset.mem_univ v)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h] at hs
  omega

theorem edgeWeight_lower {a b d : ℕ} (hb : 0 < b) (e : Sym2 (Vertex a b d))
    (he : e ∈ (graph a b d).edgeSet) :
    1 / (2*(a+b+d : ℕ) : ℝ) ≤ edgeWeight e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    have ha : (graph a b d).Adj u v := he
    have hu := transmission_le_order_sq hb u
    have hv := transmission_le_order_sq hb v
    have hp := transmission_pos_of_adj ha
    have hn : (0:ℝ) < (a+b+d : ℕ) := by exact_mod_cast (show 0<a+b+d by omega)
    have hpos : (0:ℝ) < (transmission u : ℝ)+(transmission v : ℝ) := by positivity
    have hs : Real.sqrt ((transmission u : ℝ)+(transmission v : ℝ)) ≤ 2*(a+b+d : ℕ) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hu' : (transmission u : ℝ) ≤ ((a+b+d : ℕ):ℝ)^2 := by exact_mod_cast hu
        have hv' : (transmission v : ℝ) ≤ ((a+b+d : ℕ):ℝ)^2 := by exact_mod_cast hv
        nlinarith [sq_nonneg (((a+b+d : ℕ):ℝ))]
    rw [edgeWeight_formula]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos) hs

#print axioms distance_le_order
#print axioms transmission_le_order_sq
#print axioms transmission_pos_of_adj
#print axioms edgeWeight_lower
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END GlobalBounds@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN Coercivity 3186 b105006b3d6d0b573ea1dd3551b9b07e7bdff83772f5e0b1a3f5eb9646d2553d@@
import GlobalBounds
namespace SumBalaban
open scoped BigOperators

theorem actual_edge_sum_lower {a b d : ℕ} (hb : 0<b) :
    (edgeCount a b d : ℝ) / (2*(a+b+d : ℕ)) ≤
      ∑ e ∈ (graph a b d).edgeFinset, edgeWeight e := by
  classical
  calc
    (edgeCount a b d : ℝ) / (2*(a+b+d : ℕ)) =
        ∑ _e ∈ (graph a b d).edgeFinset, (1 / (2*(a+b+d : ℕ)) : ℝ) := by
      simp [edgeCount, div_eq_mul_inv]
    _ ≤ _ := Finset.sum_le_sum (fun e he => edgeWeight_lower hb e (by simpa using he))

theorem order_le_edges_add_one {a b d : ℕ} (hb : 0<b) :
    ((a+b+d : ℕ):ℝ) ≤ (edgeCount a b d : ℝ)+1 := by
  have h := cycle_denominator_pos (a:=a) (d:=d) hb
  have hn : a+b+d ≤ edgeCount a b d+1 := by
    have hc := (connected (a:=a) (d:=d) hb).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, vertex_count,
      ←SimpleGraph.edgeFinset_card] at hc
    exact hc
  exact_mod_cast hn

theorem SJ_scaled_lower {a b d : ℕ} (hb : 0<b) :
    (edgeCount a b d : ℝ)^2 ≤
      (2*(a+b+d : ℕ))*((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2)*SJ a b d := by
  classical
  have hk := cycle_denominator_pos (a:=a) (d:=d) hb
  have hn : (0:ℝ)<(a+b+d : ℕ) := by exact_mod_cast (show 0<a+b+d by omega)
  have hm : (0:ℝ) ≤ (edgeCount a b d : ℝ) := by positivity
  have hs := actual_edge_sum_lower (a:=a) (d:=d) hb
  have ht := mul_le_mul_of_nonneg_left hs (div_nonneg hm (le_of_lt hk))
  change (edgeCount a b d : ℝ) / ((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2) *
      ((edgeCount a b d : ℝ)/(2*(a+b+d : ℕ))) ≤ SJ a b d at ht
  have he : (edgeCount a b d : ℝ) / ((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2) *
      ((edgeCount a b d : ℝ)/(2*(a+b+d : ℕ))) =
      (edgeCount a b d : ℝ)^2 / ((2*(a+b+d : ℕ))*((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2)) := by
        field_simp
  rw [he] at ht
  simpa only [mul_comm (SJ a b d)] using (div_le_iff₀ (mul_pos (by positivity) hk)).mp ht

theorem edgeCount_le_of_SJ_le {a b d : ℕ} {M : ℝ} (hb : 0<b)
    (hn : 2≤a+b+d) (hM : SJ a b d ≤ M) :
    (edgeCount a b d : ℝ) ≤ 2*(a+b+d : ℕ)*M := by
  have horder := order_le_edges_add_one (a:=a) (d:=d) hb
  have hn' : (2:ℝ) ≤ (a+b+d : ℕ) := by exact_mod_cast hn
  have hm : (0:ℝ)<(edgeCount a b d : ℝ) := by linarith
  have hk := cycle_denominator_pos (a:=a) (d:=d) hb
  have hl := SJ_scaled_lower (a:=a) (d:=d) hb
  have hsj : 0≤SJ a b d := by
    by_contra hh
    have hden : (0:ℝ)<(2*(a+b+d : ℕ))*((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2) := mul_pos (by linarith) hk
    have hf := mul_neg_of_pos_of_neg hden (lt_of_not_ge hh)
    linarith [sq_nonneg (edgeCount a b d : ℝ)]
  have hprod := mul_le_mul_of_nonneg_left hM
    (show 0≤(2*(a+b+d : ℕ):ℝ)*((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2) by positivity)
  have hM0 : 0≤M := le_trans hsj hM
  have hkM : ((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2)*M ≤ (edgeCount a b d : ℝ)*M := by nlinarith
  have hlast := mul_le_mul_of_nonneg_left hkM (show (0:ℝ)≤2*(a+b+d : ℕ) by positivity)
  nlinarith

#print axioms actual_edge_sum_lower
#print axioms SJ_scaled_lower
#print axioms edgeCount_le_of_SJ_le
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END Coercivity@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN Annulus 2186 13e38b610ebaf2d108351a7dc19faf8645c41b1e37e8555401c617171ad5f3bd@@
import Coercivity
namespace SumBalaban

theorem clique_squares_le_twice_edges {a b d : ℕ} (hb : 0<b) :
    (a:ℝ)^2+(d:ℝ)^2 ≤ 2*(edgeCount a b d : ℝ) := by
  have h := twice_edge_count (a:=a) (d:=d) hb
  have hr : (2:ℝ)*edgeCount a b d = (a:ℝ)*a+(d:ℝ)*d+a+d+2*(b-1:ℕ) := by exact_mod_cast h
  have hz : (0:ℝ)≤(b-1:ℕ) := by positivity
  nlinarith

theorem sublevel_clique_squares_upper {a b d : ℕ} {M : ℝ} (hb : 0<b)
    (hn : 2≤a+b+d) (hM : SJ a b d ≤ M) :
    (a:ℝ)^2+(d:ℝ)^2 ≤ 4*(a+b+d : ℕ)*M := by
  have hm := edgeCount_le_of_SJ_le hb hn hM
  have hq := clique_squares_le_twice_edges (a:=a) (d:=d) hb
  linarith

theorem sublevel_cycle_lower {a b d : ℕ} {M : ℝ} (hb : 0<b)
    (hn : 4≤a+b+d) (hM : SJ a b d ≤ M) :
    ((a+b+d : ℕ):ℝ) ≤ 8*((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2)*M := by
  have ho := order_le_edges_add_one (a:=a) (d:=d) hb
  have hn' : (4:ℝ)≤(a+b+d : ℕ) := by exact_mod_cast hn
  have hpos : (0:ℝ)<(a+b+d : ℕ) := by linarith
  have hmpos : (0:ℝ)<(edgeCount a b d : ℝ) := by linarith
  have hk := cycle_denominator_pos (a:=a) (d:=d) hb
  have hl := SJ_scaled_lower (a:=a) (d:=d) hb
  have hprod := mul_le_mul_of_nonneg_left hM
    (show 0≤(2*(a+b+d : ℕ):ℝ)*((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2) by positivity)
  have hsquare : ((a+b+d : ℕ):ℝ)^2 ≤ 4*(edgeCount a b d : ℝ)^2 := by nlinarith
  have hbound : ((a+b+d : ℕ):ℝ)*((a+b+d : ℕ):ℝ) ≤
      ((a+b+d : ℕ):ℝ)*(8*((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2)*M) := by nlinarith
  exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_comm] using hbound)

theorem sublevel_clique_squares_lower {a b d : ℕ} {M : ℝ} (hb : 0<b)
    (hn : 4≤a+b+d) (hlarge : 16*M≤((a+b+d : ℕ):ℝ)) (hM0 : 0≤M)
    (hM : SJ a b d ≤ M) :
    ((a+b+d : ℕ):ℝ) ≤ 8*M*((a:ℝ)^2+(d:ℝ)^2) := by
  have hl := sublevel_cycle_lower hb hn hM
  have he := real_edge_count_formula (a:=a) (d:=d) hb
  have hs : (0:ℝ)≤M*((a:ℝ)+(d:ℝ)) := mul_nonneg hM0 (by positivity)
  nlinarith

#print axioms sublevel_clique_squares_upper
#print axioms sublevel_cycle_lower
#print axioms sublevel_clique_squares_lower
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END Annulus@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN EdgeSums 1848 ed58b671ea90b4cc5c0e3fb39f40717fd94fad3ef26a9fedbf98be9722f0c5ba@@
import Annulus
namespace SumBalaban
open scoped BigOperators

theorem dart_sum_eq_twice_edge_sum (a b d : ℕ) :
    (∑ z : (graph a b d).Dart, edgeWeight z.edge) =
      2 * ∑ e ∈ (graph a b d).edgeFinset, edgeWeight e := by
  classical
  have hmap : ∀ z ∈ (Finset.univ : Finset (graph a b d).Dart),
      z.edge ∈ (graph a b d).edgeFinset := by
    intro z _
    simp
  calc
    _ = ∑ e ∈ (graph a b d).edgeFinset,
        ∑ _z ∈ Finset.univ.filter (fun z : (graph a b d).Dart => z.edge=e), edgeWeight e :=
      (Finset.sum_fiberwise_of_maps_to' hmap edgeWeight).symm
    _ = ∑ e ∈ (graph a b d).edgeFinset, 2*edgeWeight e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_const, (graph a b d).dart_edge_fiber_card e (by simpa using he)]
      simp
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem ordered_sum_eq_dart_sum (a b d : ℕ) :
    (∑ u : Vertex a b d, ∑ v : Vertex a b d,
      if (graph a b d).Adj u v then edgeWeight s(u,v) else 0) =
      ∑ z : (graph a b d).Dart, edgeWeight z.edge := by
  classical
  let f : Vertex a b d × Vertex a b d → ℝ := fun z => edgeWeight s(z.1,z.2)
  have he : (∑ z : (graph a b d).Dart, edgeWeight z.edge) =
      ∑ z ∈ (Finset.univ : Finset (Vertex a b d × Vertex a b d)).filter
        (fun z => (graph a b d).Adj z.1 z.2), f z := by
    apply Finset.sum_bij (fun z _ => z.toProd)
    · intro z _; simp
    · intro z _ z' _ h; exact SimpleGraph.Dart.ext _ _ h
    · intro z hz
      exact ⟨⟨z,(Finset.mem_filter.mp hz).2⟩,Finset.mem_univ _,rfl⟩
    · intro z _; rfl
  rw [he, Finset.sum_filter]
  exact (Fintype.sum_prod_type (fun z : Vertex a b d × Vertex a b d =>
    if (graph a b d).Adj z.1 z.2 then f z else 0)).symm

#print axioms dart_sum_eq_twice_edge_sum
#print axioms ordered_sum_eq_dart_sum
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END EdgeSums@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN FiveSums 2348 a4a463e83e1199c1da5e2a7da86070752ab1456d637f5caa911b2b4a85e39b78@@
import EdgeSums
namespace SumBalaban
open scoped BigOperators
noncomputable def leftW (a b d : ℕ) : ℕ :=
  (a-1)+(∑ i : Fin b, (i.val+1))+d*(b+1)
noncomputable def rightW (a b d : ℕ) : ℕ :=
  (d-1)+(∑ i : Fin b, (b-i.val))+a*(b+1)
noncomputable def kernel (p q : ℕ) : ℝ := 1/Real.sqrt ((p:ℝ)+(q:ℝ))
noncomputable def pathForward (a b d : ℕ) : ℝ :=
  ∑ i : Fin b, ∑ j : Fin b,
    if i.val+1=j.val then edgeWeight s((path i : Vertex a b d),path j) else 0

theorem kernel_symm (p q : ℕ) : kernel p q = kernel q p := by
  unfold kernel; rw [add_comm]

theorem clique_block (a : ℕ) (z : ℝ) :
    (∑ u : Fin a, ∑ v : Fin a, if u≠v then z else 0) =
      (a:ℝ)*(a-1:ℕ)*z := by
  classical
  have hi (u : Fin a) :
      (∑ v : Fin a, if u≠v then z else 0) = ((a-1:ℕ):ℝ)*z := by
    have hr : (∑ v : Fin a, if u=v then (0:ℝ) else 1) = (a-1:ℕ) := by
      exact_mod_cast clique_sum a u
    calc
      _ = ∑ v : Fin a, (if u=v then (0:ℝ) else 1)*z := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : u=v <;> simp [h]
      _ = (∑ v : Fin a, if u=v then (0:ℝ) else 1)*z := (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [hr]
  simp_rw [hi]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul]
  ring

theorem path_block (a b d : ℕ) :
    (∑ i : Fin b, ∑ j : Fin b,
      if i.val+1=j.val ∨ j.val+1=i.val then edgeWeight s((path i : Vertex a b d),path j) else 0) =
      2*pathForward a b d := by
  classical
  have he (i j : Fin b) :
      (if i.val+1=j.val ∨ j.val+1=i.val then edgeWeight s((path i : Vertex a b d),path j) else 0) =
      (if i.val+1=j.val then edgeWeight s((path i : Vertex a b d),path j) else 0)+
      (if j.val+1=i.val then edgeWeight s((path i : Vertex a b d),path j) else 0) := by
    split_ifs <;> (try omega) <;> ring
  simp_rw [he,Finset.sum_add_distrib]
  have hs : (∑ i : Fin b, ∑ j : Fin b,
      if j.val+1=i.val then edgeWeight s((path i : Vertex a b d),path j) else 0) = pathForward a b d := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [edgeWeight_formula,add_comm]
  rw [hs]
  change pathForward a b d + pathForward a b d = _
  ring

#print axioms clique_block
#print axioms path_block
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END FiveSums@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN ActualFive 2785 2f425d2f4bb4968a98c3fedb4af3124874c1f7cbe0deb1ec25afd0bef64863d7@@
import FiveSums
namespace SumBalaban
open scoped BigOperators

theorem weight_as_kernel {a b d : ℕ} (u v : Vertex a b d) :
    edgeWeight s(u,v) = kernel (transmission u) (transmission v) := rfl

theorem five_sum_identity {a b d : ℕ} (hb : 0<b) :
    (∑ e ∈ (graph a b d).edgeFinset, edgeWeight e) =
      (a:ℝ)*(a-1:ℕ)/2*kernel (leftW a b d) (leftW a b d) +
      (a:ℝ)*kernel (leftW a b d) (transmission (path ⟨0,hb⟩ : Vertex a b d)) +
      pathForward a b d +
      (d:ℝ)*kernel (rightW a b d) (transmission (path ⟨b-1,by omega⟩ : Vertex a b d)) +
      (d:ℝ)*(d-1:ℕ)/2*kernel (rightW a b d) (rightW a b d) := by
  classical
  have hl (u : Fin a) : transmission (left u : Vertex a b d) = leftW a b d := left_transmission_sum hb u
  have hr (u : Fin d) : transmission (right u : Vertex a b d) = rightW a b d := right_transmission_sum hb u
  have hzero (i : Fin b) : i.val=0 ↔ i=⟨0,hb⟩ := by
    constructor
    · exact fun h => Fin.ext h
    · intro h; subst i; rfl
  have hlast (i : Fin b) : i.val+1=b ↔ i=⟨b-1,by omega⟩ := by
    constructor
    · intro h; apply Fin.ext; dsimp only; omega
    · intro h; subst i; dsimp only; omega
  have hp : (∑ i : Fin b, ∑ j : Fin b,
      if i.val+1=j.val ∨ j.val+1=i.val then
        kernel (transmission (path i : Vertex a b d)) (transmission (path j : Vertex a b d)) else 0) =
      2*pathForward a b d := by
    simpa only [weight_as_kernel] using path_block a b d
  have hpoint (i j : Fin b) :
      (if (graph a b d).Adj (path i) (path j) then edgeWeight s((path i : Vertex a b d),path j) else 0) =
      (if i.val+1=j.val ∨ j.val+1=i.val then edgeWeight s((path i : Vertex a b d),path j) else 0) := by
    by_cases h : i.val+1=j.val ∨ j.val+1=i.val
    · have ha : (graph a b d).Adj (path i) (path j) := h
      simp only [ha,h,ite_true]
    · have ha : ¬(graph a b d).Adj (path i) (path j) := h
      simp only [ha,h,ite_false]
  have ht := (ordered_sum_eq_dart_sum a b d).trans (dart_sum_eq_twice_edge_sum a b d)
  simp only [Fintype.sum_sum_type,Finset.sum_add_distrib] at ht
  simp_rw [hpoint] at ht
  simp only [graph,Adj,weight_as_kernel] at ht
  simp only [hl,hr,hzero,hlast,ite_false,Finset.sum_const_zero,add_zero,zero_add] at ht
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at ht
  rw [clique_block,clique_block] at ht
  simp only [path] at hp
  simp only [hp, ←Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at ht
  simp only [kernel_symm (transmission (path ⟨0,hb⟩ : Vertex a b d)),
    kernel_symm (transmission (path ⟨b-1,by omega⟩ : Vertex a b d))] at ht
  simp only [path,graph] at ht ⊢
  nlinarith [hp]

#print axioms five_sum_identity
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END ActualFive@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN PathEdges 1886 fcf2e3065c9f79af335c57ea77bebecaebd2aefaf282573909d441a1a9a5352a@@
import ActualFive
namespace SumBalaban
open scoped BigOperators

def pathLo {b : ℕ} (i : Fin (b-1)) : Fin b := ⟨i.val,by have := i.isLt; omega⟩
def pathHi {b : ℕ} (i : Fin (b-1)) : Fin b := ⟨i.val+1,by have := i.isLt; omega⟩

theorem pathForward_single (a b d : ℕ) :
    pathForward a b d = ∑ i : Fin (b-1), edgeWeight s((path (pathLo i) : Vertex a b d),path (pathHi i)) := by
  classical
  let f : Fin b × Fin b → ℝ := fun z => edgeWeight s((path z.1 : Vertex a b d),path z.2)
  have he : (∑ i : Fin (b-1), edgeWeight s((path (pathLo i) : Vertex a b d),path (pathHi i))) =
      ∑ z ∈ (Finset.univ : Finset (Fin b × Fin b)).filter (fun z => z.1.val+1=z.2.val), f z := by
    apply Finset.sum_bij (fun i _ => (pathLo i,pathHi i))
    · intro i _; simp [pathLo,pathHi]
    · intro i _ j _ h
      apply Fin.ext
      exact congrArg (fun z : Fin b × Fin b => z.1.val) h
    · intro z hz
      have hh := (Finset.mem_filter.mp hz).2
      have hi : z.1.val<b-1 := by have := z.2.isLt; omega
      refine ⟨⟨z.1.val,hi⟩,Finset.mem_univ _,?_⟩
      apply Prod.ext
      · apply Fin.ext; rfl
      · apply Fin.ext; exact hh
    · intro i _; rfl
  rw [he,Finset.sum_filter]
  exact (Fintype.sum_prod_type (fun z : Fin b × Fin b =>
    if z.1.val+1=z.2.val then f z else 0)).symm

theorem actual_path_edge_polynomial {a b d : ℕ} (hb : 0<b) (i : Fin (b-1)) :
    ((transmission (path (pathLo i) : Vertex a b d):ℝ) +
      (transmission (path (pathHi i) : Vertex a b d):ℝ)) =
      2*((i.val+a:ℕ):ℝ)^2 - 2*((a+b+d:ℕ)-2:ℝ)*((i.val+a:ℕ):ℝ) +
      ((a+b+d:ℕ):ℝ)^2-2*((a+b+d:ℕ):ℝ)+2 -
      ((a:ℝ)^2+(d:ℝ)^2-a-d) := by
  rw [shifted_actual_transmission hb,shifted_actual_transmission hb]
  simp only [pathLo,pathHi]
  push_cast
  ring

#print axioms pathForward_single
#print axioms actual_path_edge_polynomial
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END PathEdges@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN PathError 1695 c496c3b417149271ce02ee6b0f6c5ec35a840ce65312ab46000d1e22bbb446a3@@
import PathEdges
namespace SumBalaban

theorem actual_path_pair_error {a b d : ℕ} {B : ℝ} (hb : 0<b) (hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2 ≤ B*(a+b+d : ℕ)) (i : Fin (b-1)) :
    |((transmission (path (pathLo i) : Vertex a b d):ℝ) +
      (transmission (path (pathHi i) : Vertex a b d):ℝ)) -
      (((i.val+a:ℕ):ℝ)^2 + (((a+b+d:ℕ):ℝ)-((i.val+a:ℕ):ℝ))^2)| ≤
      (B+5)*(a+b+d : ℕ) := by
  rw [actual_path_edge_polynomial hb]
  have hn : (1:ℝ)≤(a+b+d : ℕ) := by exact_mod_cast (show 1≤a+b+d by omega)
  have ht : ((i.val+a:ℕ):ℝ) ≤ (a+b+d : ℕ) := by
    exact_mod_cast (show i.val+a≤a+b+d by have := i.isLt; omega)
  have ht0 : (0:ℝ)≤((i.val+a:ℕ):ℝ) := by positivity
  have hs : (a:ℝ)+(d:ℝ) ≤ (a+b+d : ℕ) := by push_cast; linarith
  have hBn : (0:ℝ)≤B*(a+b+d : ℕ) := mul_nonneg hB (by positivity)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem path_reference_lower (n t : ℝ) : n^2/2 ≤ t^2+(n-t)^2 := by
  nlinarith [sq_nonneg (2*t-n)]

theorem actual_path_pair_lower {a b d : ℕ} {B : ℝ} (hb : 0<b) (hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2 ≤ B*(a+b+d : ℕ))
    (hn : 4*(B+5)≤((a+b+d:ℕ):ℝ)) (i : Fin (b-1)) :
    ((a+b+d:ℕ):ℝ)^2/4 ≤
      ((transmission (path (pathLo i) : Vertex a b d):ℝ) +
      (transmission (path (pathHi i) : Vertex a b d):ℝ)) := by
  have he := (abs_le.mp (actual_path_pair_error hb hB hq i)).1
  have hf := path_reference_lower (((a+b+d:ℕ):ℝ)) (((i.val+a:ℕ):ℝ))
  have hm := mul_le_mul_of_nonneg_right hn (show (0:ℝ)≤((a+b+d:ℕ):ℝ) by positivity)
  nlinarith

#print axioms actual_path_pair_error
#print axioms actual_path_pair_lower
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END PathError@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN PathKernel 2557 b733c8f71dab346ff8de7beb8adb417fc80ff7ec06aeff1dd46f32bf8b14ff6a@@
import PathError
namespace SumBalaban

theorem inverse_sqrt_error {A T n H : ℝ} (hn : 0<n) (hH : 0≤H)
    (hA : n^2/4≤A) (hT : n^2/4≤T) (herr : |A-T|≤H*n) :
    |1/Real.sqrt A - 1/Real.sqrt T| ≤ 4*H/n^2 := by
  have hA0 : 0<A := by nlinarith [sq_pos_of_pos hn]
  have hT0 : 0<T := by nlinarith [sq_pos_of_pos hn]
  have hu0 := Real.sqrt_pos.mpr hA0
  have hv0 := Real.sqrt_pos.mpr hT0
  have hu2 := Real.sq_sqrt (le_of_lt hA0)
  have hv2 := Real.sq_sqrt (le_of_lt hT0)
  have hu : n/2≤Real.sqrt A := by nlinarith [Real.sqrt_nonneg A]
  have hv : n/2≤Real.sqrt T := by nlinarith [Real.sqrt_nonneg T]
  have hprod : n^2/4≤Real.sqrt A*Real.sqrt T := by
    have h := mul_le_mul hu hv (by linarith : 0≤n/2) (le_of_lt hu0)
    nlinarith
  have hden : n^3/4 ≤ Real.sqrt A*Real.sqrt T*(Real.sqrt A+Real.sqrt T) := by
    have h := mul_le_mul hprod (show n≤Real.sqrt A+Real.sqrt T by linarith)
      (le_of_lt hn) (mul_nonneg (le_of_lt hu0) (le_of_lt hv0))
    nlinarith
  have hid : (1/Real.sqrt A - 1/Real.sqrt T)*
      (Real.sqrt A*Real.sqrt T*(Real.sqrt A+Real.sqrt T)) = T-A := by
    field_simp
    nlinarith
  have heq : |1/Real.sqrt A - 1/Real.sqrt T| =
      |A-T|/(Real.sqrt A*Real.sqrt T*(Real.sqrt A+Real.sqrt T)) := by
    apply (eq_div_iff (ne_of_gt (mul_pos (mul_pos hu0 hv0) (add_pos hu0 hv0)))).mpr
    have ha := congrArg abs hid
    simpa only [abs_mul, abs_of_pos (mul_pos (mul_pos hu0 hv0) (add_pos hu0 hv0)), abs_sub_comm] using ha
  rw [heq]
  calc
    _ ≤ (H*n)/(Real.sqrt A*Real.sqrt T*(Real.sqrt A+Real.sqrt T)) :=
      div_le_div_of_nonneg_right herr (by positivity)
    _ ≤ (H*n)/(n^3/4) := div_le_div_of_nonneg_left (mul_nonneg hH (le_of_lt hn)) (by positivity) hden
    _ = 4*H/n^2 := by field_simp

theorem actual_path_kernel_error {a b d : ℕ} {B : ℝ} (hb : 0<b) (hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2 ≤ B*(a+b+d : ℕ))
    (hn : 4*(B+5)≤((a+b+d:ℕ):ℝ)) (i : Fin (b-1)) :
    |edgeWeight s((path (pathLo i) : Vertex a b d),path (pathHi i)) -
      1/Real.sqrt (((i.val+a:ℕ):ℝ)^2 + (((a+b+d:ℕ):ℝ)-((i.val+a:ℕ):ℝ))^2)| ≤
      4*(B+5)/((a+b+d:ℕ):ℝ)^2 := by
  rw [edgeWeight_formula]
  apply inverse_sqrt_error (n:=((a+b+d:ℕ):ℝ)) (H:=B+5)
  · exact_mod_cast (show 0<a+b+d by omega)
  · linarith
  · exact actual_path_pair_lower hb hB hq hn i
  · have h := path_reference_lower (((a+b+d:ℕ):ℝ)) (((i.val+a:ℕ):ℝ))
    nlinarith [sq_nonneg (((a+b+d:ℕ):ℝ))]
  · exact actual_path_pair_error hb hB hq i

#print axioms actual_path_kernel_error
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END PathKernel@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN PathSumError 1663 61d0029664e2e0b99843888be1643cf62b560bb38b0e438439dfa81547e23a58@@
import PathKernel
namespace SumBalaban
open scoped BigOperators

theorem actual_path_sum_error {a b d : ℕ} {B : ℝ} (hb : 0<b) (hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2 ≤ B*(a+b+d : ℕ))
    (hn : 4*(B+5)≤((a+b+d:ℕ):ℝ)) :
    |pathForward a b d -
      ∑ i : Fin (b-1), 1/Real.sqrt (((i.val+a:ℕ):ℝ)^2 +
        (((a+b+d:ℕ):ℝ)-((i.val+a:ℕ):ℝ))^2)| ≤ 4*(B+5)/((a+b+d:ℕ):ℝ) := by
  rw [pathForward_single,←Finset.sum_sub_distrib]
  have hpos : (0:ℝ)<((a+b+d:ℕ):ℝ) := by exact_mod_cast (show 0<a+b+d by omega)
  have hcard : ((b-1:ℕ):ℝ)≤((a+b+d:ℕ):ℝ) := by exact_mod_cast (show b-1≤a+b+d by omega)
  calc
    _ ≤ ∑ i : Fin (b-1), |edgeWeight s((path (pathLo i) : Vertex a b d),path (pathHi i)) -
        1/Real.sqrt (((i.val+a:ℕ):ℝ)^2 + (((a+b+d:ℕ):ℝ)-((i.val+a:ℕ):ℝ))^2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (b-1), 4*(B+5)/((a+b+d:ℕ):ℝ)^2 :=
      Finset.sum_le_sum (fun i _ => actual_path_kernel_error hb hB hq hn i)
    _ = ((b-1:ℕ):ℝ)*(4*(B+5)/((a+b+d:ℕ):ℝ)^2) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ ≤ ((a+b+d:ℕ):ℝ)*(4*(B+5)/((a+b+d:ℕ):ℝ)^2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

theorem reference_scaled (n t : ℝ) (hn : 0<n) :
    1/Real.sqrt (t^2+(n-t)^2) = (1/n)*(1/Real.sqrt ((t/n)^2+(1-t/n)^2)) := by
  have hp : t^2+(n-t)^2 = n^2*((t/n)^2+(1-t/n)^2) := by field_simp
  rw [hp,Real.sqrt_mul (sq_nonneg n),Real.sqrt_sq_eq_abs,abs_of_pos hn]
  field_simp

#print axioms actual_path_sum_error
#print axioms reference_scaled
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END PathSumError@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN ReferenceIntegral 2484 ae71e85bae8b31177fc83caf246252c32e4c93e45b79bd4b37e0bc18c8f30785@@
import PathKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
namespace SumBalaban
noncomputable def referenceF (u : ℝ) : ℝ := 1/Real.sqrt (u^2+(1-u)^2)
theorem reference_phi_lower (u : ℝ) : (1:ℝ)/2≤u^2+(1-u)^2 := by
  nlinarith [sq_nonneg (u-1/2)]
theorem referenceF_continuous : Continuous referenceF := by
  apply Continuous.div continuous_const
    (((continuous_id.pow 2).add ((continuous_const.sub continuous_id).pow 2)).sqrt)
  intro u
  change Real.sqrt (u^2+(1-u)^2)≠0
  exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [reference_phi_lower u]))
theorem referenceF_lipschitz {u v : ℝ} (hu : 0≤u) (hu1 : u≤1)
    (hv : 0≤v) (hv1 : v≤1) :
    |referenceF u-referenceF v|≤8*|u-v| := by
  have hsum : |u+v-1|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have he : |(u^2+(1-u)^2)-(v^2+(1-v)^2)|≤2*|u-v| := by
    rw [show (u^2+(1-u)^2)-(v^2+(1-v)^2)=2*(u-v)*(u+v-1) by ring,
      abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg (u-v))]
  have h := inverse_sqrt_error (A:=u^2+(1-u)^2) (T:=v^2+(1-v)^2) (n:=1) (H:=2*|u-v|) (by norm_num)
    (by positivity) (by linarith [reference_phi_lower u])
    (by linarith [reference_phi_lower v]) (by simpa using he)
  dsimp [referenceF]
  simpa only [one_pow, div_one, show (4:ℝ)*(2*|u-v|)=8*|u-v| by ring] using h

theorem reference_cell_error {h t : ℝ} (hh : 0≤h) (ht : 0≤t) (hht : h+t≤1) :
    |(∫ u in h..h+t, referenceF u)-t*referenceF h|≤8*t^2 := by
  have hint : IntervalIntegrable referenceF MeasureTheory.volume h (h+t) :=
    referenceF_continuous.intervalIntegrable h (h+t)
  have hc : IntervalIntegrable (fun _ : ℝ => referenceF h) MeasureTheory.volume h (h+t) :=
    intervalIntegrable_const
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=h) (b:=h+t) (f:=fun u => referenceF u-referenceF h) (C:=8*t) ?_
  · rw [intervalIntegral.integral_sub hint hc] at he
    simpa [Real.norm_eq_abs, abs_of_nonneg ht, pow_two, mul_comm, mul_left_comm, mul_assoc] using he
  · intro u hu
    rw [Set.uIoc_of_le (by linarith : h≤h+t)] at hu
    have huu : h≤u := le_of_lt hu.1
    have hu1 : u≤1 := le_trans hu.2 hht
    rw [Real.norm_eq_abs]
    have he := referenceF_lipschitz (by linarith : 0≤u) hu1 hh (by linarith : h≤1)
    rw [abs_of_nonneg (sub_nonneg.mpr huu)] at he
    linarith [hu.2]
#print axioms referenceF_lipschitz
#print axioms reference_cell_error
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END ReferenceIntegral@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN ReferenceRectangle 1600 2e69bc73ed7efa2f08e381f66697ccf644aff88962513639714f31e056cb3671@@
import ReferenceIntegral
namespace SumBalaban
open scoped BigOperators
theorem reference_rectangle_error (h t : ℝ) (N : ℕ)
    (hh : 0≤h) (ht : 0≤t) (hN : h+(N:ℝ)*t≤1) :
    |(∑ i ∈ Finset.range N, t*referenceF (h+(i:ℝ)*t))-
      (∫ u in h..h+(N:ℝ)*t, referenceF u)|≤8*(N:ℝ)*t^2 := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a:=fun i : ℕ => h+(i:ℝ)*t) (n:=N)
    (f:=referenceF) (μ:=MeasureTheory.volume)
    (fun k _ => referenceF_continuous.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_mul, add_zero] at hs
  have hi : ∀ i ∈ Finset.range N,
      |t*referenceF (h+(i:ℝ)*t)-
        (∫ u in h+(i:ℝ)*t..h+((i+1:ℕ):ℝ)*t, referenceF u)|≤8*t^2 := by
    intro i hi
    have hiN : ((i+1:ℕ):ℝ)≤N := by exact_mod_cast (Finset.mem_range.mp hi)
    have he := reference_cell_error (h:=h+(i:ℝ)*t) (t:=t)
      (by positivity) ht (by
        have := mul_le_mul_of_nonneg_right hiN ht
        push_cast at *
        linarith)
    rw [abs_sub_comm]
    convert he using 1; push_cast; congr 2; ring
  calc
    _ = |∑ i ∈ Finset.range N,
        (t*referenceF (h+(i:ℝ)*t)-
        (∫ u in h+(i:ℝ)*t..h+((i+1:ℕ):ℝ)*t, referenceF u))| := by
      rw [Finset.sum_sub_distrib, hs]
    _ ≤ ∑ i ∈ Finset.range N,
        |t*referenceF (h+(i:ℝ)*t)-
        (∫ u in h+(i:ℝ)*t..h+((i+1:ℕ):ℝ)*t, referenceF u)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, 8*t^2 := Finset.sum_le_sum hi
    _ = _ := by simp; ring
#print axioms reference_rectangle_error
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END ReferenceRectangle@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN ReferenceValue 1526 47f62acdff03035108ccd890d242c9cc759f27ae964d6850f23a66b9f87f3f19@@
import ReferenceIntegral
import IndexTarget
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
namespace SumBalaban
theorem reference_primitive_derivative (u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sqrt 2/2*Real.arsinh (2*x-1))
      (referenceF u) u := by
  have hd := ((Real.hasDerivAt_arsinh (2*u-1)).comp u
    (((hasDerivAt_id u).const_mul 2).sub_const 1)).const_mul (Real.sqrt 2/2)
  have hs : Real.sqrt (1+(2*u-1)^2) =
      Real.sqrt 2*Real.sqrt (u^2+(1-u)^2) := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  have hp : 0<Real.sqrt (u^2+(1-u)^2) :=
    Real.sqrt_pos.mpr (by linarith [reference_phi_lower u])
  have h2 : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have he : referenceF u = Real.sqrt 2/2*((Real.sqrt (1+(2*u-1)^2))⁻¹*(2*1)) := by
    dsimp [referenceF]
    rw [hs]
    field_simp

  rw [he]
  exact hd

theorem reference_integral_value : (∫ u in (0:ℝ)..1, referenceF u)=Q := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=0) (b:=1)
    (fun u _ => reference_primitive_derivative u)
    (referenceF_continuous.intervalIntegrable 0 1)
  have hn : Real.arsinh (-1) = -Real.arsinh 1 := Real.arsinh_neg 1
  norm_num only [mul_one, mul_zero, sub_zero, zero_sub] at hi
  rw [hn] at hi
  rw [hi]
  simp only [Real.arsinh, one_pow, one_add_one_eq_two, Q]
  ring
#print axioms reference_primitive_derivative
#print axioms reference_integral_value
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END ReferenceValue@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN TransmissionLower 2627 285e5898bc9fa712aad1d06d2df18042f979e66cb46146065b05f8dfec091a65@@
import PathSumError
namespace SumBalaban

theorem transmission_ge_path_sq {a b d : ℕ} (hb : 2≤b) (u : Vertex a b d) :
    (b:ℝ)^2/8 ≤ (transmission u : ℝ) := by
  have hb0 : 0<b := by omega
  have hb' : (2:ℝ)≤b := by exact_mod_cast hb
  rcases u with u | u
  · have h := twice_left_transmission (a:=a) (d:=d) hb0 u
    have hr : (2:ℝ)*transmission (left u : Vertex a b d) =
        2*(a-1:ℕ)+(b:ℝ)*(b+1)+2*d*(b+1) := by exact_mod_cast h
    have hm : (0:ℝ)≤(d:ℝ)*(b+1) := by positivity
    have hz : (0:ℝ)≤(a-1:ℕ) := by positivity
    nlinarith
  · rcases u with i | u
    · have h := twice_path_transmission (a:=a) (d:=d) hb0 i
      have hr : (2:ℝ)*transmission (path i : Vertex a b d) =
        (i.val:ℝ)*(i.val+1)+(b-1-i.val:ℕ)*(b-i.val:ℕ)+
        2*a*(i.val+1)+2*d*(b-i.val:ℕ) := by exact_mod_cast h
      have h1 : ((b-i.val:ℕ):ℝ)=(b:ℝ)-i.val := by rw [Nat.cast_sub (by have := i.isLt; omega)]
      have h2 : ((b-1-i.val:ℕ):ℝ)=(b:ℝ)-1-i.val := by
        rw [Nat.cast_sub (by have := i.isLt; omega),Nat.cast_sub (by omega : 1≤b)]
        norm_num
      rw [h1,h2] at hr
      have hm : (0:ℝ)≤(d:ℝ)*((b:ℝ)-i.val) := by
        have hi : (i.val:ℝ)≤b := by exact_mod_cast (show i.val≤b by have := i.isLt; omega)
        exact mul_nonneg (by positivity) (by linarith)
      have hm' : (0:ℝ)≤(a:ℝ)*((i.val:ℝ)+1) := by positivity
      nlinarith [sq_nonneg (2*(i.val:ℝ)-((b:ℝ)-1))]
    · have h := twice_right_transmission (a:=a) (d:=d) hb0 u
      have hr : (2:ℝ)*transmission (right u : Vertex a b d) =
          2*(d-1:ℕ)+(b:ℝ)*(b+1)+2*a*(b+1) := by exact_mod_cast h
      have hm : (0:ℝ)≤(a:ℝ)*(b+1) := by positivity
      have hz : (0:ℝ)≤(d-1:ℕ) := by positivity
      nlinarith

theorem edgeWeight_upper {a b d : ℕ} (hb : 2≤b) (e : Sym2 (Vertex a b d)) :
    edgeWeight e ≤ 2/(b:ℝ) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    have hu := transmission_ge_path_sq hb u
    have hv := transmission_ge_path_sq hb v
    have hb' : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
    have hs := Real.sq_sqrt (show (0:ℝ)≤(transmission u : ℝ)+(transmission v : ℝ) by positivity)
    have hlow : (b:ℝ)/2≤Real.sqrt ((transmission u : ℝ)+(transmission v : ℝ)) := by
      nlinarith [Real.sqrt_nonneg ((transmission u : ℝ)+(transmission v : ℝ))]
    rw [edgeWeight_formula]
    have h := one_div_le_one_div_of_le (show (0:ℝ)<(b:ℝ)/2 by positivity) hlow
    convert h using 1; field_simp

#print axioms transmission_ge_path_sq
#print axioms edgeWeight_upper
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END TransmissionLower@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN MovingInterval 2574 2a5f1af2b343d44d5f9a686c37fcc5f82eb2dce56f5081342b87adc4bd11f881@@
import ReferenceRectangle
import ReferenceValue
namespace SumBalaban
@[simp] theorem referenceF_zero : referenceF 0=1 := by norm_num [referenceF]
@[simp] theorem referenceF_one : referenceF 1=1 := by norm_num [referenceF]

theorem reference_left_end_error {h : ℝ} (hh : 0≤h) (hh1 : h≤1) :
    |(∫ u in (0:ℝ)..h, referenceF u)-h|≤8*h^2 := by
  simpa using reference_cell_error (h:=0) (t:=h) (by norm_num) hh (by simpa using hh1)

theorem reference_right_end_error {r : ℝ} (hr : 0≤r) (hr1 : r≤1) :
    |(∫ u in 1-r..(1:ℝ), referenceF u)-r|≤8*r^2 := by
  have hint : IntervalIntegrable referenceF MeasureTheory.volume (1-r) 1 :=
    referenceF_continuous.intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume (1-r) 1 :=
    intervalIntegrable_const
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=1-r) (b:=1) (f:=fun u => referenceF u-1) (C:=8*r) ?_
  · rw [intervalIntegral.integral_sub hint hc] at he
    simpa [Real.norm_eq_abs,abs_of_nonneg hr,pow_two,mul_assoc] using he
  · intro u hu
    rw [Set.uIoc_of_le (by linarith : 1-r≤1)] at hu
    rw [Real.norm_eq_abs]
    have hh := referenceF_lipschitz (by linarith [hu.1] : 0≤u) hu.2
      (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤1)
    rw [referenceF_one, abs_of_nonpos (by linarith [hu.2] : u-1≤0)] at hh
    linarith [hu.1]

theorem reference_moving_interval {h r : ℝ} (hh : 0≤h) (hr : 0≤r)
    (hhr : h+r≤1) :
    |(∫ u in h..1-r, referenceF u)-(Q-h-r)|≤8*(h^2+r^2) := by
  have hl := reference_left_end_error hh (by linarith : h≤1)
  have hr' := reference_right_end_error hr (by linarith : r≤1)
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (referenceF_continuous.intervalIntegrable (μ:=MeasureTheory.volume) 0 h)
    (referenceF_continuous.intervalIntegrable (μ:=MeasureTheory.volume) h (1-r))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (referenceF_continuous.intervalIntegrable (μ:=MeasureTheory.volume) 0 (1-r))
    (referenceF_continuous.intervalIntegrable (μ:=MeasureTheory.volume) (1-r) 1)
  rw [reference_integral_value] at h2
  have he : (∫ u in h..1-r, referenceF u)-(Q-h-r) =
      -((∫ u in (0:ℝ)..h, referenceF u)-h)-
      ((∫ u in 1-r..(1:ℝ), referenceF u)-r) := by linarith
  rw [he]
  have hab := abs_sub_le (-((∫ u in (0:ℝ)..h, referenceF u)-h)) 0
    ((∫ u in 1-r..(1:ℝ), referenceF u)-r)
  simp only [sub_zero, zero_sub, abs_neg] at hab
  nlinarith
#print axioms reference_moving_interval
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END MovingInterval@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN TrialBound 2807 80882cc09154f5b8316f1bc22b3df53967ee7f36b8ce52099c939bdc2ad3a36e@@
import TransmissionLower
namespace SumBalaban
open scoped BigOperators

theorem SJ_nonneg (a b d : ℕ) (hb : 0<b) : 0≤SJ a b d := by
  classical
  have hw (e : Sym2 (Vertex a b d)) : 0≤edgeWeight e := by
    induction e using Sym2.inductionOn with
    | _ u v => rw [edgeWeight_formula]; positivity
  unfold SJ
  exact mul_nonneg (div_nonneg (by positivity) (le_of_lt (cycle_denominator_pos hb)))
    (Finset.sum_nonneg (fun e _ => hw e))

theorem SJ_upper_of_path {a b d : ℕ} (hb : 2≤b) :
    SJ a b d ≤ 2*(edgeCount a b d : ℝ)^2 /
      ((b:ℝ)*((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2)) := by
  classical
  have hb0 : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hk := cycle_denominator_pos (a:=a) (d:=d) (show 0<b by omega)
  have hs : (∑ e ∈ (graph a b d).edgeFinset, edgeWeight e) ≤ (edgeCount a b d : ℝ)*(2/(b:ℝ)) := by
    calc
      _ ≤ ∑ _e ∈ (graph a b d).edgeFinset, (2/(b:ℝ)) :=
        Finset.sum_le_sum (fun e _ => edgeWeight_upper hb e)
      _ = _ := by simp only [Finset.sum_const,edgeCount, nsmul_eq_mul]
  have hm : (0:ℝ)≤(edgeCount a b d : ℝ)/((edgeCount a b d : ℝ)-(a+b+d : ℕ)+2) := by positivity
  have h := mul_le_mul_of_nonneg_left hs hm
  change SJ a b d ≤ _ at h
  convert h using 1; field_simp

theorem balanced_trial_bound {k b : ℕ} (hk : 2≤k) (hb : 2≤b)
    (hsq : (k:ℝ)^2≤((k+b+k:ℕ):ℝ))
    (hsq' : ((k+b+k:ℕ):ℝ)≤4*(k:ℝ)^2)
    (hpath : ((k+b+k:ℕ):ℝ)/2≤b) : SJ k b k ≤ 128 := by
  have hkpos := cycle_denominator_pos (a:=k) (d:=k) (show 0<b by omega)
  have hpos : (0:ℝ)<(k+b+k : ℕ) := by exact_mod_cast (show 0<k+b+k by omega)
  have he := real_edge_count_formula (a:=k) (d:=k) (show 0<b by omega)
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  have hm : (edgeCount k b k : ℝ) ≤ 2*(k+b+k : ℕ) := by nlinarith
  have hm0 : (0:ℝ)≤(edgeCount k b k : ℝ) := by positivity
  have hcycle : ((k+b+k:ℕ):ℝ)/8 ≤ (edgeCount k b k : ℝ)-(k+b+k : ℕ)+2 := by nlinarith [sq_nonneg ((k:ℝ)-1)]
  have hden : ((k+b+k:ℕ):ℝ)^2/16 ≤ (b:ℝ)*((edgeCount k b k : ℝ)-(k+b+k : ℕ)+2) := by
    have h := mul_le_mul hpath hcycle (show (0:ℝ)≤((k+b+k:ℕ):ℝ)/8 by positivity) (show (0:ℝ)≤b by positivity)
    nlinarith
  calc
    _ ≤ 2*(edgeCount k b k : ℝ)^2 / ((b:ℝ)*((edgeCount k b k : ℝ)-(k+b+k : ℕ)+2)) := SJ_upper_of_path hb
    _ ≤ (8*((k+b+k:ℕ):ℝ)^2) / ((b:ℝ)*((edgeCount k b k : ℝ)-(k+b+k : ℕ)+2)) := by
      apply div_le_div_of_nonneg_right
      · nlinarith
      · positivity
    _ ≤ (8*((k+b+k:ℕ):ℝ)^2) / (((k+b+k:ℕ):ℝ)^2/16) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 128 := by field_simp; norm_num

#print axioms SJ_upper_of_path
#print axioms balanced_trial_bound
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END TrialBound@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN ActualRectangle 2193 99a8f107d33383e1738fdda9d66af8d5f9a2d7b121b34a964760d971d60f2527@@
import MovingInterval
import PathSumError
namespace SumBalaban
open scoped BigOperators

theorem actual_reference_rectangle {a b d : ℕ} {B : ℝ}
    (hb : 0<b) (hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ))
    (hn : 4*(B+5)≤((a+b+d:ℕ):ℝ)) :
    let n : ℝ := (a+b+d:ℕ)
    |pathForward a b d -
      (∫ u in (a:ℝ)/n..(a:ℝ)/n+(b-1:ℕ)/n, referenceF u)|≤
      (4*(B+5)+8)/n := by
  dsimp only
  let n : ℝ := (a+b+d:ℕ)
  have hn0 : 0<n := by dsimp [n]; exact_mod_cast (show 0<a+b+d by omega)
  have hn1 : (b-1:ℕ)≤a+b+d := by omega
  have hn1' : ((b-1:ℕ):ℝ)≤n := by dsimp [n]; exact_mod_cast hn1
  have he := actual_path_sum_error hb hB hq hn
  have hr := reference_rectangle_error ((a:ℝ)/n) (1/n) (b-1)
    (by positivity) (by positivity) (by
      rw [mul_one_div, ←add_div, div_le_one hn0]
      dsimp [n]
      have h : a+(b-1)≤a+b+d := by omega
      exact_mod_cast h)
  have hs :
      (∑ i : Fin (b-1), 1/Real.sqrt (((i.val+a:ℕ):ℝ)^2+
        (n-((i.val+a:ℕ):ℝ))^2)) =
      ∑ i ∈ Finset.range (b-1), (1/n)*referenceF ((a:ℝ)/n+(i:ℝ)*(1/n)) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => 1/Real.sqrt (((i+a:ℕ):ℝ)^2+(n-((i+a:ℕ):ℝ))^2))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [reference_scaled n ((i+a:ℕ):ℝ) hn0]
    congr 1
    dsimp [referenceF]
    push_cast
    congr 3 <;> ring
  have hs' := hs
  change |pathForward a b d - _|≤4*(B+5)/n at he
  rw [hs] at he
  have hr' : |(∑ i ∈ Finset.range (b-1), (1/n)*referenceF ((a:ℝ)/n+(i:ℝ)*(1/n)))-
      (∫ u in (a:ℝ)/n..(a:ℝ)/n+(b-1:ℕ)/n, referenceF u)|≤8/n := by
    have hc : 8*((b-1:ℕ):ℝ)*(1/n)^2≤8/n := by
      apply (le_div_iff₀ hn0).mpr
      field_simp
      nlinarith
    simpa only [mul_one_div] using hr.trans hc
  have hh := abs_sub_le (pathForward a b d)
    (∑ i ∈ Finset.range (b-1), (1/n)*referenceF ((a:ℝ)/n+(i:ℝ)*(1/n)))
    (∫ u in (a:ℝ)/n..(a:ℝ)/n+(b-1:ℕ)/n, referenceF u)
  change |pathForward a b d - _|≤(4*(B+5)+8)/n
  calc
    _ ≤ _ := hh
    _ ≤ 4*(B+5)/n+8/n := add_le_add he hr'
    _ = _ := by ring
#print axioms actual_reference_rectangle
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END ActualRectangle@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN TrialExistence 2483 dc00ff2866e73c6543d96e122ca3dde0b98196c2bcb38fb18d0886fd278b9591@@
import TrialBound
import Mathlib.Data.Nat.Sqrt
namespace SumBalaban

def coarseTrial (n : ℕ) : Triple := (n.sqrt,n-2*n.sqrt,n.sqrt)

theorem coarseTrial_admissible {n : ℕ} (hn : 64≤n) : admissible n (coarseTrial n) := by
  have hk : 8≤n.sqrt := Nat.le_sqrt.mpr hn
  have hs := Nat.sqrt_le n
  have hh : 2*n.sqrt≤n := by nlinarith
  have hb : 0<n-2*n.sqrt := Nat.sub_pos_of_lt (by nlinarith)
  simp only [admissible,coarseTrial]
  omega

theorem coarseTrial_bound {n : ℕ} (hn : 64≤n) : objective (coarseTrial n) ≤ 128 := by
  have hk : 8≤n.sqrt := Nat.le_sqrt.mpr hn
  have hs := Nat.sqrt_le n
  have hfour : 4*n.sqrt≤n := by nlinarith
  have htot : n.sqrt+(n-2*n.sqrt)+n.sqrt=n := by omega
  have hreal : (n.sqrt:ℝ)^2≤(n:ℝ) := by exact_mod_cast (Nat.sqrt_le' n)
  have hreal' : (n:ℝ)<((n.sqrt:ℝ)+1)^2 := by
    have hh : n<(n.sqrt+1)^2 := by simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' n
    exact_mod_cast hh
  have hk' : (8:ℝ)≤n.sqrt := by exact_mod_cast hk
  have hb : 2≤n-2*n.sqrt := by omega
  have hp : (n:ℝ)/2≤(n-2*n.sqrt:ℕ) := by
    have hh : ((n-2*n.sqrt:ℕ):ℝ)=(n:ℝ)-2*n.sqrt := by
      rw [Nat.cast_sub (by omega : 2*n.sqrt≤n)]
      norm_num
    rw [hh]
    have hfour' : (4:ℝ)*n.sqrt≤n := by exact_mod_cast hfour
    linarith
  unfold objective coarseTrial
  apply balanced_trial_bound (by omega : 2≤n.sqrt) hb
  · rw [htot]; exact hreal
  · rw [htot]; nlinarith
  · rw [htot]; exact hp

theorem minimizer_bound {n : ℕ} {t : Triple} (hn : 64≤n) (ht : minimizes n t) :
    objective t ≤ 128 :=
  le_trans (ht.2 (coarseTrial n) (coarseTrial_admissible hn)) (coarseTrial_bound hn)

theorem every_minimizer_radial_bounds {n : ℕ} {t : Triple} (hn : 2048≤n)
    (ht : minimizes n t) :
    (t.1:ℝ)^2+(t.2.2:ℝ)^2 ≤ 512*n ∧
    (n:ℝ) ≤ 1024*((t.1:ℝ)^2+(t.2.2:ℝ)^2) := by
  obtain ⟨ha,hb,hd,htot,had⟩ := ht.1
  have hM : SJ t.1 t.2.1 t.2.2≤128 := minimizer_bound (by omega) ht
  constructor
  · have h := sublevel_clique_squares_upper hb (by omega) hM
    rw [htot] at h
    linarith
  · have h := sublevel_clique_squares_lower hb (by omega : 4≤t.1+t.2.1+t.2.2)
      (show 16*(128:ℝ)≤((t.1+t.2.1+t.2.2:ℕ):ℝ) by rw [htot]; exact_mod_cast hn)
      (by norm_num : (0:ℝ)≤128) hM
    rw [htot] at h
    norm_num at h ⊢
    exact h

#print axioms coarseTrial_admissible
#print axioms coarseTrial_bound
#print axioms every_minimizer_radial_bounds
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END TrialExistence@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN MinimizerAnnulus 1842 7a29e9451318c22c8faa439e428e7eaf46cfa996df614bc763c27f95065240ae@@
import TrialExistence
namespace SumBalaban

theorem normalized_squares (a d n : ℕ) (hn : 0<n) :
    ((a:ℝ)/Real.sqrt n)^2+((d:ℝ)/Real.sqrt n)^2 = ((a:ℝ)^2+(d:ℝ)^2)/(n:ℝ) := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤n by positivity)
  rw [div_pow,div_pow,hs]
  ring

theorem every_minimizer_annulus {n : ℕ} {t : Triple} (hn : 2048≤n)
    (ht : minimizes n t) :
    0≤(t.1:ℝ)/Real.sqrt n ∧ (t.1:ℝ)/Real.sqrt n≤32 ∧
    0≤(t.2.2:ℝ)/Real.sqrt n ∧ (t.2.2:ℝ)/Real.sqrt n≤32 ∧
    (1:ℝ)/1024 ≤ ((t.1:ℝ)/Real.sqrt n)^2+((t.2.2:ℝ)/Real.sqrt n)^2 ∧
    ((t.1:ℝ)/Real.sqrt n)^2+((t.2.2:ℝ)/Real.sqrt n)^2≤512 ∧
    (n:ℝ)-(t.2.1:ℝ)≤64*Real.sqrt n := by
  have hpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hspos := Real.sqrt_pos.mpr hpos
  have ⟨hup,hlo⟩ := every_minimizer_radial_bounds hn ht
  have hnorm := normalized_squares t.1 t.2.2 n (by omega)
  have hqup : ((t.1:ℝ)/Real.sqrt n)^2+((t.2.2:ℝ)/Real.sqrt n)^2≤512 := by
    rw [hnorm]
    exact (div_le_iff₀ hpos).mpr (by linarith)
  have hqlo : (1:ℝ)/1024 ≤ ((t.1:ℝ)/Real.sqrt n)^2+((t.2.2:ℝ)/Real.sqrt n)^2 := by
    rw [hnorm]
    exact (le_div_iff₀ hpos).mpr (by linarith)
  have hx : 0≤(t.1:ℝ)/Real.sqrt n := by positivity
  have hy : 0≤(t.2.2:ℝ)/Real.sqrt n := by positivity
  have hxup : (t.1:ℝ)/Real.sqrt n≤32 := by nlinarith [sq_nonneg ((t.2.2:ℝ)/Real.sqrt n)]
  have hyup : (t.2.2:ℝ)/Real.sqrt n≤32 := by nlinarith [sq_nonneg ((t.1:ℝ)/Real.sqrt n)]
  refine ⟨hx,hxup,hy,hyup,hqlo,hqup,?_⟩
  have ha := (div_le_iff₀ hspos).mp hxup
  have hd := (div_le_iff₀ hspos).mp hyup
  have htot : (t.1:ℝ)+(t.2.1:ℝ)+(t.2.2:ℝ)=n := by exact_mod_cast ht.1.2.2.2.1
  linarith

#print axioms normalized_squares
#print axioms every_minimizer_annulus
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END MinimizerAnnulus@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN PathFirstCorrection 2170 e233dc54f0bd499c847f55343e789636a8f142571de10d060be4f59deb7780e0@@
import ActualRectangle
namespace SumBalaban
theorem actual_path_first_correction {a b d : ℕ} {B : ℝ}
    (hb : 0<b) (hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ))
    (hn : 4*(B+5)≤((a+b+d:ℕ):ℝ)) :
    |pathForward a b d-(Q-((a:ℝ)+d)/(a+b+d:ℕ))|≤
      (20*B+45)/(a+b+d:ℕ) := by
  let n : ℝ := (a+b+d:ℕ)
  let h : ℝ := (a:ℝ)/n
  let r : ℝ := ((d:ℝ)+1)/n
  have hn0 : 0<n := by dsimp [n]; exact_mod_cast (show 0<a+b+d by omega)
  have hn1 : 1≤n := by change 1≤((a+b+d:ℕ):ℝ); nlinarith
  have hncast : n=(a:ℝ)+b+d := by dsimp [n]; push_cast; ring
  have hbm : ((b-1:ℕ):ℝ)=(b:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hhr : h+r≤1 := by
    dsimp [h,r]
    rw [←add_div, div_le_one hn0]
    have hb' : (1:ℝ)≤b := by exact_mod_cast hb
    linarith
  have hm := reference_moving_interval (h:=h) (r:=r) (by positivity) (by positivity) hhr
  have he := actual_reference_rectangle hb hB hq hn
  have hend : (a:ℝ)/n+((b-1:ℕ):ℝ)/n=1-r := by
    rw [hbm]
    dsimp [r]
    field_simp
    linarith
  change |pathForward a b d-(∫ u in h..(a:ℝ)/n+((b-1:ℕ):ℝ)/n, referenceF u)|≤
    (4*(B+5)+8)/n at he
  rw [hend] at he
  have hbound : 8*(h^2+r^2)≤(16*B+16)/n := by
    have hsq : (a:ℝ)^2+((d:ℝ)+1)^2≤2*B*n+2 := by
      change (a:ℝ)^2+(d:ℝ)^2≤B*n at hq
      nlinarith [sq_nonneg ((d:ℝ)-1),sq_nonneg (a:ℝ)]
    dsimp [h,r]
    apply (le_div_iff₀ hn0).mpr
    field_simp
    nlinarith
  have hdiff : (Q-h-r)-(Q-((a:ℝ)+d)/n) = -1/n := by dsimp [h,r]; ring
  have hh := abs_sub_le (pathForward a b d)
    (∫ u in h..1-r, referenceF u) (Q-h-r)
  have hp : |pathForward a b d-(Q-h-r)|≤(4*(B+5)+8)/n+(16*B+16)/n :=
    hh.trans (add_le_add he (hm.trans hbound))
  have hh' := abs_sub_le (pathForward a b d) (Q-h-r) (Q-((a:ℝ)+d)/n)
  have hneg : |(-1:ℝ)/n|=1/n := by rw [abs_div]; simp [abs_of_pos hn0]
  rw [hdiff,hneg] at hh'
  change |pathForward a b d-(Q-((a:ℝ)+d)/n)|≤(20*B+45)/n
  calc
    _ ≤ _ := hh'
    _ ≤ ((4*(B+5)+8)/n+(16*B+16)/n)+1/n := add_le_add hp le_rfl
    _ = _ := by ring
#print axioms actual_path_first_correction
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END PathFirstCorrection@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN CliquePolynomials 2234 ceec5d97c87ac437ae42f900af02b20c82da45704c6d3dcb173b17605eb738e9@@
import MinimizerAnnulus
namespace SumBalaban

theorem leftW_polynomial {a b d : ℕ} (ha : 0<a) (hb : 0<b) :
    2*(leftW a b d : ℝ) = ((a+b+d:ℕ):ℝ)^2-2*(a:ℝ)*(a+b+d:ℕ)+
      (a:ℝ)^2-(d:ℝ)^2+(a+b+d:ℕ)+a+d-2 := by
  let u : Fin a := ⟨0,ha⟩
  have h := twice_left_transmission (a:=a) (d:=d) hb u
  have hr : (2:ℝ)*transmission (left u : Vertex a b d) =
      2*(a-1:ℕ)+(b:ℝ)*(b+1)+2*d*(b+1) := by exact_mod_cast h
  rw [left_transmission_sum hb] at hr
  change 2*(leftW a b d : ℝ)=_ at hr
  have hsub : ((a-1:ℕ):ℝ)=(a:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤a)]; norm_num
  rw [hsub] at hr
  push_cast
  nlinarith

theorem rightW_polynomial {a b d : ℕ} (hd : 0<d) (hb : 0<b) :
    2*(rightW a b d : ℝ) = ((a+b+d:ℕ):ℝ)^2-2*(d:ℝ)*(a+b+d:ℕ)+
      (d:ℝ)^2-(a:ℝ)^2+(a+b+d:ℕ)+a+d-2 := by
  let u : Fin d := ⟨0,hd⟩
  have h := twice_right_transmission (a:=a) (d:=d) hb u
  have hr : (2:ℝ)*transmission (right u : Vertex a b d) =
      2*(d-1:ℕ)+(b:ℝ)*(b+1)+2*a*(b+1) := by exact_mod_cast h
  rw [right_transmission_sum hb] at hr
  change 2*(rightW a b d : ℝ)=_ at hr
  have hsub : ((d-1:ℕ):ℝ)=(d:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤d)]; norm_num
  rw [hsub] at hr
  push_cast
  nlinarith

theorem left_attachment_argument {a b d : ℕ} (ha : 0<a) (hb : 0<b) :
    (leftW a b d : ℝ)+(transmission (path ⟨0,hb⟩ : Vertex a b d):ℝ) =
      ((a+b+d:ℕ):ℝ)^2-2*(a:ℝ)*(a+b+d:ℕ)+(a:ℝ)^2-(d:ℝ)^2+2*a+d-1 := by
  have hl := leftW_polynomial (d:=d) ha hb
  rw [shifted_actual_transmission hb]
  push_cast at *
  nlinarith

theorem right_attachment_argument {a b d : ℕ} (hd : 0<d) (hb : 0<b) :
    (rightW a b d : ℝ)+(transmission (path ⟨b-1,by omega⟩ : Vertex a b d):ℝ) =
      ((a+b+d:ℕ):ℝ)^2-2*(d:ℝ)*(a+b+d:ℕ)+(d:ℝ)^2-(a:ℝ)^2+2*d+a-1 := by
  have hr := rightW_polynomial (a:=a) hd hb
  rw [shifted_actual_transmission hb]
  have hsub : ((b-1:ℕ):ℝ)=(b:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤b)]; norm_num
  push_cast
  rw [hsub]
  push_cast at hr
  nlinarith

#print axioms leftW_polynomial
#print axioms rightW_polynomial
#print axioms left_attachment_argument
#print axioms right_attachment_argument
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END CliquePolynomials@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN CliqueError 1777 dd9bd0a1455f4d265d23b3adfa01a82f07a27e1219433136bbdd83ec24d022b4@@
import CliquePolynomials
namespace SumBalaban

theorem polynomial_residual_bounds {a d n B : ℝ} (ha : 0≤a) (hd : 0≤d)
    (hn : 1≤n) (hB : 0≤B) (hs : a+d≤n) (hq : a^2+d^2≤B*n) :
    |a^2-d^2+n+a+d-2|≤(B+3)*n ∧ |a^2-d^2+2*a+d-1|≤(B+3)*n := by
  have hBn := mul_nonneg hB (show 0≤n by linarith)
  constructor <;> apply abs_le.mpr <;> constructor <;>
    nlinarith [sq_nonneg a,sq_nonneg d]

theorem actual_clique_arguments_error {a b d : ℕ} {B : ℝ}
    (ha : 0<a) (hb : 0<b) (hd : 0<d) (hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ)) :
    |2*(leftW a b d : ℝ)-((a+b+d:ℕ):ℝ)^2+2*(a:ℝ)*(a+b+d:ℕ)|≤(B+3)*(a+b+d:ℕ) ∧
    |2*(rightW a b d : ℝ)-((a+b+d:ℕ):ℝ)^2+2*(d:ℝ)*(a+b+d:ℕ)|≤(B+3)*(a+b+d:ℕ) ∧
    |(leftW a b d : ℝ)+(transmission (path ⟨0,hb⟩ : Vertex a b d):ℝ)-
      ((a+b+d:ℕ):ℝ)^2+2*(a:ℝ)*(a+b+d:ℕ)|≤(B+3)*(a+b+d:ℕ) ∧
    |(rightW a b d : ℝ)+(transmission (path ⟨b-1,by omega⟩ : Vertex a b d):ℝ)-
      ((a+b+d:ℕ):ℝ)^2+2*(d:ℝ)*(a+b+d:ℕ)|≤(B+3)*(a+b+d:ℕ) := by
  have hn : (1:ℝ)≤(a+b+d:ℕ) := by exact_mod_cast (show 1≤a+b+d by omega)
  have hs : (a:ℝ)+(d:ℝ)≤(a+b+d:ℕ) := by push_cast; linarith
  have hl := polynomial_residual_bounds (by positivity : (0:ℝ)≤a) (by positivity : (0:ℝ)≤d) hn hB hs hq
  have hr := polynomial_residual_bounds (by positivity : (0:ℝ)≤d) (by positivity : (0:ℝ)≤a) hn hB
    (by linarith : (d:ℝ)+(a:ℝ)≤(a+b+d:ℕ)) (by linarith : (d:ℝ)^2+(a:ℝ)^2≤B*(a+b+d:ℕ))
  rw [leftW_polynomial ha hb,rightW_polynomial hd hb,left_attachment_argument ha hb,right_attachment_argument hd hb]
  ring_nf at hl hr ⊢
  exact ⟨hl.1,hr.1,hl.2,hr.2⟩

#print axioms actual_clique_arguments_error
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END CliqueError@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN CliqueTaylor 3100 f5ebaf45094a8d4bdf9829cd7797747d9a1cf852624ed1d902a01125c83c55bc@@
import CliqueError
import PathKernel
namespace SumBalaban
theorem inverse_sqrt_first_correction {A a n B H : ℝ}
    (ha : 0≤a) (hn : 1≤n) (hB : 0≤B) (hH : 0≤H)
    (hlarge : 16*(B+H+1)≤n) (ha2 : a^2≤B*n)
    (herr : |A-n^2+2*a*n|≤H*n) :
    |1/Real.sqrt A - (1/n+a/n^2)| ≤ (4*H+6*B)/n^2 := by
  have hn0 : 0<n := by linarith
  have ha4 : a≤n/4 := by
    have : B*n≤n^2/16 := by nlinarith
    nlinarith [sq_nonneg (a-n/4)]
  have hnma : 0<n-a := by linarith
  have hA : n^2/4≤A := by
    have he := (abs_le.mp herr).1
    have : H*n≤n^2/16 := by nlinarith
    nlinarith
  have hT : n^2/4≤(n-a)^2 := by nlinarith [sq_nonneg (n/4)]
  have he : |A-(n-a)^2|≤(H+B)*n := by
    apply abs_le.mpr
    have hh := abs_le.mp herr
    constructor <;> nlinarith [sq_nonneg a]
  have he' := inverse_sqrt_error hn0 (by positivity : 0≤H+B) hA hT he
  rw [Real.sqrt_sq (le_of_lt hnma)] at he'
  have hid : 1/(n-a)-(1/n+a/n^2) = a^2/((n-a)*n^2) := by
    field_simp
    ring
  have hr : |1/(n-a)-(1/n+a/n^2)|≤2*B/n^2 := by
    rw [hid, abs_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (by positivity : 0<(n-a)*n^2)
      (by positivity : 0<n^2)).mpr
    have hab : a^2≤2*B*(n-a) := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg n)]
  calc
    _ ≤ |1/Real.sqrt A-1/(n-a)|+|1/(n-a)-(1/n+a/n^2)| :=
      abs_sub_le _ _ _
    _ ≤ 4*(H+B)/n^2+2*B/n^2 := add_le_add he' hr
    _ = _ := by ring

#print axioms inverse_sqrt_first_correction

theorem actual_clique_four_corrections {a b d : ℕ} {B : ℝ}
    (ha : 0<a) (hb : 0<b) (hd : 0<d) (hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ))
    (hn : 16*(2*B+4)≤((a+b+d:ℕ):ℝ)) :
    let n : ℝ := (a+b+d:ℕ)
    |1/Real.sqrt (2*(leftW a b d:ℝ))-(1/n+(a:ℝ)/n^2)|≤(10*B+12)/n^2 ∧
    |1/Real.sqrt (2*(rightW a b d:ℝ))-(1/n+(d:ℝ)/n^2)|≤(10*B+12)/n^2 ∧
    |1/Real.sqrt ((leftW a b d:ℝ)+(transmission (path ⟨0,hb⟩ : Vertex a b d):ℝ))-
      (1/n+(a:ℝ)/n^2)|≤(10*B+12)/n^2 ∧
    |1/Real.sqrt ((rightW a b d:ℝ)+(transmission (path ⟨b-1,by omega⟩ : Vertex a b d):ℝ))-
      (1/n+(d:ℝ)/n^2)|≤(10*B+12)/n^2 := by
  dsimp only
  obtain ⟨h1,h2,h3,h4⟩ := actual_clique_arguments_error ha hb hd hB hq
  have hn1 : (1:ℝ)≤(a+b+d:ℕ) := by exact_mod_cast (show 1≤a+b+d by omega)
  have hl : 16*(B+(B+3)+1)≤((a+b+d:ℕ):ℝ) := by linarith
  have ha2 : (a:ℝ)^2≤B*(a+b+d:ℕ) := by nlinarith [sq_nonneg (d:ℝ)]
  have hd2 : (d:ℝ)^2≤B*(a+b+d:ℕ) := by nlinarith [sq_nonneg (a:ℝ)]
  have hh : 0≤B+3 := by linarith
  have hc : 4*(B+3)+6*B=10*B+12 := by ring
  constructor
  · simpa only [hc] using inverse_sqrt_first_correction (by positivity) hn1 hB hh hl ha2 h1
  constructor
  · simpa only [hc] using inverse_sqrt_first_correction (by positivity) hn1 hB hh hl hd2 h2
  constructor
  · simpa only [hc] using inverse_sqrt_first_correction (by positivity) hn1 hB hh hl ha2 h3
  · simpa only [hc] using inverse_sqrt_first_correction (by positivity) hn1 hB hh hl hd2 h4
#print axioms actual_clique_four_corrections

end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END CliqueTaylor@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN RadialCost 1295 86a993a820a4eeff9174b5c781dc6d32b2d450cf4064e76eae67e15bb0fae226@@
import CliqueError
namespace SumBalaban
noncomputable def radialF (q : ℝ) : ℝ := q/2+1+Q+2*Q/q
noncomputable def radialQ : ℝ := 2*Real.sqrt Q

theorem radialQ_pos : 0<radialQ := mul_pos (by norm_num) (Real.sqrt_pos.mpr Q_pos)

theorem radial_excess {q : ℝ} (hq : 0<q) :
    radialF q-radialF radialQ = (q-radialQ)^2/(2*q) := by
  have hsq := Real.sq_sqrt (le_of_lt Q_pos)
  have hspos := Real.sqrt_pos.mpr Q_pos
  unfold radialF radialQ
  field_simp
  nlinarith

theorem radial_excess_nonneg {q : ℝ} (hq : 0<q) :
    0≤radialF q-radialF radialQ := by rw [radial_excess hq]; positivity

theorem radial_cost_bound {q δ L e : ℝ} (hδ : 0<δ) (hq : δ≤q)
    (_hL : 0≤L) (_he : 0≤e) (herr : |q-radialQ|≤L*e) :
    radialF q-radialF radialQ ≤ L^2*e^2/(2*δ) := by
  have hq0 : 0<q := lt_of_lt_of_le hδ hq
  have habs := abs_le.mp herr
  have hs : (q-radialQ)^2≤L^2*e^2 := by
    have hprod := mul_nonneg (show 0≤L*e-(q-radialQ) by linarith)
      (show 0≤L*e+(q-radialQ) by linarith)
    nlinarith
  rw [radial_excess hq0]
  calc
    _ ≤ (L^2*e^2)/(2*q) := div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

#print axioms radial_excess
#print axioms radial_cost_bound
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END RadialCost@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN CliqueSumCorrection 4161 5e359c7a1a9ffc5d410e163fceb9d5a5b2d4d05f408d86fa4cc80618c5239c18@@
import CliqueTaylor
namespace SumBalaban
theorem weighted_two_error {w z t v ε k : ℝ} (hw : 0≤w) (hv : 0≤v)
    (hz : |z-k|≤ε) (ht : |t-k|≤ε) :
    |w*z+v*t-(w+v)*k|≤(w+v)*ε := by
  calc
    _ = |w*(z-k)+v*(t-k)| := by congr 1; ring
    _ ≤ |w*(z-k)|+|v*(t-k)| := abs_add_le _ _
    _ = w*|z-k|+v*|t-k| := by rw [abs_mul,abs_mul,abs_of_nonneg hw,abs_of_nonneg hv]
    _ ≤ w*ε+v*ε := add_le_add (mul_le_mul_of_nonneg_left hz hw) (mul_le_mul_of_nonneg_left ht hv)
    _ = _ := by ring
noncomputable def actualCliqueSum (a b d : ℕ) (hb : 0<b) : ℝ :=
  (a:ℝ)*(a-1:ℕ)/2*(1/Real.sqrt (2*(leftW a b d:ℝ)))+
  (a:ℝ)*(1/Real.sqrt ((leftW a b d:ℝ)+(transmission (path ⟨0,hb⟩ : Vertex a b d):ℝ)))+
  (d:ℝ)*(d-1:ℕ)/2*(1/Real.sqrt (2*(rightW a b d:ℝ)))+
  (d:ℝ)*(1/Real.sqrt ((rightW a b d:ℝ)+(transmission (path ⟨b-1,by omega⟩ : Vertex a b d):ℝ)))
theorem actual_clique_sum_first_correction {a b d : ℕ} {B : ℝ}
    (ha : 0<a) (hb : 0<b) (hd : 0<d) (hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ))
    (hn : 16*(2*B+4)≤((a+b+d:ℕ):ℝ)) :
    let n : ℝ := (a+b+d:ℕ)
    |actualCliqueSum a b d hb-
      (((a:ℝ)^2+(d:ℝ)^2)/(2*n)+((a:ℝ)+d)/(2*n)+
       ((a:ℝ)^3+(d:ℝ)^3)/(2*n^2))|≤
      ((B+1)*(10*B+12)+B)/n := by
  dsimp only
  let n : ℝ := (a+b+d:ℕ)
  have hn0 : 0<n := by dsimp [n]; exact_mod_cast (show 0<a+b+d by omega)
  have ham : ((a-1:ℕ):ℝ)=(a:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hdm : ((d-1:ℕ):ℝ)=(d:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  obtain ⟨h1,h2,h3,h4⟩ := actual_clique_four_corrections ha hb hd hB hq hn
  have hL := weighted_two_error (w:=(a:ℝ)*(a-1:ℕ)/2) (v:=(a:ℝ))
    (by positivity) (by positivity) h1 h3
  have hR := weighted_two_error (w:=(d:ℝ)*(d-1:ℕ)/2) (v:=(d:ℝ))
    (by positivity) (by positivity) h2 h4
  have hW : ((a:ℝ)*(a-1:ℕ)/2+a)+((d:ℝ)*(d-1:ℕ)/2+d)≤(B+1)*n := by
    rw [ham,hdm]
    have hs : (a:ℝ)+d≤n := by dsimp [n]; push_cast; linarith [show (0:ℝ)≤b by positivity]
    change (a:ℝ)^2+(d:ℝ)^2≤B*n at hq
    nlinarith
  let P : ℝ := ((a:ℝ)*(a-1:ℕ)/2+a)*(1/n+(a:ℝ)/n^2)+
    ((d:ℝ)*(d-1:ℕ)/2+d)*(1/n+(d:ℝ)/n^2)
  have hE : |actualCliqueSum a b d hb-P|≤((B+1)*(10*B+12))/n := by
    have hh := abs_add_le
      ((a:ℝ)*(a-1:ℕ)/2*(1/Real.sqrt (2*(leftW a b d:ℝ)))+
       (a:ℝ)*(1/Real.sqrt ((leftW a b d:ℝ)+(transmission (path ⟨0,hb⟩ : Vertex a b d):ℝ)))-
       ((a:ℝ)*(a-1:ℕ)/2+a)*(1/n+(a:ℝ)/n^2))
      ((d:ℝ)*(d-1:ℕ)/2*(1/Real.sqrt (2*(rightW a b d:ℝ)))+
       (d:ℝ)*(1/Real.sqrt ((rightW a b d:ℝ)+(transmission (path ⟨b-1,by omega⟩ : Vertex a b d):ℝ)))-
       ((d:ℝ)*(d-1:ℕ)/2+d)*(1/n+(d:ℝ)/n^2))
    have hh' := hh.trans (add_le_add hL hR)
    have hr : (actualCliqueSum a b d hb-P)=
      ((a:ℝ)*(a-1:ℕ)/2*(1/Real.sqrt (2*(leftW a b d:ℝ)))+
       (a:ℝ)*(1/Real.sqrt ((leftW a b d:ℝ)+(transmission (path ⟨0,hb⟩ : Vertex a b d):ℝ)))-
       ((a:ℝ)*(a-1:ℕ)/2+a)*(1/n+(a:ℝ)/n^2))+
      ((d:ℝ)*(d-1:ℕ)/2*(1/Real.sqrt (2*(rightW a b d:ℝ)))+
       (d:ℝ)*(1/Real.sqrt ((rightW a b d:ℝ)+(transmission (path ⟨b-1,by omega⟩ : Vertex a b d):ℝ)))-
       ((d:ℝ)*(d-1:ℕ)/2+d)*(1/n+(d:ℝ)/n^2)) := by dsimp [actualCliqueSum,P]; ring
    rw [←hr] at hh'
    apply hh'.trans
    have hm := mul_le_mul_of_nonneg_right hW (show 0≤(10*B+12)/n^2 by positivity)
    have hid : (B+1)*n*((10*B+12)/n^2)=((B+1)*(10*B+12))/n := by field_simp
    rw [hid] at hm
    nlinarith
  let T : ℝ := ((a:ℝ)^2+(d:ℝ)^2)/(2*n)+((a:ℝ)+d)/(2*n)+
    ((a:ℝ)^3+(d:ℝ)^3)/(2*n^2)
  have hPT : P-T=((a:ℝ)^2+(d:ℝ)^2)/(2*n^2) := by dsimp [P,T]; rw [ham,hdm]; ring
  have hPTb : |P-T|≤B/n := by
    rw [hPT,abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by positivity : 0<2*n^2)).mpr
    field_simp
    nlinarith
  have hh := (abs_sub_le (actualCliqueSum a b d hb) P T).trans (add_le_add hE hPTb)
  change |actualCliqueSum a b d hb-T|≤((B+1)*(10*B+12)+B)/n
  convert hh using 1; ring
#print axioms actual_clique_sum_first_correction
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END CliqueSumCorrection@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN OptimalTrial 3491 035053500b750a55bf1633ab86b46e615280a7dd68c058ea726e09fce42504e4@@
import RadialCost
import Mathlib.Algebra.Order.Floor.Ring
namespace SumBalaban
noncomputable def optimalTrial (n : ℕ) : Triple :=
  let k := Nat.floor (c*Real.sqrt n)
  (k,n-2*k,k)
theorem optimal_trial_bounds {n : ℕ} (hn : 4≤n)
    (hlo : 4≤c^2*(n:ℝ)) (hhi : 16*c^2≤(n:ℝ)) :
    admissible n (optimalTrial n) ∧
    c/2≤((optimalTrial n).1:ℝ)/Real.sqrt n ∧
    ((optimalTrial n).1:ℝ)/Real.sqrt n≤c ∧
    |2*(((optimalTrial n).1:ℝ)/Real.sqrt n)^2-radialQ|≤4*c/Real.sqrt n := by
  let k := Nat.floor (c*Real.sqrt n)
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hs := Real.sqrt_pos.mpr hn0
  have hs2 := Real.sq_sqrt (le_of_lt hn0)
  have hc := c_pos
  have hx0 : 0≤c*Real.sqrt n := by positivity
  have hx2 : (c*Real.sqrt n)^2=c^2*(n:ℝ) := by rw [mul_pow,hs2]
  have hxlo : 2≤c*Real.sqrt n := by nlinarith [sq_nonneg (c*Real.sqrt n-2)]
  have hxhi : c*Real.sqrt n≤(n:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right hhi (le_of_lt hn0)
    nlinarith [sq_nonneg (c*Real.sqrt n-(n:ℝ)/4)]
  have hklo : 1≤k := by
    apply Nat.le_floor
    norm_num
    linarith
  have hkhi : (k:ℝ)≤c*Real.sqrt n := Nat.floor_le hx0
  have hkerr : c*Real.sqrt n<(k:ℝ)+1 := Nat.lt_floor_add_one _
  have hkpath : 2*k+1≤n := by
    have hn4 : (4:ℝ)≤n := by exact_mod_cast hn
    have hh : (2:ℝ)*k+1≤n := by linarith
    exact_mod_cast hh
  have hadm : admissible n (optimalTrial n) := by
    change 0<k ∧ 0<n-2*k ∧ 0<k ∧ k+(n-2*k)+k=n ∧ k≤k
    omega
  let z : ℝ := (k:ℝ)/Real.sqrt n
  have hz0 : 0≤z := by positivity
  have hzhi : z≤c := (div_le_iff₀ hs).mpr hkhi
  have hzlo : c/2≤z := by
    apply (le_div_iff₀ hs).mpr
    nlinarith
  have he : c-z≤1/Real.sqrt n := by
    apply (le_div_iff₀ hs).mpr
    dsimp [z]
    field_simp
    linarith
  have hq0 : radialQ=2*c^2 := by
    unfold radialQ c
    rw [Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mpr Q_pos))]
  have hqhi : 2*z^2≤radialQ := by rw [hq0]; nlinarith
  have hcost : radialQ-2*z^2≤4*c/Real.sqrt n := by
    rw [hq0]
    have hh := mul_le_mul he (show c+z≤2*c by linarith)
      (by positivity : 0≤c+z) (by positivity : 0≤1/Real.sqrt n)
    have hid : (1/Real.sqrt n)*(2*c)=2*c/Real.sqrt n := by ring
    rw [hid] at hh
    calc
      _ = 2*((c-z)*(c+z)) := by ring
      _ ≤ 2*(2*c/Real.sqrt n) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  refine ⟨hadm,?_,?_,?_⟩
  · exact hzlo
  · exact hzhi
  · change |2*z^2-radialQ|≤_
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem optimal_trial_radial_cost {n : ℕ} (hn : 4≤n)
    (hlo : 4≤c^2*(n:ℝ)) (hhi : 16*c^2≤(n:ℝ)) :
    radialF (2*(((optimalTrial n).1:ℝ)/Real.sqrt n)^2)-radialF radialQ≤
      16*c^2/(c^2*(n:ℝ)) := by
  obtain ⟨_,hl,hu,he⟩ := optimal_trial_bounds hn hlo hhi
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hs := Real.sqrt_pos.mpr hn0
  have hc := c_pos
  have hh := radial_cost_bound (q:=2*(((optimalTrial n).1:ℝ)/Real.sqrt n)^2)
    (δ:=c^2/2) (L:=4*c) (e:=1/Real.sqrt n)
    (by positivity : 0<c^2/2) (by nlinarith [c_pos])
    (by positivity) (by positivity) (by simpa only [mul_one_div] using he)
  have hid : (4*c)^2*(1/Real.sqrt n)^2/(2*(c^2/2))=16*c^2/(c^2*(n:ℝ)) := by
    rw [div_pow,Real.sq_sqrt (le_of_lt hn0)]
    field_simp
    ring
  rw [hid] at hh
  exact hh
#print axioms optimal_trial_bounds
#print axioms optimal_trial_radial_cost
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END OptimalTrial@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN Prefactor 2487 02cac29c09d440ab72ed5c7954706521f12bd06340551a306a718d2666d4915c@@
import CliqueTaylor
namespace SumBalaban
theorem prefactor_residual_identity {q u v : ℝ}
    (hq : q≠0) (hD : q-u+2*v≠0) :
    (1+(2-4*v)/(q-u+2*v))-(1+2/q+2*u/q^2) =
    (2*u^2-4*v*q^2-4*v*q-4*u*v)/(q^2*(q-u+2*v)) := by
  field_simp
  ring

theorem prefactor_uniform_bound {q u v B δ : ℝ}
    (hδ : 0<δ) (hq : δ≤q) (hB : q≤B)
    (hu : 0≤u) (hu1 : u≤1) (huδ : u≤δ/2) (hv : 0≤v)
    (hu2 : u^2≤2*B*v) :
    |(1+(2-4*v)/(q-u+2*v))-(1+2/q+2*u/q^2)| ≤
      2*(4*B^2+8*B+4)*v/δ^3 := by
  have hq0 : 0<q := lt_of_lt_of_le hδ hq
  have hB0 : 0≤B := by linarith
  have hD : 0<q-u+2*v := by linarith
  rw [prefactor_residual_identity (ne_of_gt hq0) (ne_of_gt hD), abs_div,
    abs_of_pos (mul_pos (sq_pos_of_pos hq0) hD)]
  have hnum : |2*u^2-4*v*q^2-4*v*q-4*u*v|≤(4*B^2+8*B+4)*v := by
    have hq2 : q^2≤B^2 := by nlinarith
    have hvq := mul_le_mul_of_nonneg_left hq2 hv
    have hvq' := mul_le_mul_of_nonneg_left hB hv
    have huv := mul_le_mul_of_nonneg_left hu1 hv
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg u, mul_nonneg hv (sq_nonneg q),
      mul_nonneg hu hv, mul_nonneg (le_of_lt hq0) hv]
  have hq2 : δ^2≤q^2 := by nlinarith
  have hden : δ^3/2≤q^2*(q-u+2*v) := by
    have hh := mul_le_mul hq2 (show δ/2≤q-u+2*v by linarith)
      (by positivity : 0≤δ/2) (sq_nonneg q)
    nlinarith
  have hc : 0≤(4*B^2+8*B+4)*v := by positivity
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hq0) hD)).mpr
  apply hnum.trans
  have hh := mul_le_mul_of_nonneg_left hden
    (show 0≤2*(4*B^2+8*B+4)*v/δ^3 by positivity)
  have hid : 2*(4*B^2+8*B+4)*v/δ^3*(δ^3/2) =
      (4*B^2+8*B+4)*v := by field_simp
  rw [hid] at hh
  exact hh

theorem actual_prefactor_exact {a b d : ℕ} (hb : 0<b) :
    let n : ℝ := (a+b+d:ℕ)
    let q : ℝ := ((a:ℝ)^2+(d:ℝ)^2)/n
    let u : ℝ := ((a:ℝ)+d)/n
    let v : ℝ := 1/n
    (edgeCount a b d:ℝ)/((edgeCount a b d:ℝ)-n+2) =
      1+(2-4*v)/(q-u+2*v) := by
  dsimp only
  have hn : (0:ℝ)<(a+b+d:ℕ) := by exact_mod_cast (show 0<a+b+d by omega)
  have he := real_edge_count_formula (a:=a) (d:=d) hb
  have hk := cycle_denominator_pos (a:=a) (d:=d) hb
  rw [he] at *
  have hD : (a:ℝ)^2+(d:ℝ)^2-a-d+2≠0 := by nlinarith [hk]
  have hi := mul_inv_cancel₀ hD
  ring_nf at hi
  field_simp [ne_of_gt hn, hD]
  linear_combination hi

#print axioms prefactor_residual_identity
#print axioms prefactor_uniform_bound
#print axioms actual_prefactor_exact
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END Prefactor@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN ActualPrefactor 1917 0448a8c9530255dfa75de9eba71812327c988cfc3e3b0560b4086ebccbce283a@@
import Prefactor
namespace SumBalaban
theorem actual_prefactor_first_correction {a b d : ℕ} {B δ : ℝ}
    (hb : 0<b) (_hB : 0≤B) (hδ : 0<δ)
    (hq : (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ))
    (hqlo : δ*(a+b+d:ℕ)≤(a:ℝ)^2+(d:ℝ)^2)
    (hn : 8*B≤δ^2*(a+b+d:ℕ)) :
    let n : ℝ := (a+b+d:ℕ)
    let q : ℝ := ((a:ℝ)^2+(d:ℝ)^2)/n
    let u : ℝ := ((a:ℝ)+d)/n
    |(edgeCount a b d:ℝ)/((edgeCount a b d:ℝ)-n+2)-
      (1+2/q+2*u/q^2)|≤2*(4*B^2+8*B+4)/δ^3/n := by
  dsimp only
  let n : ℝ := (a+b+d:ℕ)
  let q : ℝ := ((a:ℝ)^2+(d:ℝ)^2)/n
  let u : ℝ := ((a:ℝ)+d)/n
  have hn0 : 0<n := by dsimp [n]; exact_mod_cast (show 0<a+b+d by omega)
  have hS : ((a:ℝ)+d)^2≤2*B*n := by
    change (a:ℝ)^2+(d:ℝ)^2≤B*n at hq
    nlinarith [sq_nonneg ((a:ℝ)-d)]
  have hSl : (a:ℝ)+d≤δ*n/2 := by
    change 8*B≤δ^2*n at hn
    have hh := mul_le_mul_of_nonneg_right hn (le_of_lt hn0)
    have hdn : 0<δ*n := mul_pos hδ hn0
    nlinarith [sq_nonneg (((a:ℝ)+d)-δ*n/2)]
  have hq' : δ≤q := (le_div_iff₀ hn0).mpr hqlo
  have hqB : q≤B := (div_le_iff₀ hn0).mpr hq
  have hu1 : u≤1 := by
    apply (div_le_one hn0).mpr
    dsimp [n]
    push_cast
    linarith [show (0:ℝ)≤b by positivity]
  have huδ : u≤δ/2 := (div_le_iff₀ hn0).mpr (by linarith)
  have hu2 : u^2≤2*B*(1/n) := by
    dsimp [u]
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
    field_simp
    nlinarith
  have he := prefactor_uniform_bound hδ hq' hqB (by dsimp [u]; positivity) hu1 huδ
    (by positivity : 0≤1/n) hu2
  have hid := actual_prefactor_exact (a:=a) (d:=d) hb
  change (edgeCount a b d:ℝ)/((edgeCount a b d:ℝ)-n+2)=
    1+(2-4*(1/n))/(q-u+2*(1/n)) at hid
  change |(edgeCount a b d:ℝ)/((edgeCount a b d:ℝ)-n+2)-(1+2/q+2*u/q^2)|≤_
  rw [hid]
  convert he using 1; ring
#print axioms actual_prefactor_first_correction
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END ActualPrefactor@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN EdgeFirstCorrection 1837 66678ee5a9e44b8126a7b1445560fcbf291d6d8fc98e7b7317be89aa36bbde7a@@
import CliqueSumCorrection
import PathFirstCorrection
namespace SumBalaban
open scoped BigOperators
theorem actual_edge_sum_split {a b d : ℕ} (hb : 0<b) :
    (∑ e ∈ (graph a b d).edgeFinset, edgeWeight e)=
      actualCliqueSum a b d hb+pathForward a b d := by
  rw [five_sum_identity hb]
  unfold actualCliqueSum
  simp only [kernel,←two_mul]
  ring

theorem actual_edge_first_correction {a b d : ℕ} {B : ℝ}
    (ha : 0<a) (hb : 0<b) (hd : 0<d) (hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ))
    (hn : 16*(2*B+4)≤((a+b+d:ℕ):ℝ)) :
    let n : ℝ := (a+b+d:ℕ)
    |(∑ e ∈ (graph a b d).edgeFinset, edgeWeight e)-
      (((a:ℝ)^2+(d:ℝ)^2)/(2*n)+Q+
       ((a:ℝ)^3+(d:ℝ)^3)/(2*n^2)-((a:ℝ)+d)/(2*n))|≤
      ((B+1)*(10*B+12)+21*B+45)/n := by
  dsimp only
  let n : ℝ := (a+b+d:ℕ)
  have hC := actual_clique_sum_first_correction ha hb hd hB hq hn
  have hP := actual_path_first_correction hb hB hq (by nlinarith)
  let TC : ℝ := ((a:ℝ)^2+(d:ℝ)^2)/(2*n)+((a:ℝ)+d)/(2*n)+
       ((a:ℝ)^3+(d:ℝ)^3)/(2*n^2)
  let TP : ℝ := Q-((a:ℝ)+d)/n
  have hident :
      (∑ e ∈ (graph a b d).edgeFinset, edgeWeight e)-
      (((a:ℝ)^2+(d:ℝ)^2)/(2*n)+Q+
       ((a:ℝ)^3+(d:ℝ)^3)/(2*n^2)-((a:ℝ)+d)/(2*n)) =
      (actualCliqueSum a b d hb-TC)+(pathForward a b d-TP) := by
    rw [actual_edge_sum_split hb]
    dsimp [TC,TP]
    ring
  change |(∑ e ∈ (graph a b d).edgeFinset, edgeWeight e)-
      (((a:ℝ)^2+(d:ℝ)^2)/(2*n)+Q+
       ((a:ℝ)^3+(d:ℝ)^3)/(2*n^2)-((a:ℝ)+d)/(2*n))|≤_
  rw [hident]
  calc
    _ ≤ |actualCliqueSum a b d hb-TC|+|pathForward a b d-TP| := abs_add_le _ _
    _ ≤ ((B+1)*(10*B+12)+B)/n+(20*B+45)/n := add_le_add hC hP
    _ = _ := by ring
#print axioms actual_edge_sum_split
#print axioms actual_edge_first_correction
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END EdgeFirstCorrection@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN OptimalTrialEventually 1256 d9282bff9ae7aec5e0b90e9096e05c00afad8972a5ae9c5fe491c96fcac6c711@@
import OptimalTrial
namespace SumBalaban
theorem optimal_trial_eventually :
    ∀ᶠ n : ℕ in Filter.atTop, admissible n (optimalTrial n) ∧
      radialF (2*(((optimalTrial n).1:ℝ)/Real.sqrt n)^2)-radialF radialQ≤16/(n:ℝ) := by
  let T : ℝ := 4+4/c^2+16*c^2
  refine Filter.eventually_atTop.mpr ⟨Nat.ceil T,?_⟩
  intro n hn
  have hc := c_pos
  have hcn : c≠0 := ne_of_gt hc
  have hceil : T≤(Nat.ceil T:ℝ) := Nat.le_ceil T
  have hnn : (Nat.ceil T:ℝ)≤n := by exact_mod_cast hn
  have hT : T≤(n:ℝ) := le_trans hceil hnn
  have hn4 : (4:ℝ)≤n := by dsimp [T] at hT; nlinarith [show (0:ℝ)≤4/c^2 by positivity]
  have h4 : 4≤n := by exact_mod_cast hn4
  have hn0 : (0:ℝ)<n := by linarith
  have hlo : 4≤c^2*(n:ℝ) := by
    have hbound : 4/c^2≤(n:ℝ) := by dsimp [T] at hT; nlinarith [sq_nonneg c]
    have hh := (div_le_iff₀ (sq_pos_of_pos hc)).mp hbound
    nlinarith
  have hhi : 16*c^2≤(n:ℝ) := by dsimp [T] at hT; nlinarith [show (0:ℝ)≤4/c^2 by positivity]
  refine ⟨(optimal_trial_bounds h4 hlo hhi).1,?_⟩
  have he := optimal_trial_radial_cost h4 hlo hhi
  have hid : 16*c^2/(c^2*(n:ℝ))=16/(n:ℝ) := by field_simp
  rwa [hid] at he
#print axioms optimal_trial_eventually
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END OptimalTrialEventually@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN NormalizedBounds 1681 02ca3bd28ff8106a8c50e6680db9a5cfd2e657b82fbb85de1d340b85bd2e8d77@@
import ActualPrefactor
namespace SumBalaban
theorem actual_normalized_bounds {a b d : ℕ} {B δ : ℝ}
    (hb : 0<b) (_hB : 0≤B)
    (hq : (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ))
    (hql : δ*(a+b+d:ℕ)≤(a:ℝ)^2+(d:ℝ)^2) :
    let n : ℝ := (a+b+d:ℕ)
    let q : ℝ := ((a:ℝ)^2+(d:ℝ)^2)/n
    let u : ℝ := ((a:ℝ)+d)/n
    let t : ℝ := ((a:ℝ)^3+(d:ℝ)^3)/n^2
    δ≤q ∧ q≤B ∧ 0≤u ∧ u≤1 ∧ 0≤t ∧ t≤B*u ∧ u^2≤2*B/n := by
  dsimp only
  let n : ℝ := (a+b+d:ℕ)
  let q : ℝ := ((a:ℝ)^2+(d:ℝ)^2)/n
  let u : ℝ := ((a:ℝ)+d)/n
  let t : ℝ := ((a:ℝ)^3+(d:ℝ)^3)/n^2
  have hn0 : 0<n := by dsimp [n]; exact_mod_cast (show 0<a+b+d by omega)
  have hu0 : 0≤u := by dsimp [u]; positivity
  have hqB : q≤B := (div_le_iff₀ hn0).mpr hq
  have hu1 : u≤1 := by
    apply (div_le_one hn0).mpr
    dsimp [n]
    push_cast
    linarith [show (0:ℝ)≤b by positivity]
  have htq : t≤u*q := by
    have hid : u*q=(((a:ℝ)+d)*((a:ℝ)^2+(d:ℝ)^2))/n^2 := by dsimp [u,q]; ring
    rw [hid]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hn0)).mpr
    have hh : 0≤(a:ℝ)*(d:ℝ)*((a:ℝ)+d) := by positivity
    nlinarith
  have htB : t≤B*u := by
    have hh := mul_le_mul_of_nonneg_left hqB hu0
    nlinarith
  have hu2 : u^2≤2*B/n := by
    have hid : 2*B/n=(2*B*n)/n^2 := by field_simp
    rw [hid]
    dsimp [u]
    rw [div_pow]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hn0)).mpr
    change (a:ℝ)^2+(d:ℝ)^2≤B*n at hq
    nlinarith [sq_nonneg ((a:ℝ)-d)]
  refine ⟨(le_div_iff₀ hn0).mpr hql,hqB,hu0,hu1,?_,htB,hu2⟩
  positivity
#print axioms actual_normalized_bounds
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END NormalizedBounds@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN ProductCorrection 1527 ba2bf6e094cacd0007602c3261a405aaa617f0ea207141bddc54ee99b9a48f41@@
import RadialCost
import EdgeFirstCorrection
import ActualPrefactor
namespace SumBalaban
noncomputable def correctionG (x y : ℝ) : ℝ :=
  let q := x^2+y^2
  (q+2)*(x^3+y^3)/(2*q)+(x+y)*(-1/2+2*Q/q^2)

theorem normalized_product_identity {x y e : ℝ} (hq : x^2+y^2≠0) :
    let q := x^2+y^2
    let s := x+y
    let r := x^3+y^3
    (1+2/q+2*e*s/q^2)*(q/2+Q+e*(r-s)/2) =
      radialF q+e*correctionG x y+e^2*s*(r-s)/q^2 := by
  dsimp only
  unfold radialF correctionG
  dsimp only
  field_simp
  ring

theorem product_remainder_bound {P E P₀ A T n KP KE KD M L : ℝ}
    (hn : 0<n) (hKP : 0≤KP) (_hKE : 0≤KE)
    (hP : |P-P₀|≤KP/n) (hE : |E-A|≤KE/n)
    (hM : |E|≤M) (hL : |P₀|≤L) (hcross : |P₀*A-T|≤KD/n) :
    |P*E-T|≤(KP*M+L*KE+KD)/n := by
  have hM0 : 0≤M := le_trans (abs_nonneg _) hM
  have hL0 : 0≤L := le_trans (abs_nonneg _) hL
  have h1 : |(P-P₀)*E|≤(KP/n)*M := by
    rw [abs_mul]
    exact mul_le_mul hP hM (abs_nonneg _) (by positivity)
  have h2 : |P₀*(E-A)|≤L*(KE/n) := by
    rw [abs_mul]
    exact mul_le_mul hL hE (abs_nonneg _) hL0
  have hid : P*E-T = ((P-P₀)*E+P₀*(E-A))+(P₀*A-T) := by ring
  rw [hid]
  calc
    _ ≤ |(P-P₀)*E+P₀*(E-A)|+|P₀*A-T| := abs_add_le _ _
    _ ≤ (|(P-P₀)*E|+|P₀*(E-A)|)+|P₀*A-T| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((KP/n)*M+L*(KE/n))+KD/n := add_le_add (add_le_add h1 h2) hcross
    _ = _ := by ring
#print axioms normalized_product_identity
#print axioms product_remainder_bound
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END ProductCorrection@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN ClusterSelection 1113 735347c5eb319dc8e475b9af0eb484b15880497a9c4ad3feb3cc9314cc0b3ec3@@
import ProductCorrection
import OptimalTrialEventually
namespace SumBalaban
theorem source_c_fourth : c^4=Q := by
  have h1 := Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mpr Q_pos))
  have h2 := Real.sq_sqrt (le_of_lt Q_pos)
  unfold c
  nlinarith

theorem correction_at_optimal_radius {x y : ℝ}
    (hq : x^2+y^2=2*c^2) :
    correctionG x y=(c^2+1)/(2*c^2)*(x^3+y^3) := by
  have hc := c_pos
  unfold correctionG
  dsimp only
  rw [hq,←source_c_fourth]
  field_simp
  ring

theorem optimal_cluster_forced_balanced {x y : ℝ} (hx : 0≤x) (hy : 0≤y)
    (hq : x^2+y^2=2*c^2) (hG : correctionG x y≤correctionG c c) :
    x=c ∧ y=c := by
  obtain ⟨hl,he⟩ := angular_cubic hx hy c_pos hq
  have h1 := correction_at_optimal_radius hq
  have h2 := correction_at_optimal_radius (x:=c) (y:=c) (by ring)
  rw [h1,h2] at hG
  have hp : 0<(c^2+1)/(2*c^2) := by have := c_pos; positivity
  have hu : x^3+y^3≤2*c^3 := by nlinarith only [hG,hp]
  exact he.mp (le_antisymm hu hl)
#print axioms source_c_fourth
#print axioms correction_at_optimal_radius
#print axioms optimal_cluster_forced_balanced
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END ClusterSelection@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN MixedProduct 1708 ec14bc4befe5705cfef61d262991d9e76577c2dbb98fa7021a4a9ffc88789448@@
import ProductCorrection
import NormalizedBounds
namespace SumBalaban
theorem mixed_remainder_bound {q u t n B δ : ℝ} (hn : 0<n) (hδ : 0<δ)
    (hq : δ≤q) (hB : 0≤B) (hu : 0≤u) (ht : 0≤t)
    (htu : t≤B*u) (hu2 : u^2≤2*B/n) :
    |u*(t-u)/q^2|≤2*B*(B+1)/(δ^2*n) := by
  have hq0 : 0<q := lt_of_lt_of_le hδ hq
  have hq2 : δ^2≤q^2 := by nlinarith
  have ha : |t-u|≤(B+1)*u := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hnum : u*|t-u|≤2*B*(B+1)/n := by
    have h1 := mul_le_mul_of_nonneg_left ha hu
    have h2 := mul_le_mul_of_nonneg_left hu2 (show 0≤B+1 by linarith)
    calc
      _ ≤ u*((B+1)*u) := h1
      _ = (B+1)*u^2 := by ring
      _ ≤ (B+1)*(2*B/n) := h2
      _ = _ := by ring
  calc
    _ = (u*|t-u|)/q^2 := by
      rw [abs_div,abs_mul,abs_of_nonneg hu,abs_of_pos (sq_pos_of_pos hq0)]
    _ ≤ (2*B*(B+1)/n)/q^2 := div_le_div_of_nonneg_right hnum (sq_nonneg q)
    _ ≤ (2*B*(B+1)/n)/δ^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hδ) hq2
    _ = _ := by ring

theorem actual_mixed_remainder {a b d : ℕ} {B δ : ℝ}
    (hb : 0<b) (hB : 0≤B) (hδ : 0<δ)
    (hq : (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ))
    (hql : δ*(a+b+d:ℕ)≤(a:ℝ)^2+(d:ℝ)^2) :
    let n : ℝ := (a+b+d:ℕ)
    let q : ℝ := ((a:ℝ)^2+(d:ℝ)^2)/n
    let u : ℝ := ((a:ℝ)+d)/n
    let t : ℝ := ((a:ℝ)^3+(d:ℝ)^3)/n^2
    |u*(t-u)/q^2|≤2*B*(B+1)/(δ^2*n) := by
  obtain ⟨h1,_,h3,_,h5,h6,h7⟩ := actual_normalized_bounds hb hB hq hql
  apply mixed_remainder_bound ?_ hδ h1 hB h3 h5 h6 h7
  exact_mod_cast (show 0<a+b+d by omega)
#print axioms mixed_remainder_bound
#print axioms actual_mixed_remainder
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END MixedProduct@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN UniformExpansion 3679 1f8e9effafed35cb7674c5b5e67439e6e6ecefe0e638e896adc969a2c9cb9047@@
import MixedProduct
namespace SumBalaban
open scoped BigOperators
noncomputable def edgeErrorK (B : ℝ) : ℝ := (B+1)*(10*B+12)+21*B+45
noncomputable def prefactorErrorK (B δ : ℝ) : ℝ := 2*(4*B^2+8*B+4)/δ^3
noncomputable def combinedErrorK (B δ : ℝ) : ℝ :=
  prefactorErrorK B δ*(B+Q+edgeErrorK B+1)+
  (1+2/δ+2/δ^2)*edgeErrorK B+2*B*(B+1)/δ^2

theorem actual_SJ_rational_expansion {a b d : ℕ} {B δ : ℝ}
    (ha : 0<a) (hb : 0<b) (hd : 0<d) (hB : 0≤B) (hδ : 0<δ)
    (hq : (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ))
    (hql : δ*(a+b+d:ℕ)≤(a:ℝ)^2+(d:ℝ)^2)
    (hn : 16*(2*B+4)≤((a+b+d:ℕ):ℝ))
    (hnδ : 8*B≤δ^2*(a+b+d:ℕ)) :
    let n : ℝ := (a+b+d:ℕ)
    let q : ℝ := ((a:ℝ)^2+(d:ℝ)^2)/n
    let u : ℝ := ((a:ℝ)+d)/n
    let t : ℝ := ((a:ℝ)^3+(d:ℝ)^3)/n^2
    |SJ a b d-((1+2/q)*(q/2+Q)+(1+2/q)*(t-u)/2+
      (2*u/q^2)*(q/2+Q))|≤combinedErrorK B δ/n := by
  dsimp only
  let n : ℝ := (a+b+d:ℕ)
  let q : ℝ := ((a:ℝ)^2+(d:ℝ)^2)/n
  let u : ℝ := ((a:ℝ)+d)/n
  let t : ℝ := ((a:ℝ)^3+(d:ℝ)^3)/n^2
  let P : ℝ := (edgeCount a b d:ℝ)/((edgeCount a b d:ℝ)-n+2)
  let E : ℝ := ∑ e ∈ (graph a b d).edgeFinset, edgeWeight e
  let P₀ : ℝ := 1+2/q+2*u/q^2
  let A : ℝ := q/2+Q+(t-u)/2
  let T : ℝ := (1+2/q)*(q/2+Q)+(1+2/q)*(t-u)/2+(2*u/q^2)*(q/2+Q)
  have hn0 : 0<n := by dsimp [n]; exact_mod_cast (show 0<a+b+d by omega)
  have hn1 : 1≤n := by change 1≤((a+b+d:ℕ):ℝ); nlinarith
  obtain ⟨hqlo,hqB,hu0,hu1,ht0,htu,hu2⟩ := actual_normalized_bounds hb hB hq hql
  change δ≤q at hqlo
  change q≤B at hqB
  change 0≤u at hu0
  change u≤1 at hu1
  change 0≤t at ht0
  change t≤B*u at htu
  have hq0 : 0<q := lt_of_lt_of_le hδ hqlo
  have hKE : 0≤edgeErrorK B := by unfold edgeErrorK; positivity
  have hKP : 0≤prefactorErrorK B δ := by unfold prefactorErrorK; positivity
  have hP : |P-P₀|≤prefactorErrorK B δ/n :=
    actual_prefactor_first_correction hb hB hδ hq hql hnδ
  have he := actual_edge_first_correction ha hb hd hB hq hn
  have hA : A=((a:ℝ)^2+(d:ℝ)^2)/(2*n)+Q+
      ((a:ℝ)^3+(d:ℝ)^3)/(2*n^2)-((a:ℝ)+d)/(2*n) := by dsimp [A,q,t,u]; ring
  have hE : |E-A|≤edgeErrorK B/n := by
    rw [hA]
    exact he
  have hE0 : 0≤E := by
    dsimp [E]
    apply Finset.sum_nonneg
    intro e he
    cases e using Sym2.inductionOn with
    | _ x y => rw [edgeWeight_formula]; positivity
  have htB : t≤B := by nlinarith
  have hAb : A≤B+Q := by dsimp [A]; linarith
  have hker : edgeErrorK B/n≤edgeErrorK B := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  have hEb : |E|≤B+Q+edgeErrorK B+1 := by
    rw [abs_of_nonneg hE0]
    have hh := (abs_le.mp hE).2
    linarith
  have hi : 1/q≤1/δ := one_div_le_one_div_of_le hδ hqlo
  have hi0 : 0≤1/q := by positivity
  have hδi0 : 0≤1/δ := by positivity
  have hi2 : (1/q)^2≤(1/δ)^2 := by nlinarith only [hi,hi0,hδi0]
  have hui2 := mul_le_mul hu1 hi2 (sq_nonneg (1/q)) (by norm_num : (0:ℝ)≤1)
  have hP₀id : P₀=1+2*(1/q)+2*u*(1/q)^2 := by dsimp [P₀]; ring
  have hLb : |P₀|≤1+2/δ+2/δ^2 := by
    rw [hP₀id,abs_of_nonneg (by positivity)]
    have hid : 1+2/δ+2/δ^2=1+2*(1/δ)+2*(1/δ)^2 := by ring
    rw [hid]
    linarith only [hi,hui2]
  have hcrossid : P₀*A-T=u*(t-u)/q^2 := by dsimp [P₀,A,T]; ring
  have hcross : |P₀*A-T|≤(2*B*(B+1)/δ^2)/n := by
    rw [hcrossid]
    have hh := actual_mixed_remainder hb hB hδ hq hql
    convert hh using 1; ring
  have hh := product_remainder_bound hn0 hKP hKE hP hE hEb hLb hcross
  change |SJ a b d-T|≤combinedErrorK B δ/n
  exact hh
#print axioms actual_SJ_rational_expansion
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END UniformExpansion@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN UniformEndpoint 2038 4b391e92cb30c3363a0682e4b03662823fc1c2caf780b159775f9a42ebfe854f@@
import UniformExpansion
namespace SumBalaban
theorem rational_correction_as_normalized {a d n : ℝ} (hn : 0<n)
    (hS : 0<a^2+d^2) :
    let q := (a^2+d^2)/n
    let u := (a+d)/n
    let t := (a^3+d^3)/n^2
    (1+2/q)*(q/2+Q)+(1+2/q)*(t-u)/2+(2*u/q^2)*(q/2+Q) =
      radialF ((a/Real.sqrt n)^2+(d/Real.sqrt n)^2)+
        (1/Real.sqrt n)*correctionG (a/Real.sqrt n) (d/Real.sqrt n) := by
  dsimp only
  unfold radialF correctionG
  dsimp only
  have hs := Real.sqrt_pos.mpr hn
  have hs2 := Real.sq_sqrt (le_of_lt hn)
  generalize hz : Real.sqrt n=z at *
  rw [←hs2]
  field_simp [ne_of_gt hs,ne_of_gt hS]
  ring

theorem common_uniform_expansion :
    ∃ K : ℝ, 0≤K ∧ ∃ N : ℕ, 1≤N ∧
    ∀ a b d : ℕ, 0<a → 0<b → 0<d → N≤a+b+d →
      (a:ℝ)^2+(d:ℝ)^2≤512*(a+b+d:ℕ) →
      ((a+b+d:ℕ):ℝ)≤1024*((a:ℝ)^2+(d:ℝ)^2) →
      let n : ℝ := (a+b+d:ℕ)
      let x : ℝ := (a:ℝ)/Real.sqrt n
      let y : ℝ := (d:ℝ)/Real.sqrt n
      |SJ a b d-radialF (x^2+y^2)-(1/Real.sqrt n)*correctionG x y|≤K/n := by
  refine ⟨combinedErrorK 512 (1/1024),?_,2^40,by norm_num,?_⟩
  · unfold combinedErrorK prefactorErrorK edgeErrorK
    have := Q_pos
    positivity
  · intro a b d ha hb hd hn hq hql
    have hn0 : (0:ℝ)<(a+b+d:ℕ) := by exact_mod_cast (show 0<a+b+d by omega)
    have hge : (2^40:ℝ)≤(a+b+d:ℕ) := by exact_mod_cast hn
    have hS : (0:ℝ)<(a:ℝ)^2+(d:ℝ)^2 := by positivity
    have he := actual_SJ_rational_expansion ha hb hd
      (by norm_num : (0:ℝ)≤512) (by norm_num : (0:ℝ)<1/1024) hq
      (by nlinarith : (1/1024:ℝ)*(a+b+d:ℕ)≤(a:ℝ)^2+(d:ℝ)^2)
      (by nlinarith : 16*(2*(512:ℝ)+4)≤(a+b+d:ℕ))
      (by nlinarith : 8*(512:ℝ)≤(1/1024:ℝ)^2*(a+b+d:ℕ))
    have hid := rational_correction_as_normalized (a:=(a:ℝ)) (d:=(d:ℝ)) hn0 hS
    dsimp only at he hid ⊢
    rw [hid] at he
    convert he using 1; congr 1; ring
#print axioms rational_correction_as_normalized
#print axioms common_uniform_expansion
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END UniformEndpoint@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN AuditV3 7211 fad0372a192422d9bcf8ac29a6ccc2d0e5b61530da44e7dc2c5674375bdee4c4@@
import UniformEndpoint
import ClusterSelection
#print axioms SumBalaban.angular_cubic
#print axioms SumBalaban.connected
#print axioms SumBalaban.coordinate
#print axioms SumBalaban.coordinate_step
#print axioms SumBalaban.coordinate_walk
#print axioms SumBalaban.coordinate_dist
#print axioms SumBalaban.path_dist_le
#print axioms SumBalaban.path_dist_of_le
#print axioms SumBalaban.left_path_dist
#print axioms SumBalaban.path_right_dist
#print axioms SumBalaban.left_right_dist
#print axioms SumBalaban.left_left_dist
#print axioms SumBalaban.right_right_dist
#print axioms SumBalaban.Vertex
#print axioms SumBalaban.left
#print axioms SumBalaban.path
#print axioms SumBalaban.right
#print axioms SumBalaban.Adj
#print axioms SumBalaban.graph
#print axioms SumBalaban.path_reachable
#print axioms SumBalaban.reachable_from_start
#print axioms SumBalaban.preconnected
#print axioms SumBalaban.degree_as_sum
#print axioms SumBalaban.left_degree
#print axioms SumBalaban.right_degree
#print axioms SumBalaban.path_degree_sum
#print axioms SumBalaban.path_neighbor_count
#print axioms SumBalaban.sum_path_degrees
#print axioms SumBalaban.twice_edge_count
#print axioms SumBalaban.twice_sum_path_orders
#print axioms SumBalaban.twice_left_transmission
#print axioms SumBalaban.vertex_count
#print axioms SumBalaban.cycle_denominator_pos
#print axioms SumBalaban.edgeWeight_formula
#print axioms SumBalaban.edgeClass
#print axioms SumBalaban.edge_class_lt_five
#print axioms SumBalaban.edgeWeight
#print axioms SumBalaban.edgeCount
#print axioms SumBalaban.SJ
#print axioms SumBalaban.Q
#print axioms SumBalaban.c
#print axioms SumBalaban.Q_pos
#print axioms SumBalaban.c_pos
#print axioms SumBalaban.Triple
#print axioms SumBalaban.admissible
#print axioms SumBalaban.objective
#print axioms SumBalaban.minimizes
#print axioms SumBalaban.candidates
#print axioms SumBalaban.minimum_attained
#print axioms SumBalaban.SourceTarget
#print axioms SumBalaban.twice_path_distance_sum
#print axioms SumBalaban.twice_path_transmission
#print axioms SumBalaban.shifted_actual_transmission
#print axioms SumBalaban.edge_count_formula
#print axioms SumBalaban.natural_cycle_formula
#print axioms SumBalaban.reverse_path_sum
#print axioms SumBalaban.twice_right_transmission
#print axioms SumBalaban.real_edge_count_formula
#print axioms SumBalaban.transmission
#print axioms SumBalaban.clique_sum
#print axioms SumBalaban.left_transmission_sum
#print axioms SumBalaban.right_transmission_sum
#print axioms SumBalaban.path_dist
#print axioms SumBalaban.path_transmission_sum
#print axioms SumBalaban.distance_le_order
#print axioms SumBalaban.transmission_le_order_sq
#print axioms SumBalaban.transmission_pos_of_adj
#print axioms SumBalaban.edgeWeight_lower
#print axioms SumBalaban.actual_edge_sum_lower
#print axioms SumBalaban.order_le_edges_add_one
#print axioms SumBalaban.SJ_scaled_lower
#print axioms SumBalaban.edgeCount_le_of_SJ_le
#print axioms SumBalaban.clique_squares_le_twice_edges
#print axioms SumBalaban.sublevel_clique_squares_upper
#print axioms SumBalaban.sublevel_cycle_lower
#print axioms SumBalaban.sublevel_clique_squares_lower
#print axioms SumBalaban.dart_sum_eq_twice_edge_sum
#print axioms SumBalaban.ordered_sum_eq_dart_sum
#print axioms SumBalaban.leftW
#print axioms SumBalaban.rightW
#print axioms SumBalaban.kernel
#print axioms SumBalaban.pathForward
#print axioms SumBalaban.kernel_symm
#print axioms SumBalaban.clique_block
#print axioms SumBalaban.path_block
#print axioms SumBalaban.weight_as_kernel
#print axioms SumBalaban.five_sum_identity
#print axioms SumBalaban.pathLo
#print axioms SumBalaban.pathHi
#print axioms SumBalaban.pathForward_single
#print axioms SumBalaban.actual_path_edge_polynomial
#print axioms SumBalaban.actual_path_pair_error
#print axioms SumBalaban.path_reference_lower
#print axioms SumBalaban.actual_path_pair_lower
#print axioms SumBalaban.inverse_sqrt_error
#print axioms SumBalaban.actual_path_kernel_error
#print axioms SumBalaban.actual_path_sum_error
#print axioms SumBalaban.reference_scaled
#print axioms SumBalaban.transmission_ge_path_sq
#print axioms SumBalaban.edgeWeight_upper
#print axioms SumBalaban.SJ_nonneg
#print axioms SumBalaban.SJ_upper_of_path
#print axioms SumBalaban.balanced_trial_bound
#print axioms SumBalaban.coarseTrial
#print axioms SumBalaban.coarseTrial_admissible
#print axioms SumBalaban.coarseTrial_bound
#print axioms SumBalaban.minimizer_bound
#print axioms SumBalaban.every_minimizer_radial_bounds
#print axioms SumBalaban.normalized_squares
#print axioms SumBalaban.every_minimizer_annulus
#print axioms SumBalaban.leftW_polynomial
#print axioms SumBalaban.rightW_polynomial
#print axioms SumBalaban.left_attachment_argument
#print axioms SumBalaban.right_attachment_argument
#print axioms SumBalaban.polynomial_residual_bounds
#print axioms SumBalaban.actual_clique_arguments_error
#print axioms SumBalaban.radialF
#print axioms SumBalaban.radialQ
#print axioms SumBalaban.radialQ_pos
#print axioms SumBalaban.radial_excess
#print axioms SumBalaban.radial_excess_nonneg
#print axioms SumBalaban.radial_cost_bound
#print axioms SumBalaban.inverse_sqrt_first_correction
#print axioms SumBalaban.actual_clique_four_corrections
#print axioms SumBalaban.prefactor_residual_identity
#print axioms SumBalaban.prefactor_uniform_bound
#print axioms SumBalaban.actual_prefactor_exact
#print axioms SumBalaban.referenceF
#print axioms SumBalaban.reference_phi_lower
#print axioms SumBalaban.referenceF_continuous
#print axioms SumBalaban.referenceF_lipschitz
#print axioms SumBalaban.reference_cell_error
#print axioms SumBalaban.reference_rectangle_error
#print axioms SumBalaban.reference_primitive_derivative
#print axioms SumBalaban.reference_integral_value
#print axioms SumBalaban.reference_left_end_error
#print axioms SumBalaban.reference_right_end_error
#print axioms SumBalaban.reference_moving_interval
#print axioms SumBalaban.actual_reference_rectangle
#print axioms SumBalaban.actual_path_first_correction
#print axioms SumBalaban.weighted_two_error
#print axioms SumBalaban.actualCliqueSum
#print axioms SumBalaban.actual_clique_sum_first_correction
#print axioms SumBalaban.actual_edge_sum_split
#print axioms SumBalaban.actual_edge_first_correction
#print axioms SumBalaban.actual_prefactor_first_correction
#print axioms SumBalaban.optimalTrial
#print axioms SumBalaban.optimal_trial_bounds
#print axioms SumBalaban.optimal_trial_radial_cost
#print axioms SumBalaban.optimal_trial_eventually
#print axioms SumBalaban.correctionG
#print axioms SumBalaban.normalized_product_identity
#print axioms SumBalaban.product_remainder_bound
#print axioms SumBalaban.actual_normalized_bounds
#print axioms SumBalaban.mixed_remainder_bound
#print axioms SumBalaban.actual_mixed_remainder
#print axioms SumBalaban.edgeErrorK
#print axioms SumBalaban.prefactorErrorK
#print axioms SumBalaban.combinedErrorK
#print axioms SumBalaban.actual_SJ_rational_expansion
#print axioms SumBalaban.rational_correction_as_normalized
#print axioms SumBalaban.common_uniform_expansion
#print axioms SumBalaban.source_c_fourth
#print axioms SumBalaban.correction_at_optimal_radius
#print axioms SumBalaban.optimal_cluster_forced_balanced

@@SB335033_LITERAL_SOURCE_V4 END AuditV3@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN TrialLimits 1558 4b18e2f399d0cd61e7594f682ebe86b4b64f2449821f20034ee54efa4951596a@@
import OptimalTrialEventually
import ClusterSelection
import UniformEndpoint
import Mathlib.Topology.Algebra.Order.Field
namespace SumBalaban
open Filter
noncomputable def trialX (n : ℕ) : ℝ := ((optimalTrial n).1:ℝ)/Real.sqrt n

theorem inverse_sqrt_limit : Tendsto (fun n : ℕ => 1/Real.sqrt (n:ℝ)) atTop (nhds 0) := by
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

theorem trial_normalized_limit : Tendsto trialX atTop (nhds c) := by
  have hlow : ∀ᶠ n : ℕ in atTop, c-1/Real.sqrt (n:ℝ) ≤ trialX n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))
    have he := Nat.lt_floor_add_one (c*Real.sqrt (n:ℝ))
    change c-1/Real.sqrt (n:ℝ) ≤ (Nat.floor (c*Real.sqrt (n:ℝ)):ℝ)/Real.sqrt (n:ℝ)
    apply (le_div_iff₀ hs).mpr
    field_simp
    nlinarith
  have hhigh : ∀ᶠ n : ℕ in atTop, trialX n ≤ c := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))
    change (Nat.floor (c*Real.sqrt (n:ℝ)):ℝ)/Real.sqrt (n:ℝ) ≤ c
    exact (div_le_iff₀ hs).mpr (Nat.floor_le (mul_nonneg (le_of_lt c_pos) (Real.sqrt_nonneg _)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub inverse_sqrt_limit) tendsto_const_nhds hlow hhigh
#print axioms trial_normalized_limit
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END TrialLimits@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN TrialExpansion 3543 9f8b7f8fd65e60cf3d9ebef87bc37a0e70d9e13c6a693cc8aa9c52d3a063c82d@@
import TrialLimits
import MinimizerAnnulus
namespace SumBalaban
open Filter

theorem general_uniform_expansion {B δ : ℝ} (hB : 0≤B) (hδ : 0<δ) :
    ∃ K : ℝ, 0≤K ∧ ∃ N : ℕ, 1≤N ∧
    ∀ a b d : ℕ, 0<a → 0<b → 0<d → N≤a+b+d →
      (a:ℝ)^2+(d:ℝ)^2≤B*(a+b+d:ℕ) →
      δ*(a+b+d:ℕ)≤(a:ℝ)^2+(d:ℝ)^2 →
      |SJ a b d-radialF (((a:ℝ)/Real.sqrt (a+b+d:ℕ))^2+
        ((d:ℝ)/Real.sqrt (a+b+d:ℕ))^2)-
        (1/Real.sqrt (a+b+d:ℕ))*correctionG ((a:ℝ)/Real.sqrt (a+b+d:ℕ))
          ((d:ℝ)/Real.sqrt (a+b+d:ℕ))|≤K/(a+b+d:ℕ) := by
  let T : ℝ := 1+16*(2*B+4)+8*B/δ^2
  refine ⟨combinedErrorK B δ, ?_, max 1 (Nat.ceil T), le_max_left _ _, ?_⟩
  · unfold combinedErrorK prefactorErrorK edgeErrorK
    have := Q_pos
    positivity
  · intro a b d ha hb hd hn hq hql
    have hT : T≤((a+b+d:ℕ):ℝ) := le_trans (Nat.le_ceil T)
      (by exact_mod_cast (le_trans (le_max_right 1 (Nat.ceil T)) hn))
    have hn1 : 16*(2*B+4)≤((a+b+d:ℕ):ℝ) := by
      dsimp [T] at hT
      have : 0≤8*B/δ^2 := by positivity
      linarith
    have hn2 : 8*B≤δ^2*((a+b+d:ℕ):ℝ) := by
      have hbound : 8*B/δ^2≤((a+b+d:ℕ):ℝ) := by dsimp [T] at hT; nlinarith
      have := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hbound
      nlinarith
    have he := actual_SJ_rational_expansion ha hb hd hB hδ hq hql hn1 hn2
    have hid := rational_correction_as_normalized
      (a:=(a:ℝ)) (d:=(d:ℝ)) (by positivity : (0:ℝ)<(a+b+d:ℕ))
      (by positivity : (0:ℝ)<(a:ℝ)^2+(d:ℝ)^2)
    dsimp only at he hid
    rw [hid] at he
    convert he using 1
    congr 1
    ring

theorem trial_eventual_expansion :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ n : ℕ in atTop,
      |objective (optimalTrial n)-radialF (2*(trialX n)^2)-
        (1/Real.sqrt (n:ℝ))*correctionG (trialX n) (trialX n)|≤K/(n:ℝ) := by
  have hc := c_pos
  have hq : Tendsto (fun n => 2*(trialX n)^2) atTop (nhds (2*c^2)) :=
    tendsto_const_nhds.mul (trial_normalized_limit.pow 2)
  obtain ⟨K,hK,N,hN,hE⟩ := general_uniform_expansion
    (B:=2*c^2+1) (δ:=c^2) (by positivity) (sq_pos_of_pos hc)
  refine ⟨K,hK,?_⟩
  have hlo : ∀ᶠ n : ℕ in atTop, c^2 < 2*(trialX n)^2 :=
    (tendsto_order.mp hq).1 _ (by nlinarith [sq_pos_of_pos hc])
  have hhi : ∀ᶠ n : ℕ in atTop, 2*(trialX n)^2 < 2*c^2+1 :=
    (tendsto_order.mp hq).2 _ (by linarith)
  filter_upwards [optimal_trial_eventually, hlo, hhi, eventually_ge_atTop N] with n ha hl hu hn
  obtain ⟨ha,hb,hd,hs,had⟩ := ha.1
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hnorm := normalized_squares (optimalTrial n).1 (optimalTrial n).2.2 n hn0
  have heq : (optimalTrial n).2.2=(optimalTrial n).1 := rfl
  rw [heq] at hnorm
  have hnorm2 : 2*(trialX n)^2 = (((optimalTrial n).1:ℝ)^2+((optimalTrial n).1:ℝ)^2)/(n:ℝ) := by
    simpa only [trialX, ←two_mul] using hnorm
  have hupper : ((optimalTrial n).1:ℝ)^2+((optimalTrial n).2.2:ℝ)^2≤(2*c^2+1)*(n:ℝ) := by
    rw [heq]; rw [hnorm2] at hu; exact le_of_lt ((div_lt_iff₀ hnR).mp hu)
  have hlower : c^2*(n:ℝ)≤((optimalTrial n).1:ℝ)^2+((optimalTrial n).2.2:ℝ)^2 := by
    rw [heq]; rw [hnorm2] at hl; exact le_of_lt ((lt_div_iff₀ hnR).mp hl)
  have he := hE _ _ _ ha hb hd (by omega) (by simpa [hs] using hupper) (by simpa [hs] using hlower)
  rw [hs] at he
  simpa only [objective, heq, trialX, ←two_mul] using he
#print axioms general_uniform_expansion
#print axioms trial_eventual_expansion
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END TrialExpansion@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN MinimizerComparison 2622 e5b9576260612c968e0e35f5865b681bbdbce6a64bdda305cc5dc1e76af97778@@
import TrialExpansion
namespace SumBalaban
open Filter
noncomputable def normA (t : Triple) (n : ℕ) : ℝ := (t.1:ℝ)/Real.sqrt n
noncomputable def normD (t : Triple) (n : ℕ) : ℝ := (t.2.2:ℝ)/Real.sqrt n

theorem minimizer_eventual_expansion {f : ℕ → Triple}
    (hf : ∀ᶠ n in atTop, minimizes n (f n)) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ n : ℕ in atTop,
      |objective (f n)-radialF ((normA (f n) n)^2+(normD (f n) n)^2)-
        (1/Real.sqrt (n:ℝ))*correctionG (normA (f n) n) (normD (f n) n)|≤K/(n:ℝ) := by
  obtain ⟨K,hK,N,hN,hE⟩ := common_uniform_expansion
  refine ⟨K,hK,?_⟩
  filter_upwards [hf, eventually_ge_atTop (max N 2048)] with n hm hn
  have ⟨ha,hb,hd,hs,had⟩ := hm.1
  have hn0 : 0<n := by omega
  obtain ⟨_,_,_,_,hl,hu,_⟩ := every_minimizer_annulus (by omega) hm
  have hnorm := normalized_squares (f n).1 (f n).2.2 n hn0
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  rw [hnorm] at hu
  have hl' : (1:ℝ)/1024≤(((f n).1:ℝ)^2+((f n).2.2:ℝ)^2)/(n:ℝ) := by
    simpa only [normA,normD,div_pow,Real.sq_sqrt (le_of_lt hnR),←add_div] using hl
  have he := hE _ _ _ ha hb hd (by omega)
    (by rw [hs]; exact (div_le_iff₀ hnR).mp hu)
    (by rw [hs]; have := (le_div_iff₀ hnR).mp hl'; nlinarith)
  rw [hs] at he
  exact he

theorem comparison_algebra {n x y u K L S T : ℝ} (hn : 0<n)
    (hq : 0<x^2+y^2)
    (hS : |S-radialF (x^2+y^2)-(1/Real.sqrt n)*correctionG x y|≤K/n)
    (hT : |T-radialF (2*u^2)-(1/Real.sqrt n)*correctionG u u|≤L/n)
    (hcost : radialF (2*u^2)-radialF radialQ≤16/n) (hmin : S≤T) :
    radialF (x^2+y^2) ≤ radialF (2*u^2)+(1/Real.sqrt n)*(correctionG u u-correctionG x y)+(K+L)/n ∧
    correctionG x y ≤ correctionG u u+(16+K+L)/Real.sqrt n := by
  have hs := Real.sqrt_pos.mpr hn
  have hs2 := Real.sq_sqrt (le_of_lt hn)
  obtain ⟨hSl,hSu⟩ := abs_le.mp hS
  obtain ⟨hTl,hTu⟩ := abs_le.mp hT
  have hrad := radial_excess_nonneg hq
  constructor
  · have heq : (K+L)/n=K/n+L/n := by ring
    rw [heq]
    nlinarith
  · have hmul : (1/Real.sqrt n)*(correctionG x y-correctionG u u)≤(16+K+L)/n := by
      have heq : (16+K+L)/n=16/n+K/n+L/n := by ring
      rw [heq]
      nlinarith
    have he := mul_le_mul_of_nonneg_right hmul (le_of_lt hs)
    have hid1 : (1/Real.sqrt n)*(correctionG x y-correctionG u u)*Real.sqrt n = correctionG x y-correctionG u u := by field_simp
    have hid2 : (16+K+L)/n*Real.sqrt n=(16+K+L)/Real.sqrt n := by
      field_simp
      rw [hs2]
    rw [hid1,hid2] at he
    linarith
#print axioms minimizer_eventual_expansion
#print axioms comparison_algebra
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END MinimizerComparison@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN EventualComparison 1234 4a2f31bc1d44dec54893beade6ee5f0cb7ecb3eecf7d74b979f6a3df35b29b75@@
import MinimizerComparison
namespace SumBalaban
open Filter

theorem minimizer_eventual_comparison {f : ℕ → Triple}
    (hf : ∀ᶠ n in atTop, minimizes n (f n)) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      radialF ((normA (f n) n)^2+(normD (f n) n)^2) ≤
        radialF (2*(trialX n)^2)+(1/Real.sqrt (n:ℝ))*
          (correctionG (trialX n) (trialX n)-correctionG (normA (f n) n) (normD (f n) n))+C/(n:ℝ) ∧
      correctionG (normA (f n) n) (normD (f n) n) ≤
        correctionG (trialX n) (trialX n)+(16+C)/Real.sqrt (n:ℝ) := by
  obtain ⟨K,hK,hE⟩ := minimizer_eventual_expansion hf
  obtain ⟨L,hL,hT⟩ := trial_eventual_expansion
  refine ⟨K+L,?_⟩
  filter_upwards [hf,hE,hT,optimal_trial_eventually,eventually_ge_atTop 2048] with n hm he ht htrial hn
  have hr := every_minimizer_annulus hn hm
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hq : 0<(normA (f n) n)^2+(normD (f n) n)^2 := by
    have hh := hr.2.2.2.2.1
    change (1:ℝ)/1024≤(normA (f n) n)^2+(normD (f n) n)^2 at hh
    linarith
  have hcomp := comparison_algebra hnR hq he ht htrial.2 (hm.2 _ htrial.1)
  simpa only [add_assoc] using hcomp

#print axioms minimizer_eventual_comparison
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END EventualComparison@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN MinimizingCluster 4240 ad40dd4b1e590190b84952749ae7049d69e3e96586f2daa5f878f0f8d70ac6b3@@
import EventualComparison
import Mathlib.Tactic.FunProp
namespace SumBalaban
open Filter

theorem correction_limit {α : Type*} {l : Filter α} {u v : α → ℝ} {x y : ℝ}
    (hu : Tendsto u l (nhds x)) (hv : Tendsto v l (nhds y)) (hq : 0<x^2+y^2) :
    Tendsto (fun i => correctionG (u i) (v i)) l (nhds (correctionG x y)) := by
  unfold correctionG
  dsimp only
  have hqq := (hu.pow 2).add (hv.pow 2)
  exact (((hqq.add_const 2).mul ((hu.pow 3).add (hv.pow 3))).div
    (tendsto_const_nhds.mul hqq) (by positivity)).add
    ((hu.add hv).mul (tendsto_const_nhds.add
      (tendsto_const_nhds.div (hqq.pow 2) (by positivity))))

theorem radial_limit {α : Type*} {l : Filter α} {q : α → ℝ} {r : ℝ}
    (hq : Tendsto q l (nhds r)) (hr : 0<r) :
    Tendsto (fun i => radialF (q i)) l (nhds (radialF r)) := by
  unfold radialF
  exact (((hq.div_const 2).add_const 1).add_const Q).add
    (tendsto_const_nhds.div hq (ne_of_gt hr))

theorem minimizing_cluster_balanced {f : ℕ → Triple}
    (hf : ∀ᶠ n in atTop, minimizes n (f n)) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) {x y : ℝ}
    (hx : Tendsto (fun i => normA (f (φ i)) (φ i)) atTop (nhds x))
    (hy : Tendsto (fun i => normD (f (φ i)) (φ i)) atTop (nhds y)) :
    x=c ∧ y=c := by
  have ha : ∀ᶠ n : ℕ in atTop,
      0≤normA (f n) n ∧ 0≤normD (f n) n ∧
      (1:ℝ)/1024≤(normA (f n) n)^2+(normD (f n) n)^2 := by
    filter_upwards [hf,eventually_ge_atTop 2048] with n hn hN
    obtain ⟨h1,_,h2,_,h3,_,_⟩ := every_minimizer_annulus hN hn
    exact ⟨h1,h2,h3⟩
  have hseq := hφ.eventually ha
  have hx0 : 0≤x := ge_of_tendsto hx (hseq.mono fun _ h => h.1)
  have hy0 : 0≤y := ge_of_tendsto hy (hseq.mono fun _ h => h.2.1)
  have hqseq := (hx.pow 2).add (hy.pow 2)
  have hql : (1:ℝ)/1024≤x^2+y^2 := ge_of_tendsto hqseq (hseq.mono fun _ h => h.2.2)
  have hq : 0<x^2+y^2 := by linarith
  have hG := correction_limit hx hy hq
  have ht := trial_normalized_limit.comp hφ
  have hcq : 0<c^2+c^2 := by have := c_pos; positivity
  have hGt := correction_limit ht ht hcq
  have hqt : Tendsto (fun i => 2*(trialX (φ i))^2) atTop (nhds (2*c^2)) :=
    tendsto_const_nhds.mul (ht.pow 2)
  have hFt := radial_limit hqt (by have := c_pos; positivity)
  have hF := radial_limit hqseq hq
  have he := inverse_sqrt_limit.comp hφ
  have hinv : Tendsto (fun i => 1/(φ i:ℝ)) atTop (nhds 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hφ)
  obtain ⟨C,hcomp⟩ := minimizer_eventual_comparison hf
  have hcomp' := hφ.eventually hcomp
  have hright := hFt.add ((he.mul (hGt.sub hG)).add ((tendsto_const_nhds (x:=C)).mul hinv))
  have hright' : Tendsto (fun i => radialF (2*(trialX (φ i))^2)+
      (1/Real.sqrt (φ i:ℝ))*(correctionG (trialX (φ i)) (trialX (φ i))-
        correctionG (normA (f (φ i)) (φ i)) (normD (f (φ i)) (φ i)))+C/(φ i:ℝ))
      atTop (nhds (radialF (2*c^2))) := by
    simpa only [zero_mul,mul_zero,add_zero,div_eq_mul_inv,one_div,add_assoc,Function.comp_def,one_mul] using hright
  have hrad : radialF (x^2+y^2)≤radialF (2*c^2) :=
    le_of_tendsto_of_tendsto hF hright' (hcomp'.mono fun _ h => h.1)
  have hq0 : radialQ=2*c^2 := by unfold radialQ c; rw [Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mpr Q_pos))]
  have hrad0 : radialF (x^2+y^2)-radialF radialQ≤0 := by rw [hq0]; linarith
  rw [radial_excess hq] at hrad0
  have hzero : (x^2+y^2-radialQ)^2=0 := by
    have := (div_le_iff₀ (show 0<2*(x^2+y^2) by positivity)).mp hrad0
    nlinarith [sq_nonneg (x^2+y^2-radialQ)]
  have hqr : x^2+y^2=2*c^2 := by rw [sq_eq_zero_iff] at hzero; rw [←hq0]; linarith
  have hrightG : Tendsto (fun i => correctionG (trialX (φ i)) (trialX (φ i))+
      (16+C)/Real.sqrt (φ i:ℝ)) atTop (nhds (correctionG c c)) := by
    simpa only [mul_zero,add_zero,div_eq_mul_inv,one_div,Function.comp_def,one_mul] using
      hGt.add ((tendsto_const_nhds (x:=16+C)).mul he)
  have hGl := le_of_tendsto_of_tendsto hG hrightG (hcomp'.mono fun _ h => h.2)
  exact optimal_cluster_forced_balanced hx0 hy0 hqr hGl
#print axioms correction_limit
#print axioms radial_limit
#print axioms minimizing_cluster_balanced
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END MinimizingCluster@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN SourceEndpoint 3292 7492d25a0675f686440df8912ec0ef0f6c69065beac1a3a3cfe14e4222986080@@
import MinimizingCluster
import Mathlib.Topology.Sequences
namespace SumBalaban
open Filter
set_option maxHeartbeats 800000

theorem every_minimizer_pair_limit {f : ℕ → Triple}
    (hf : ∀ᶠ n in atTop, minimizes n (f n)) :
    Tendsto (fun n => (normA (f n) n,normD (f n) n)) atTop (nhds (c,c)) := by
  let z : ℕ → ℝ × ℝ := fun n => (normA (f n) n,normD (f n) n)
  have hbox : ∀ᶠ n in atTop, z n ∈ (Set.Icc (0:ℝ) 32) ×ˢ (Set.Icc (0:ℝ) 32) := by
    filter_upwards [hf,eventually_ge_atTop 2048] with n hm hn
    obtain ⟨h1,h2,h3,h4,_,_,_⟩ := every_minimizer_annulus hn hm
    exact ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hbad
  have hfreq : ∃ᶠ n in atTop, ε≤dist (z n) (c,c) := by
    simpa only [not_lt] using (not_eventually.mp hbad)
  let S : Set (ℝ × ℝ) := ((Set.Icc (0:ℝ) 32) ×ˢ (Set.Icc (0:ℝ) 32)) ∩
    {p | ε≤dist p (c,c)}
  have hcompact : IsCompact S :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hfreqS : ∃ᶠ n in atTop, z n ∈ S := by
    exact (hfreq.and_eventually hbox).mono fun n hn => ⟨hn.2,hn.1⟩
  obtain ⟨p,hp,φ,hφ,hlim⟩ := hcompact.tendsto_subseq' hfreqS
  have hA : Tendsto (fun i => normA (f (φ i)) (φ i)) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hlim
  have hD : Tendsto (fun i => normD (f (φ i)) (φ i)) atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hlim
  have hbalance := minimizing_cluster_balanced hf hφ.tendsto_atTop hA hD
  have hp0 : p=(c,c) := Prod.ext hbalance.1 hbalance.2
  have hh : ε≤dist p (c,c) := hp.2
  rw [hp0,dist_self] at hh
  linarith

theorem every_minimizer_radial_limit {f : ℕ → Triple}
    (hf : ∀ᶠ n in atTop, minimizes n (f n)) :
    Tendsto (fun n => (normA (f n) n)^2+(normD (f n) n)^2) atTop (nhds radialQ) := by
  have h := every_minimizer_pair_limit hf
  have hq0 : radialQ=c^2+c^2 := by
    unfold radialQ c
    rw [Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mpr Q_pos))]
    ring
  rw [hq0]
  exact (((continuous_fst.tendsto (c,c)).comp h).pow 2).add
    (((continuous_snd.tendsto (c,c)).comp h).pow 2)

theorem source_target : SourceTarget := by
  intro f hf
  have hpair := every_minimizer_pair_limit hf
  have hA : Tendsto (fun n => normA (f n) n) atTop (nhds c) :=
    (continuous_fst.tendsto (c,c)).comp hpair
  have hD : Tendsto (fun n => normD (f n) n) atTop (nhds c) :=
    (continuous_snd.tendsto (c,c)).comp hpair
  refine ⟨hA,hD,?_⟩
  have hsmall := (hA.add hD).mul inverse_sqrt_limit
  have hlim : Tendsto (fun n => 1-(normA (f n) n+normD (f n) n)*(1/Real.sqrt (n:ℝ)))
      atTop (nhds 1) := by
    simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub hsmall
  apply hlim.congr'
  filter_upwards [hf,eventually_ge_atTop 1] with n hm hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hs := Real.sqrt_pos.mpr hn0
  have hs2 := Real.sq_sqrt (le_of_lt hn0)
  have hsum : ((f n).1:ℝ)+((f n).2.1:ℝ)+((f n).2.2:ℝ)=(n:ℝ) := by exact_mod_cast hm.1.2.2.2.1
  dsimp only [normA,normD]
  field_simp
  nlinarith [hs2]
#print axioms every_minimizer_pair_limit
#print axioms every_minimizer_radial_limit
#print axioms source_target
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END SourceEndpoint@@

@@SB335033_LITERAL_SOURCE_V4 BEGIN AuditV4 1202 972f3bba8bbbecd5325f17f4cdc69986409eef7df760962c4b45fafa84d8fd66@@
import SourceEndpoint
import AuditV3
namespace SumBalaban
-- Expanded endpoint: no selection, annulus, expansion, or convergence hypotheses.
theorem all_eventually_minimizing_choices :
    ∀ f : ℕ → Triple, (∀ᶠ n in Filter.atTop, minimizes n (f n)) →
    Filter.Tendsto (fun n => ((f n).1:ℝ)/Real.sqrt n) Filter.atTop (nhds c) ∧
    Filter.Tendsto (fun n => ((f n).2.2:ℝ)/Real.sqrt n) Filter.atTop (nhds c) ∧
    Filter.Tendsto (fun n => ((f n).2.1:ℝ)/(n:ℝ)) Filter.atTop (nhds 1) := source_target
#print SourceTarget
#print all_eventually_minimizing_choices
#print axioms all_eventually_minimizing_choices
#print axioms source_target
#print axioms every_minimizer_pair_limit
#print axioms every_minimizer_radial_limit
#print axioms minimizing_cluster_balanced
#print axioms minimizer_eventual_comparison
#print axioms minimizer_eventual_expansion
#print axioms comparison_algebra
#print axioms trial_eventual_expansion
#print axioms general_uniform_expansion
#print axioms trial_normalized_limit
#print axioms inverse_sqrt_limit
#print axioms common_uniform_expansion
#print axioms optimal_cluster_forced_balanced
#print axioms SJ
#print axioms minimum_attained
end SumBalaban

@@SB335033_LITERAL_SOURCE_V4 END AuditV4@@
