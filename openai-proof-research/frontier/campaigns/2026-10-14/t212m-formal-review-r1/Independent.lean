import T212M
import Controls
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/- Independent reviewer checks for the frozen T212M scoped support. MIT.
Reviewer-written. Imports the author modules only to pin and instantiate their
exact elaborated statements. Nothing here is a probabilistic or FPP statement. -/
namespace T212MReview

open T212M

/-! ## Statement pinning
Each `example` restates an author declaration with explicitly written binders;
it typechecks only if the author type has at least this meaning. -/

section Pin

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

example (F : Finset (Sym2 V)) (w w' : Sym2 V → ℝ) :
    changeBudget F w w' = ∑ e ∈ F, |w' e - w e| := rfl

/-- Walk cost counts every traversal of an edge, with multiplicity. -/
example (w : Sym2 V → ℝ) {a b : V} (p : G.Walk a b) :
    walkCost w p = (p.edges.map w).sum := rfl

example (w : Sym2 V → ℝ) {u v b : V} (h : G.Adj u v) (q : G.Walk v b) :
    walkCost w (SimpleGraph.Walk.cons h q) = w s(u, v) + walkCost w q := by
  simp [walkCost]

/-- Pin of the final all-walk theorem, with every hypothesis written out. -/
example (d : V → V → ℝ) (hsym : ∀ u v, d u v = d v u)
    (htri : ∀ u v z, d u z ≤ d u v + d v z)
    (w w' : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (hw' : ∀ e, 0 ≤ w' e)
    (F : Finset (Sym2 V)) (hoff : ∀ e, e ∉ F → w' e = w e)
    (hdom : ∀ u v (p : G.Walk u v), d u v ≤ walkCost w p)
    (x : V) (ray : ℕ → V) (segments : ∀ i j, G.Walk (ray i) (ray j))
    (hsegments : ∀ i j, i ≤ j → walkCost w (segments i j) = d (ray i) (ray j))
    (hcal : ∀ i j, i ≤ j → d x (ray j) = d x (ray i) + d (ray i) (ray j))
    (hescape : ∀ B : ℝ, ∃ N : ℕ, ∀ n, N ≤ n → B < d x (ray n))
    (C : ℝ) (hregion : ∀ e ∈ F, ∃ c ∈ e, d x c ≤ C) :
    ∃ N : ℕ, ∀ i j, N ≤ i → i ≤ j → ∀ p : G.Walk (ray i) (ray j),
      walkCost w' (segments i j) ≤ walkCost w' p := by
  obtain ⟨N, hN⟩ := ray_tail_stable_all_walks d hsym htri w w' hw hw' F hoff
    (fun p => hdom _ _ p) x ray segments hsegments hcal hescape C hregion
  exact ⟨N, fun i j hi hij p => hN i hi j hij p⟩

/-- Pin of the intermediate theorem: no nonnegativity of the new weights. -/
example (d : V → V → ℝ) (hsym : ∀ u v, d u v = d v u)
    (htri : ∀ u v z, d u z ≤ d u v + d v z)
    (w w' : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (F : Finset (Sym2 V)) (hoff : ∀ e, e ∉ F → w' e = w e)
    (hdom : ∀ u v (p : G.Walk u v), d u v ≤ walkCost w p)
    (x : V) (ray : ℕ → V) (segments : ∀ i j, G.Walk (ray i) (ray j))
    (hsegments : ∀ i j, i ≤ j → walkCost w (segments i j) = d (ray i) (ray j))
    (hcal : ∀ i j, i ≤ j → d x (ray j) = d x (ray i) + d (ray i) (ray j))
    (hescape : ∀ B : ℝ, ∃ N : ℕ, ∀ n, N ≤ n → B < d x (ray n))
    (C : ℝ) (hregion : ∀ e ∈ F, ∃ c ∈ e, d x c ≤ C) :
    ∃ N : ℕ, ∀ i j, N ≤ i → i ≤ j → ∀ p : G.Walk (ray i) (ray j), p.edges.Nodup →
      walkCost w' (segments i j) ≤ walkCost w' p := by
  obtain ⟨N, hN⟩ := ray_tail_stable d hsym htri w w' hw F hoff
    (fun p => hdom _ _ p) x ray segments hsegments hcal hescape C hregion
  exact ⟨N, fun i j hi hij p hp => hN i hi j hij p hp⟩

/-- Pin of the toll inequality, with the strict-detour reading. -/
example (d : V → V → ℝ) (hsym : ∀ u v, d u v = d v u)
    (htri : ∀ u v z, d u z ≤ d u v + d v z)
    (w w' : Sym2 V → ℝ) (F : Finset (Sym2 V)) (hoff : ∀ e, e ∉ F → w' e = w e)
    (hdom : ∀ u v (p : G.Walk u v), d u v ≤ walkCost w p)
    (x a b c : V) (C : ℝ) (hc : d x c ≤ C) (hcal : d x b = d x a + d a b)
    (p : G.Walk a b) (hp : p.edges.Nodup) (hvisit : c ∈ p.support) :
    d a b + 2 * d x a - 2 * C - changeBudget F w w' ≤ walkCost w' p :=
  detour_barrier d hsym htri w w' F hoff (fun p => hdom _ _ p) C hc hcal p hp hvisit

end Pin

/-! ## Derived corollaries from the public lemmas -/

section Derived

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- The region hypothesis is never restrictive for a finite change set:
some finite `C` always works, for any root and any real `d`. -/
theorem region_constant_exists (d : V → V → ℝ) (x : V) (F : Finset (Sym2 V)) :
    ∃ C : ℝ, ∀ e ∈ F, ∃ c ∈ e, d x c ≤ C := by
  refine ⟨∑ e ∈ F, |d x e.out.1|, fun e he => ⟨e.out.1, Sym2.out_fst_mem e, ?_⟩⟩
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun e => |d x e.out.1|) (fun _ _ => abs_nonneg _) he)

/-- Uniform metric-threshold form: one threshold `C + Δ/2` in root distance,
independent of any ray or index, gives all-walk minimality of a calibrated
original geodesic segment. Avoidance is derived, not assumed. -/
theorem uniform_late_segment_all_walks (d : V → V → ℝ) (hsym : ∀ u v, d u v = d v u)
    (htri : ∀ u v z, d u z ≤ d u v + d v z)
    (w w' : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (hw' : ∀ e, 0 ≤ w' e)
    (F : Finset (Sym2 V)) (hoff : ∀ e, e ∉ F → w' e = w e)
    (hdom : ∀ {u v} (p : G.Walk u v), d u v ≤ walkCost w p)
    {x a b : V} (C : ℝ) (hregion : ∀ e ∈ F, ∃ c ∈ e, d x c ≤ C)
    (hcal : d x b = d x a + d a b) (hlate : C + changeBudget F w w' / 2 < d x a)
    (segment : G.Walk a b) (hsegment : walkCost w segment = d a b)
    (p : G.Walk a b) : walkCost w' segment ≤ walkCost w' p := by
  have hdelta : 0 ≤ changeBudget F w w' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have havoid := calibrated_segment_avoids d htri w hw hdom F C hregion hcal
    (by linarith) segment hsegment
  exact (late_segment_minimizes d hsym htri w w' F hoff hdom C hregion hcal hlate
    segment hsegment havoid p.bypass p.bypass_isPath.isTrail.edges_nodup).trans
    (bypass_cost_le w' hw' p)

end Derived

/-! ## Infinite-graph nonvacuity of the two tail theorems
Complete graph on ℕ, weights and distance |u - v|, root 0, ray n = n,
segments are single edges, and the edge {0,1} is lowered from 1 to 1/2.
The escape hypothesis cannot hold on a graph with bounded `d`, so the author
controls on `Fin 4` do not instantiate `ray_tail_stable`; this section does. -/

section Line

abbrev K : SimpleGraph ℕ := ⊤

noncomputable def dist (u v : ℕ) : ℝ := |(u : ℝ) - (v : ℝ)|

noncomputable def wt : Sym2 ℕ → ℝ :=
  Sym2.lift ⟨dist, fun u v => abs_sub_comm (u : ℝ) (v : ℝ)⟩

def F : Finset (Sym2 ℕ) := {s(0, 1)}

noncomputable def wtHalf (e : Sym2 ℕ) : ℝ := if e ∈ F then 1 / 2 else wt e

noncomputable def wtNeg (e : Sym2 ℕ) : ℝ := if e ∈ F then -1 else wt e

def seg (i j : ℕ) : K.Walk i j :=
  if h : i = j then SimpleGraph.Walk.nil.copy rfl h
  else SimpleGraph.Walk.cons (by simpa using h) SimpleGraph.Walk.nil

theorem dist_symm (u v : ℕ) : dist u v = dist v u := abs_sub_comm _ _

theorem dist_tri (u v z : ℕ) : dist u z ≤ dist u v + dist v z := abs_sub_le _ _ _

theorem wt_mk (u v : ℕ) : wt s(u, v) = dist u v := rfl

theorem wt_nonneg (e : Sym2 ℕ) : 0 ≤ wt e := by
  induction e using Sym2.inductionOn with
  | _ u v => exact abs_nonneg _

theorem wt_dom {u v : ℕ} (p : K.Walk u v) : dist u v ≤ walkCost wt p :=
  distance_dominated_by_cost dist (fun u => by simp [dist]) dist_tri wt
    (fun _ _ _ => le_rfl) p

theorem seg_cost (i j : ℕ) : walkCost wt (seg i j) = dist i j := by
  unfold seg
  split_ifs with h
  · subst h; simp [walkCost, dist]
  · simp [walkCost, wt_mk]

theorem line_cal (i j : ℕ) (h : i ≤ j) : dist 0 j = dist 0 i + dist i j := by
  have hij : (i : ℝ) ≤ j := by exact_mod_cast h
  simp only [dist, Nat.cast_zero, zero_sub, abs_neg, Nat.abs_cast]
  rw [abs_of_nonpos (by linarith)]
  ring

theorem line_escape (B : ℝ) : ∃ N : ℕ, ∀ n, N ≤ n → B < dist 0 n := by
  obtain ⟨N, hN⟩ := exists_nat_gt B
  refine ⟨N, fun n hn => ?_⟩
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  simp only [dist, Nat.cast_zero, zero_sub, abs_neg, Nat.abs_cast]
  linarith

theorem line_region : ∀ e ∈ F, ∃ c ∈ e, dist 0 c ≤ 0 := by
  intro e he
  rw [F, Finset.mem_singleton] at he
  subst he
  exact ⟨0, Sym2.mem_mk_left 0 1, by simp [dist]⟩

theorem half_off : ∀ e, e ∉ F → wtHalf e = wt e := fun e he => by simp [wtHalf, he]

theorem neg_off : ∀ e, e ∉ F → wtNeg e = wt e := fun e he => by simp [wtNeg, he]

theorem half_nonneg (e : Sym2 ℕ) : 0 ≤ wtHalf e := by
  unfold wtHalf; split_ifs
  · norm_num
  · exact wt_nonneg e

/-- The modification is genuine: the changed edge lies on the original ray
(it is `seg 0 1`) and the budget is positive. -/
theorem half_change_genuine :
    wtHalf s(0, 1) ≠ wt s(0, 1) ∧ changeBudget F wt wtHalf = 1 / 2 ∧
      (seg 0 1).edges = [s(0, 1)] := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [wtHalf, F, wt_mk, dist]
  · norm_num [changeBudget, F, wtHalf, wt_mk, dist]
  · simp [seg]

/-- Nonvacuity of the final all-walk tail theorem on an infinite graph. -/
theorem all_walks_instance :
    ∃ N : ℕ, ∀ i, N ≤ i → ∀ j, i ≤ j →
      ∀ p : K.Walk i j, walkCost wtHalf (seg i j) ≤ walkCost wtHalf p :=
  ray_tail_stable_all_walks (ray := fun n => n) dist dist_symm dist_tri wt wtHalf
    wt_nonneg half_nonneg F half_off wt_dom 0 seg (fun i j _ => seg_cost i j)
    line_cal line_escape 0 line_region

/-- The intermediate theorem genuinely needs no new-weight nonnegativity:
it applies with a negative new weight on the changed edge. -/
theorem edge_simple_instance_negative_weight :
    ∃ N : ℕ, ∀ i, N ≤ i → ∀ j, i ≤ j →
      ∀ p : K.Walk i j, p.edges.Nodup → walkCost wtNeg (seg i j) ≤ walkCost wtNeg p :=
  ray_tail_stable (ray := fun n => n) dist dist_symm dist_tri wt wtNeg
    wt_nonneg F neg_off wt_dom 0 seg (fun i j _ => seg_cost i j)
    line_cal line_escape 0 line_region

/-! ## Hypothesis-deletion controls -/

/-- Back-and-forth traversals of the changed edge, `k` times. -/
noncomputable def loop : ℕ → K.Walk 0 0
  | 0 => SimpleGraph.Walk.nil
  | k + 1 => SimpleGraph.Walk.cons (v := 1) (by decide)
      (SimpleGraph.Walk.cons (v := 0) (by decide) (loop k))

theorem loop_cost (k : ℕ) : walkCost wtNeg (loop k) = -2 * k := by
  induction k with
  | zero => simp [loop, walkCost]
  | succ k ih =>
    have h10 : s(1, 0) = s(0, 1) := Sym2.eq_swap
    simp only [walkCost, loop, SimpleGraph.Walk.edges_cons, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]
    simp [wtNeg, F, h10]
    ring

noncomputable def detour (i k : ℕ) (hi : i ≠ 0) : K.Walk i i :=
  SimpleGraph.Walk.cons (v := 0) (by simpa using hi)
    ((loop k).append (SimpleGraph.Walk.cons (v := i) (by simpa using hi.symm)
      SimpleGraph.Walk.nil))

theorem detour_cost (i k : ℕ) (hi : 2 ≤ i) :
    walkCost wtNeg (detour i k (by omega)) = 2 * i - 2 * k := by
  have hF : s(i, 0) ∉ F := by
    simp [F]; omega
  have hF' : s(0, i) ∉ F := by
    simp [F]; omega
  have hloop := loop_cost k
  simp only [detour, walkCost, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_append,
    List.map_cons, List.map_append, List.sum_cons, List.sum_append] at hloop ⊢
  rw [hloop]
  simp [wtNeg, hF, hF', wt_mk, dist]
  ring

/-- Deleting new-weight nonnegativity from the all-walk theorem is fatal:
with every other hypothesis proved above (`wt_nonneg`, `neg_off`, `wt_dom`,
`seg_cost`, `line_cal`, `line_escape`, `line_region`), the conclusion fails. -/
theorem all_walks_needs_new_nonneg :
    ¬ ∃ N : ℕ, ∀ i, N ≤ i → ∀ j, i ≤ j →
      ∀ p : K.Walk i j, walkCost wtNeg (seg i j) ≤ walkCost wtNeg p := by
  rintro ⟨N, hN⟩
  have h := hN (N + 2) (by omega) (N + 2) le_rfl (detour (N + 2) (N + 3) (by omega))
  rw [detour_cost (N + 2) (N + 3) (by omega)] at h
  have hseg : walkCost wtNeg (seg (N + 2) (N + 2)) = 0 := by simp [seg, walkCost]
  rw [hseg] at h
  push_cast at h
  linarith

/-- Deleting lateness from `late_segment_minimizes` is fatal: on the same
infinite graph, the unchanged original geodesic edge 0-2 satisfies every other
hypothesis but loses to the edge-simple shortcut 0-1-2. -/
def shortcut : K.Walk 0 2 :=
  SimpleGraph.Walk.cons (v := 1) (by decide)
    (SimpleGraph.Walk.cons (v := 2) (by decide) SimpleGraph.Walk.nil)

theorem lateness_needed :
    (dist 0 2 = dist 0 0 + dist 0 2) ∧
    walkCost wt (seg 0 2) = dist 0 2 ∧
    (∀ e ∈ (seg 0 2).edges, e ∉ F) ∧
    shortcut.edges.Nodup ∧
    ¬ (0 + changeBudget F wt wtHalf / 2 < dist 0 0) ∧
    walkCost wtHalf shortcut < walkCost wtHalf (seg 0 2) := by
  have h02 : s(0, 2) ∉ F := by simp [F]
  refine ⟨by simp [dist], seg_cost 0 2, ?_, ?_, ?_, ?_⟩
  · intro e he; simp [seg] at he; subst he; exact h02
  · simp [shortcut]
  · rw [half_change_genuine.2.1]; norm_num [dist]
  · norm_num [shortcut, seg, walkCost, wtHalf, F, wt_mk, dist]

/-- Deleting `Nodup` from `walk_cost_change` is fatal on the same instance. -/
def repeated : K.Walk 0 1 :=
  SimpleGraph.Walk.cons (v := 1) (by decide)
    (SimpleGraph.Walk.cons (v := 0) (by decide)
      (SimpleGraph.Walk.cons (v := 1) (by decide) SimpleGraph.Walk.nil))

theorem budget_needs_nodup :
    ¬ (repeated.edges.Nodup) ∧
    ¬ |walkCost wtHalf repeated - walkCost wt repeated| ≤ changeBudget F wt wtHalf := by
  have h10 : s(1, 0) = s(0, 1) := Sym2.eq_swap
  refine ⟨by simp [repeated, h10], ?_⟩
  rw [half_change_genuine.2.1]
  simp [repeated, walkCost, wtHalf, F, h10, wt_mk, dist]
  norm_num

end Line

end T212MReview

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for modName in [`T212M, `Controls] do
    let some idx := env.getModuleIdx? modName | throwError m!"module {modName} missing"
    let mut names : Array Name := #[]
    for (n, _) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some idx then
        names := names.push n
    names := names.qsort (fun a b => a.toString < b.toString)
    IO.println s!"MODULE {modName} constants={names.size}"
    for n in names do
      let some ci := env.find? n | throwError m!"lost {n}"
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .axiomInfo _ => "AXIOM"
        | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
      let unsafeFlag := if ci.isUnsafe then " UNSAFE" else ""
      let axs ← Lean.collectAxioms n
      let bad := axs.toList.filter (fun a => !standard.contains a)
      let inst := if Meta.isInstanceCore env n then " instance" else ""
      let internal := if n.isInternal then " internal" else ""
      IO.println s!"  {n} kind={kind}{inst}{internal}{unsafeFlag} axioms={axs.toList} bad={bad}"
      if !bad.isEmpty then throwError m!"nonstandard axiom in {n}: {bad}"
      if kind == "AXIOM" || kind == "opaque" then throwError m!"axiom/opaque declared: {n}"
      if ci.isUnsafe then throwError m!"declaration marked isUnsafe: {n}"
  let mut mine : Array Name := #[]
  for (n, _) in env.constants.map₂.toList do
    if (`T212MReview).isPrefixOf n then mine := mine.push n
  mine := mine.qsort (fun a b => a.toString < b.toString)
  IO.println s!"REVIEWER constants={mine.size}"
  for n in mine do
    let some ci := env.find? n | throwError m!"lost {n}"
    let axs ← Lean.collectAxioms n
    let bad := axs.toList.filter (fun a => !standard.contains a)
    IO.println s!"  {n} axioms={axs.toList} bad={bad}"
    if !bad.isEmpty then throwError m!"nonstandard axiom in {n}: {bad}"
    if ci.isUnsafe then throwError m!"reviewer declaration marked isUnsafe: {n}"
  IO.println "INDEPENDENT_INVENTORY_PASS"
