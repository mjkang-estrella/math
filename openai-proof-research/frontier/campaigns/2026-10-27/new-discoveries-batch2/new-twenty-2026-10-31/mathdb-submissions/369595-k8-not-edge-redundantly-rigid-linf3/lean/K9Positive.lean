import LinfBridge
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.FinRange

/-!
# `K₉` is edge-redundantly rigid in `ℓ∞³`

An explicit integer placement (found by the author's exact LP search, checked
independently by the reviewer) is an edge-redundantly rigid framework in the
sense of the source definitions.  This shows that the definitions of
`CdkDefs` are not vacuous, and that `n = 2d + 2 = 8` is the only failure of
Conjecture 5.4 at `d = 3` up to `n = 9` (the extension to all `n ≥ 9` is proved
on paper only).

* every pair of points has a unique dominant coordinate, given by `colT`
  (`domZ_colT`, kernel evaluation over the integers);
* every colour class stays connected after deleting any single edge
  (`conn_check`, kernel evaluation of a reachability iteration);
* translations are infinitesimal rigid motions.
-/

namespace CDK.K9

open K8

/-- The placement, integer coordinates. -/
def P9 : Fin 9 → Fin 3 → ℤ :=
  ![![13, 5, 10], ![15, -3, 16], ![-2, -8, 7], ![19, -9, 12], ![-1, -11, 8], ![7, 3, -2],
    ![9, -17, 0], ![0, 0, -5], ![-2, -4, -3]]

noncomputable def p9 : Fin 9 → Fin 3 → ℝ := fun v i => (P9 v i : ℝ)

/-- The colour (dominant coordinate) of each pair. -/
def colT : Fin 9 → Fin 9 → Fin 3 :=
  ![![0, 1, 0, 1, 1, 2, 1, 2, 0], ![1, 0, 0, 1, 0, 2, 2, 2, 2], ![0, 0, 0, 0, 1, 1, 0, 2, 2],
    ![1, 1, 0, 0, 0, 2, 2, 0, 0], ![1, 0, 1, 0, 0, 1, 0, 2, 2], ![2, 2, 1, 2, 1, 0, 1, 0, 0],
    ![1, 2, 0, 2, 0, 1, 0, 1, 1], ![2, 2, 2, 0, 2, 0, 1, 0, 1], ![0, 2, 2, 0, 2, 0, 1, 1, 0]]

def domZ (v w : Fin 9) (k : Fin 3) : Prop :=
  ∀ j, j ≠ k → |P9 v j - P9 w j| < |P9 v k - P9 w k|

theorem domZ_colT : ∀ v w : Fin 9, v ≠ w → domZ v w (colT v w) := by
  unfold domZ; decide +kernel

theorem dom_of_domZ {v w : Fin 9} {k : Fin 3} (h : domZ v w k) : Dom (p9 v - p9 w) k := by
  intro j hj
  have := h j hj
  simp only [Pi.sub_apply, p9]
  rw [← Int.cast_sub, ← Int.cast_sub, ← Int.cast_abs, ← Int.cast_abs]
  exact_mod_cast this

/-- Smoothness at a unit vector with a dominant coordinate. -/
theorem smooth_of_dom {x₀ : Fin 3 → ℝ} {k : Fin 3} (hx : ‖x₀‖ = 1) (hk : Dom x₀ k) :
    IsSmoothAt x₀ := by
  have h1 : |x₀ k| = 1 := by rw [← norm_eq_of_dom hk, hx]
  refine ⟨coordFun (x₀ k) k, isSupport_coordFun h1, fun φ hφ => ?_⟩
  exact LinearMap.ext fun y => by rw [support_formula hx hk hφ y, coordFun_apply]

theorem not_dom_zero (k : Fin 3) : ¬ Dom (0 : Fin 3 → ℝ) k := by
  intro h
  fin_cases k
  · simpa using h 1 (by decide)
  · simpa using h 0 (by decide)
  · simpa using h 0 (by decide)

theorem framework (H : SimpleGraph (Fin 9)) : IsFramework H p9 := by
  intro v w hvw
  have hd := dom_of_domZ (domZ_colT v w hvw.ne)
  have hne : p9 v ≠ p9 w := by
    intro e
    rw [e, sub_self] at hd
    exact not_dom_zero _ hd
  exact ⟨hne, smooth_of_dom (norm_normalised hne) ((dom_normalised_iff hne).mpr hd)⟩

/-- Translations are infinitesimal rigid motions. -/
theorem isInfRigidMotion_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) :
    IsInfRigidMotion (fun _ : E => c) := by
  have hd : ∀ x : E, HasDerivAt (fun t : ℝ => x + t • c) c 0 := by
    intro x
    have := ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add x
    simpa using this
  refine ⟨⟨fun x t => x + t • c, fun x => ?_, fun x => by simp, fun x => (hd x).differentiableAt,
    fun x y t _ => by simp⟩, fun x => (hd x).deriv.symm⟩
  exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn

/-! ### Connectivity of the colour classes after deleting one edge -/

/-- Edges of colour `c` other than `{a, b}`. -/
def adjB (a b : Fin 9) (c : Fin 3) (v w : Fin 9) : Bool :=
  decide (v ≠ w) && decide (colT v w = c) && !((v == a && w == b) || (v == b && w == a))

def stepL (E : Fin 9 → Fin 9 → Bool) (R : List Bool) : List Bool :=
  (List.finRange 9).map fun (w : Fin 9) =>
    R.getD w.val false || (List.finRange 9).any fun (v : Fin 9) => R.getD v.val false && E v w

/-- Vertices reachable from `0` in at most `n` steps. -/
def reachL (E : Fin 9 → Fin 9 → Bool) : ℕ → List Bool
  | 0 => (List.finRange 9).map fun w => decide (w = 0)
  | n + 1 => stepL E (reachL E n)

set_option maxRecDepth 100000 in
theorem conn_check_0 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 0 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_1 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 1 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_2 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 2 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_3 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 3 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_4 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 4 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_5 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 5 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_6 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 6 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_7 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 7 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_8 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 8 b c) 8).getD w false = true := by
  decide +kernel

/-- Every colour class minus any single edge `{a, b}` is connected (for `a = b`
nothing is deleted). -/
theorem conn_check : ∀ (a b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB a b c) 8).getD w false = true := by
  intro a
  fin_cases a
  exacts [conn_check_0, conn_check_1, conn_check_2, conn_check_3, conn_check_4, conn_check_5,
    conn_check_6, conn_check_7, conn_check_8]

theorem getD_map_finRange {β : Type*} (g : Fin 9 → β) (d : β) (w : Fin 9) :
    ((List.finRange 9).map g).getD w.val d = g w := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simp)]
  simp

theorem reach_const (E : Fin 9 → Fin 9 → Bool) (f : Fin 9 → ℝ)
    (hE : ∀ v w, E v w = true → f v = f w) :
    ∀ n (w : Fin 9), (reachL E n).getD w false = true → f w = f 0 := by
  intro n
  induction n with
  | zero =>
    intro w h
    simp only [reachL, getD_map_finRange, decide_eq_true_eq] at h
    rw [h]
  | succ n ih =>
    intro w h
    simp only [reachL, stepL, getD_map_finRange, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true] at h
    rcases h with h | ⟨v, -, hv, hvw⟩
    · exact ih w h
    · rw [← hE v w hvw]; exact ih v hv

theorem infRigid_of (H : SimpleGraph (Fin 9)) (a b : Fin 9)
    (hH : ∀ v w, adjB a b (colT v w) v w = true → H.Adj v w) : IsInfRigid (stdBasis 3) H p9 := by
  refine ⟨framework H, fun u hu => ?_⟩
  have hedge : ∀ c v w, adjB a b c v w = true → u (v, c) = u (w, c) := by
    intro c v w h
    have hc : colT v w = c := by
      simp only [adjB, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2
    have hadj : H.Adj v w := hH v w (by rw [hc]; exact h)
    obtain ⟨c', s, hd, hs, hrow⟩ := mulVec_edge (framework H) hadj
    have hc' : c' = c := by
      rw [← hc]; exact hd.unique (dom_of_domZ (domZ_colT v w hadj.ne))
    have := hrow u
    rw [hu, Pi.zero_apply] at this
    rcases mul_eq_zero.mp this.symm with h0 | h0
    · exact absurd h0 hs
    · rw [← hc']; linarith
  have hconst : ∀ v i, u (v, i) = u (0, i) := fun v i =>
    reach_const _ (fun x => u (x, i)) (hedge i) 8 v (conn_check a b i v)
  refine ⟨fun _ => displacement (stdBasis 3) u 0, isInfRigidMotion_const _, fun v => ?_⟩
  rw [displacement_std, displacement_std]
  funext i
  exact hconst v i

/-- **`K₉` is edge-redundantly rigid in `ℓ∞³`.** -/
theorem k9_edgeRedundantlyRigid : EdgeRedundantlyRigid (completeGraph 9) 3 := by
  refine ⟨p9, infRigid_of _ 0 0 fun v w h => ?_, fun e he => ?_⟩
  · simp only [adjB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  · obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep e
    refine infRigid_of _ a b fun v w h => ?_
    simp only [adjB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
      Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨h.1.1, fun hmem => ?_⟩
    rw [Set.mem_singleton_iff, ← hab] at hmem
    have := Sym2.eq_iff.mp hmem
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases h.2.1 with h' | h' <;> contradiction
    · rcases h.2.2 with h' | h' <;> contradiction

end CDK.K9
