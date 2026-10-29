import DepthDefs
import Mathlib.Data.Set.Countable
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option warningAsError true

namespace CascadeRate
attribute [local instance] Classical.propDecidable
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
abbrev Word := List Bool
abbrev InfiniteWord := ℕ → Bool

def PrefixClosed (T : Set Word) : Prop := ∀ ⦃u v⦄, u <+: v → v ∈ T → u ∈ T
def Internal (T : Set Word) (w : Word) : Prop := ∃ a : Bool, w ++ [a] ∈ T
def FiniteContext (T : Set Word) (w : Word) : Prop := w ∈ T ∧ ¬ Internal T w
def InfiniteContext (T : Set Word) (b : InfiniteWord) : Prop :=
  ∀ n, List.ofFn (fun i : Fin n => b i) ∈ T

def ShiftClosed (T : Set Word) : Prop := ∀ w ∈ T, w.drop 1 ∈ T

structure SourceContextTree where
  nodes : Set Word
  prefix_closed : PrefixClosed nodes
  root_internal : Internal nodes []
  saturated : ∀ w, Internal nodes w → ∀ a : Bool, w ++ [a] ∈ nodes
  countable_branches : Set.Countable {b | InfiniteContext nodes b}

theorem root_internal_of_nontrivial (N : Set Word) (hp : PrefixClosed N)
    (hn : ∃ w ∈ N, w ≠ []) : Internal N [] := by
  rcases hn with ⟨w,hw,hn⟩
  cases w with
  | nil => exact (hn rfl).elim
  | cons a v => exact ⟨a, hp ⟨v,rfl⟩ hw⟩

theorem internal_prefix (T : SourceContextTree) {u v : Word}
    (h : u <+: v) (hv : Internal T.nodes v) : Internal T.nodes u := by
  rcases hv with ⟨a, ha⟩
  rcases h with ⟨s, rfl⟩
  cases s with
  | nil => exact ⟨a, by simpa using ha⟩
  | cons b s =>
    refine ⟨b, T.prefix_closed ?_ ha⟩
    exact ⟨s ++ [a], by simp⟩

theorem internal_node (T : SourceContextTree) {w : Word}
    (h : Internal T.nodes w) : w ∈ T.nodes := by
  obtain ⟨a, ha⟩ := h
  exact T.prefix_closed ⟨[a], rfl⟩ ha

theorem nontrivial (T : SourceContextTree) : [false] ∈ T.nodes := by
  simpa using T.saturated [] T.root_internal false

-- A recursive search for the first leaf on a finite noninternal path.
theorem exists_context_prefix (T : SourceContextTree) (w : Word)
    (hw : ¬ Internal T.nodes w) : ∃ c, c <+: w ∧ FiniteContext T.nodes c := by
  have hex : ∃ n, ¬ Internal T.nodes (w.take n) := ⟨w.length, by simpa using hw⟩
  let n := Nat.find hex
  have hn : ¬ Internal T.nodes (w.take n) := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    apply hn
    simpa [this] using T.root_internal
  have hprev : Internal T.nodes (w.take (n-1)) := by
    by_contra h
    have := Nat.find_min hex (show n-1 < n by omega)
    exact this h
  have hlen : n ≤ w.length := Nat.find_min' hex (show ¬ Internal T.nodes (w.take w.length) by simpa using hw)
  have hlt : n-1 < w.length := by omega
  have hnode : w.take n ∈ T.nodes := by
    have hp : w.take (n-1) ++ [w[n-1]'(by omega)] = w.take n := by
      simpa [show n-1+1=n by omega] using
        (List.take_append_getElem (l := w) (i := n-1) hlt)
    rw [← hp]
    exact T.saturated _ hprev _
  exact ⟨w.take n, List.take_prefix _ _, hnode, hn⟩

noncomputable def cont (T : SourceContextTree) (w : Word) : Word :=
  if h : ¬ Internal T.nodes w then (exists_context_prefix T w h).choose else []

theorem cont_spec (T : SourceContextTree) {w : Word} (h : ¬ Internal T.nodes w) :
    cont T w <+: w ∧ FiniteContext T.nodes (cont T w) := by
  simp only [cont, dite_eq_left h]
  exact (exists_context_prefix T w h).choose_spec

theorem context_prefix_unique (T : SourceContextTree) {u v w : Word}
    (hu : u <+: w) (hv : v <+: w)
    (huc : FiniteContext T.nodes u) (hvc : FiniteContext T.nodes v) : u = v := by
  have step : ∀ {u v : Word}, u <+: v → FiniteContext T.nodes u →
      v ∈ T.nodes → u = v := by
    intro u v hp hc hn
    rcases hp with ⟨s,rfl⟩
    cases s with
    | nil => simp
    | cons a s =>
      exfalso
      apply hc.2
      exact ⟨a, T.prefix_closed ⟨s, by simp⟩ hn⟩
  rcases List.prefix_or_prefix_of_prefix hu hv with h | h
  · exact step h huc hvc.1
  · exact (step h hvc huc.1).symm

-- The least positive shift reaching an internal suffix is the longest strict one.
noncomputable def lisIndex (T : SourceContextTree) (w : Word) : ℕ :=
  if h : w ≠ [] then Nat.find (show ∃ j, 0 < j ∧ Internal T.nodes (w.drop j) from
    ⟨w.length, by simpa using List.length_pos_iff.mpr h, by simpa using T.root_internal⟩)
  else 0

noncomputable def lis (T : SourceContextTree) (w : Word) : Word := w.drop (lisIndex T w)
noncomputable def alphaLIS (T : SourceContextTree) (w : Word) : Word :=
  w.drop (lisIndex T w - 1)

theorem lisIndex_spec (T : SourceContextTree) {w : Word} (hw : w ≠ []) :
    0 < lisIndex T w ∧ Internal T.nodes (w.drop (lisIndex T w)) ∧
    lisIndex T w ≤ w.length ∧
    ∀ j, 0 < j → j < lisIndex T w → ¬ Internal T.nodes (w.drop j) := by
  let hex : ∃ j, 0 < j ∧ Internal T.nodes (w.drop j) :=
    ⟨w.length, List.length_pos_iff.mpr hw, by simpa using T.root_internal⟩
  change 0 < (if _ : w ≠ [] then Nat.find hex else 0) ∧ _
  simp only [lisIndex, dite_eq_left hw]
  exact ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2,
    Nat.find_min' hex ⟨List.length_pos_iff.mpr hw, by simpa using T.root_internal⟩,
    fun j hj hjn hi => Nat.find_min hex hjn ⟨hj, hi⟩⟩

theorem lis_maximal (T : SourceContextTree) {w : Word} (hw : w ≠ [])
    {j : ℕ} (hj : 0 < j) (hi : Internal T.nodes (w.drop j)) :
    (w.drop j).length ≤ (lis T w).length := by
  have h := lisIndex_spec T hw
  have : lisIndex T w ≤ j := by
    by_contra hh
    exact h.2.2.2 j hj (by omega) hi
  simp only [lis, List.length_drop]
  omega

theorem lis_strict (T : SourceContextTree) {w : Word} (hw : w ≠ []) :
    (lis T w).length < w.length := by
  have h := lisIndex_spec T hw
  simp only [lis, List.length_drop]
  have : 0 < w.length := List.length_pos_iff.mpr hw
  omega

theorem alphaLIS_length (T : SourceContextTree) {w : Word} (hw : w ≠ []) :
    (alphaLIS T w).length = w.length - lisIndex T w + 1 := by
  have h := lisIndex_spec T hw
  simp only [alphaLIS, List.length_drop]
  omega

theorem alphaLIS_singleton (T : SourceContextTree) (a : Bool) : alphaLIS T [a] = [a] := by
  have h := lisIndex_spec T (show [a] ≠ [] by simp)
  have hj : lisIndex T [a] = 1 := by simp at h; omega
  simp [alphaLIS, hj]

theorem alphaLIS_preceding_letter (T : SourceContextTree) {w : Word} (hw : w ≠ []) :
    ∃ a : Bool, alphaLIS T w = a :: lis T w := by
  have hs := lisIndex_spec T hw
  have hj : lisIndex T w - 1 < w.length := by omega
  refine ⟨w[lisIndex T w - 1], ?_⟩
  unfold alphaLIS lis
  have he := List.getElem_cons_drop (as := w) hj
  simpa [show lisIndex T w - 1 + 1 = lisIndex T w by omega] using he.symm

theorem alphaLIS_noninternal (T : SourceContextTree) {w : Word}
    (hw : w ≠ []) (hn : ¬ Internal T.nodes w) : ¬ Internal T.nodes (alphaLIS T w) := by
  have h := lisIndex_spec T hw
  unfold alphaLIS
  by_cases hj : lisIndex T w = 1
  · simpa [hj] using hn
  · exact h.2.2.2 _ (by omega) (by omega)

-- Probability laws are indexed by both kinds of actual contexts.
abbrev Context (T : SourceContextTree) :=
  {w : Word // FiniteContext T.nodes w} ⊕ {b : InfiniteWord // InfiniteContext T.nodes b}
theorem contexts_countable (T : SourceContextTree) : Countable (Context T) := by
  have : Countable {b : InfiniteWord // InfiniteContext T.nodes b} :=
    T.countable_branches.to_subtype
  infer_instance

structure ProbabilityAssignment (T : SourceContextTree) where
  law : Context T → Bool → ℝ
  positive : ∀ c a, 0 < law c a
  normalized : ∀ c, law c false + law c true = 1

noncomputable def fairAssignment (T : SourceContextTree) : ProbabilityAssignment T where
  law := fun _ _ => 1/2
  positive := by intros; norm_num
  normalized := by intros; norm_num

theorem fairAssignment_law (T : SourceContextTree) (c : Context T) (a : Bool) :
    (fairAssignment T).law c a = (1/2 : ℝ) := rfl

noncomputable def finiteLaw (T : SourceContextTree) (q : ProbabilityAssignment T)
    (w : Word) (a : Bool) : ℝ :=
  if h : ¬ Internal T.nodes w then
    q.law (.inl ⟨cont T w, (cont_spec T h).2⟩) a else 1

-- Zero-based k corresponds to source beta_(k+1), evaluated at sigma^(k+1)(w).
noncomputable def cascade (T : SourceContextTree) (q : ProbabilityAssignment T)
    (w : Word) : ℝ :=
  ∏ k ∈ Finset.range (lisIndex T w - 1),
    finiteLaw T q (w.drop (k+1)) (w[k]?.getD false)

theorem cascade_nil (T : SourceContextTree) (q : ProbabilityAssignment T) :
    cascade T q [] = 1 := by simp [cascade, lisIndex]

theorem cascade_factor_valid (T : SourceContextTree) {w : Word}
    (hw : w ≠ []) {k : ℕ} (hk : k < lisIndex T w - 1) :
    k < w.length ∧ ¬ Internal T.nodes (w.drop (k+1)) := by
  have h := lisIndex_spec T hw
  exact ⟨by omega, h.2.2.2 _ (by omega) (by omega)⟩

theorem cascade_fair (T : SourceContextTree) {w : Word} (hw : w ≠ []) :
    cascade T (fairAssignment T) w = (1/2 : ℝ) ^ (lisIndex T w - 1) := by
  unfold cascade
  have hf : ∀ k ∈ Finset.range (lisIndex T w - 1),
      finiteLaw T (fairAssignment T) (w.drop (k+1)) (w[k]?.getD false) = (1/2 : ℝ) := by
    intro k hk
    have h := (cascade_factor_valid T hw (Finset.mem_range.mp hk)).2
    simp [finiteLaw, h, fairAssignment]
  simp only [Finset.prod_congr rfl hf, Finset.prod_const, Finset.card_range]

theorem cascade_fair_halfpower (T : SourceContextTree) {w : Word} (hw : w ≠ []) :
    cascade T (fairAssignment T) w = (1/2 : ℝ) ^ (w.length - (alphaLIS T w).length) := by
  rw [cascade_fair T hw, alphaLIS_length T hw]
  have h := lisIndex_spec T hw
  congr 1
  omega

-- Literal equation (5), finite because all words have one prescribed length.
noncomputable def kappa (T : SourceContextTree) (q : ProbabilityAssignment T)
    (s : Word) (n : ℕ) : ℝ := by
  classical
  exact ∑ v : Fin (s.length+n-1) → Bool,
    if FiniteContext T.nodes (List.ofFn v) ∧ alphaLIS T (List.ofFn v) = s
    then cascade T q (List.ofFn v) else 0

def GeometricDecay (f : ℕ → ℝ) : Prop :=
  ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∃ n₀, ∀ n ≥ n₀, f n ≤ C*r^n

def ContextAlphaLIS (T : SourceContextTree) (s : Word) : Prop :=
  ∃ c, FiniteContext T.nodes c ∧ alphaLIS T c = s

def SourceGeometricRateClaim : Prop :=
  ∀ (T : SourceContextTree) (q : ProbabilityAssignment T),
    (∀ (S : SourceContextTree), S.nodes ⊆ T.nodes → ShiftClosed S.nodes → S.nodes.Finite) →
    ∀ s, ContextAlphaLIS T s → GeometricDecay (kappa T q s)
end CascadeRate
