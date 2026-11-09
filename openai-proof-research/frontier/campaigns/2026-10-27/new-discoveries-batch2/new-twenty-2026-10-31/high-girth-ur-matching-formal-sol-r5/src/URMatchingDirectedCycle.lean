module
public import URMatchingEmbeddedSwitch
public import Mathlib.GroupTheory.Perm.List
@[expose] public section
namespace URMatching
universe u v
variable {I : Type u} {V : Type v} [Fintype I] [DecidableEq I] [DecidableEq V]

/-- The actual off-diagonal cross-edge digraph on indexed matching edges. -/
def CrossArc (G : SimpleGraph V) (e : Sum I I ↪ V) (i j : I) : Prop :=
  i ≠ j ∧ G.Adj (e (Sum.inl i)) (e (Sum.inr j))

/-- A simple directed cycle, given by its distinct indices in cyclic order. -/
def DirectedCycleList (R : I → I → Prop) (l : List I) : Prop :=
  l.Nodup ∧ 2 ≤ l.length ∧ ∀ (n : ℕ) (hn : n < l.length),
    R (l[n]) (l[(n + 1) % l.length]'(Nat.mod_lt _ (Nat.zero_le n |>.trans_lt hn)))

/-- Switch precisely the cycle, fixing every matched edge outside its list. -/
theorem directed_cycle_not_ur (G : SimpleGraph V) (e : Sum I I ↪ V)
    (diag : ∀ i, G.Adj (e (Sum.inl i)) (e (Sum.inr i)))
    (l : List I) (cycle : DirectedCycleList (CrossArc G e) l) :
    ¬ IsUR G (indexedEdges e (Equiv.refl I)) := by
  apply indexed_switch_not_ur G e l.formPerm
  · intro he
    have h1 : l.formPerm = 1 := he
    have hs := (List.formPerm_eq_one_iff l cycle.1).mp h1
    exact (Nat.not_succ_le_self 1) (cycle.2.1.trans hs)
  · intro i
    by_cases hi : i ∈ l
    · obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hi
      rw [List.formPerm_apply_getElem l cycle.1 n hn]
      exact (cycle.2.2 n hn).2
    · rw [List.formPerm_apply_of_notMem hi]
      exact diag i

/-- Literal UR uniqueness excludes every directed simple cycle in this digraph. -/
theorem ur_no_directed_cycle (G : SimpleGraph V) (e : Sum I I ↪ V)
    (diag : ∀ i, G.Adj (e (Sum.inl i)) (e (Sum.inr i)))
    (ur : IsUR G (indexedEdges e (Equiv.refl I))) :
    ¬ ∃ l, DirectedCycleList (CrossArc G e) l := by
  rintro ⟨l, hl⟩
  exact directed_cycle_not_ur G e diag l hl ur
end URMatching
