import IntervalPartition

namespace IntervalWidth
variable {α : Type*} [LE α] {n k : Nat} {I : Fin n → Interval α}

/-- A matching to k distinct supply copies at each index. Each demand chooses at
most one parent; injective slots at each parent prevent reuse of a supply copy. -/
structure CopyMatching (k : Nat) (I : Fin n → Interval α) where
  parent : Fin n → Option (Fin n)
  edge : ∀ i j, parent j = some i → Compatible I i j
  slots : ∀ i, {j : Fin n // parent j = some i} ↪ Fin k

/-- Forgetting the copy labels of a matching leaves a chronological forest. -/
def CopyMatching.toForest (M : CopyMatching k I) : Forest k I where
  parent := M.parent
  edge := M.edge
  arity := by
    intro i
    have h := Fintype.card_le_of_embedding (M.slots i)
    simpa only [Fintype.card_fin, Fintype.card_subtype] using h

/-- Every bounded-arity forest can label its children with distinct supply copies. -/
noncomputable def Forest.toMatching (F : Forest k I) : CopyMatching k I := by
  classical
  refine ⟨F.parent, F.edge, fun i => ?_⟩
  have h : Fintype.card {j : Fin n // F.parent j = some i} ≤ Fintype.card (Fin k) := by
    simpa only [Fintype.card_fin, Fintype.card_subtype] using F.arity i
  exact Classical.choice (Function.Embedding.nonempty_of_card_le h)

noncomputable def CopyMatching.size (M : CopyMatching k I) : Nat := by
  classical
  exact Fintype.card {j : Fin n // M.parent j ≠ none}

theorem CopyMatching.roots_add_size (M : CopyMatching k I) :
    M.toForest.rootCount + M.size = n := by
  classical
  change Fintype.card {j : Fin n // M.parent j = none} +
    Fintype.card {j : Fin n // ¬ M.parent j = none} = n
  rw [Fintype.card_subtype_compl]
  have h := Fintype.card_subtype_le (fun j : Fin n => M.parent j = none)
  rw [Fintype.card_fin] at h ⊢
  exact Nat.add_sub_of_le h

theorem CopyMatching.width_le_defect (M : CopyMatching k I) :
    width k I ≤ n - M.size := by
  have h := M.roots_add_size
  have eq : n - M.size = M.toForest.rootCount := by omega
  rw [eq]
  exact width_le_roots M.toForest

/-- Exact attained matching optimum, derived rather than used to define width. -/
theorem width_matching_optimum (k : Nat) (I : Fin n → Interval α) :
    (∃ M : CopyMatching k I, n - M.size = width k I) ∧
    (∀ M : CopyMatching k I, width k I ≤ n - M.size) := by
  obtain ⟨F, hF⟩ := (width_eq_min_roots k I).1
  refine ⟨⟨F.toMatching, ?_⟩, CopyMatching.width_le_defect⟩
  have h := F.toMatching.roots_add_size
  have eq : F.toMatching.toForest.rootCount = F.rootCount := rfl
  rw [eq, hF] at h
  omega

end IntervalWidth
