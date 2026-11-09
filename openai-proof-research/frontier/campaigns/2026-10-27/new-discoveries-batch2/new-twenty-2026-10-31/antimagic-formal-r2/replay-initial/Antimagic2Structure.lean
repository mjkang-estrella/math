import AntimagicModel
namespace Antimagic
open Finset

/-- The vertices that index incoming edges. -/
abbrev Nonroot (t n : ℕ) := {v : Vertex t n // 0 < depth v}

def parent {t n : ℕ} (ht : 0 < t) (v : Nonroot t n) : Vertex t n :=
  ⟨⟨v.val.1.val - 1, by have := v.val.1.isLt; omega⟩,
    ⟨v.val.2.val / t, by
      apply (Nat.div_lt_iff_lt_mul ht).mpr
      have hv := v.val.2.isLt
      have hh : v.val.1.val - 1 + 1 = v.val.1.val := by have := v.property; unfold depth at this; omega
      exact hv.trans_le (le_of_eq (by rw [← pow_succ]; exact congrArg (fun k => t ^ k) hh.symm))⟩⟩

theorem parent_child {t n : ℕ} (ht : 0 < t) (v : Nonroot t n) :
    Child (parent ht v) v.val := by
  constructor
  · have := v.property; change 0 < v.val.1.val at this
    change v.val.1.val = v.val.1.val - 1 + 1
    omega
  · rfl

theorem child_parent_unique {t n : ℕ} {u v : Vertex t n} (h : Child u v)
    (ht : 0 < t) : u = parent ht ⟨v, by have := h.1; unfold depth; omega⟩ := by
  apply Sigma.ext
  · apply Fin.ext
    have := h.1
    change u.1.val = v.1.val - 1
    omega
  · apply (Fin.heq_ext_iff (by congr 1; have := h.1; change u.1.val = v.1.val - 1; omega)).mpr
    exact h.2.symm

/-- The explicit ordered incoming edge. -/
def incomingEdge {t n : ℕ} (ht : 0 < t) (v : Nonroot t n) : (tree t n).edgeSet :=
  ⟨s(parent ht v, v.val), (tree t n).mem_edgeSet.mpr (Or.inl (parent_child ht v))⟩

theorem incomingEdge_injective {t n : ℕ} (ht : 0 < t) :
    Function.Injective (@incomingEdge t n ht) := by
  intro a b hab
  have he := congrArg Subtype.val hab
  rcases Sym2.eq_iff.mp he with h | h
  · exact Subtype.ext h.2
  · have ha := (parent_child ht a).1
    have hb := (parent_child ht b).1
    have h₁ := congrArg (fun v : Vertex t n => v.1.val) h.1
    have h₂ := congrArg (fun v : Vertex t n => v.1.val) h.2
    omega

theorem incomingEdge_surjective {t n : ℕ} (ht : 0 < t) :
    Function.Surjective (@incomingEdge t n ht) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    rcases (tree t n).mem_edgeSet.mp he with h | h
    · let a : Nonroot t n := ⟨v, by have := h.1; unfold depth; omega⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change s(parent ht a, v) = s(u, v)
      rw [← child_parent_unique h ht]
    · let a : Nonroot t n := ⟨u, by have := h.1; unfold depth; omega⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change s(parent ht a, u) = s(u, v)
      rw [← child_parent_unique h ht]
      exact Sym2.eq_swap

noncomputable def incomingEquiv {t n : ℕ} (ht : 0 < t) :
    Nonroot t n ≃ (tree t n).edgeSet :=
  Equiv.ofBijective (incomingEdge ht) ⟨incomingEdge_injective ht, incomingEdge_surjective ht⟩

/-- Reindexing the literal incidence sum by incoming endpoints. -/
theorem weight_incoming {t n : ℕ} (ht : 0 < t) (f : Labeling (tree t n))
    (v : Vertex t n) :
    weight (tree t n) f v = ∑ a : Nonroot t n,
      if v = parent ht a ∨ v = a.val then (f (incomingEdge ht a)).val + 1 else 0 := by
  unfold weight
  rw [← (incomingEquiv ht).sum_comp]
  apply sum_congr rfl
  intro a _
  change (if v ∈ s(parent ht a, a.val) then _ else _) = _
  simp only [Sym2.mem_iff]; rfl

def childAt {t n : ℕ} (v : Vertex t n) (hv : depth v < n) (j : Fin t) : Vertex t n :=
  ⟨⟨v.1.val + 1, by unfold depth at hv; omega⟩,
    ⟨t * v.2.val + j.val, by
      rw [pow_succ, Nat.mul_comm (t ^ v.1.val) t]
      have := v.2.isLt
      have := j.isLt
      calc
        t * v.2.val + j.val < t * (v.2.val + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        _ ≤ t * t ^ v.1.val := Nat.mul_le_mul_left _ v.2.isLt⟩⟩

theorem childAt_child {t n : ℕ} (ht : 0 < t) (v : Vertex t n)
    (hv : depth v < n) (j : Fin t) : Child v (childAt v hv j) := by
  refine ⟨rfl, ?_⟩
  change (t * v.2.val + j.val) / t = v.2.val
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ ht, Nat.div_eq_of_lt j.isLt, Nat.zero_add]

def childrenEquiv {t n : ℕ} (ht : 0 < t) (v : Vertex t n) (hv : depth v < n) :
    Fin t ≃ {w : Vertex t n // Child v w} where
  toFun j := ⟨childAt v hv j, childAt_child ht v hv j⟩
  invFun w := ⟨w.val.2.val % t, Nat.mod_lt _ ht⟩
  left_inv j := by apply Fin.ext; simp [childAt, Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  right_inv w := by
    apply Subtype.ext
    apply Sigma.ext
    · apply Fin.ext; exact w.property.1.symm
    · apply (Fin.heq_ext_iff (by congr 1; exact w.property.1.symm)).mpr
      change t * v.2.val + w.val.2.val % t = w.val.2.val
      rw [← w.property.2]
      exact Nat.div_add_mod _ _

theorem children_count {t n : ℕ} (ht : 0 < t) (v : Vertex t n) :
    (univ.filter (Child v)).card = if depth v < n then t else 0 := by
  split_ifs with hv
  · rw [← Fintype.card_subtype, ← Fintype.card_congr (childrenEquiv ht v hv)]
    exact Fintype.card_fin t
  · have he : univ.filter (Child v) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro w hw
      have h := (mem_filter.mp hw).2
      have := w.1.isLt
      have := h.1
      unfold depth at hv
      omega
    rw [he, card_empty]

theorem root_reachable {t n : ℕ} (ht : 0 < t) (v : Vertex t n) :
    (tree t n).Reachable (root t n) v := by
  have aux : ∀ h, ∀ v : Vertex t n, depth v = h →
      (tree t n).Reachable (root t n) v := by
    intro h
    induction h with
    | zero =>
      intro v hv
      rw [unique_depth_zero v hv]
    | succ h ih =>
      intro v hv
      let a : Nonroot t n := ⟨v, by omega⟩
      have hp : depth (parent ht a) = h := by
        change v.1.val - 1 = h
        change v.1.val = h + 1 at hv
        omega
      exact (ih _ hp).trans (SimpleGraph.Adj.reachable (G := tree t n) (Or.inl (parent_child ht a)))
  exact aux _ v rfl

theorem tree_connected {t n : ℕ} (ht : 0 < t) : (tree t n).Connected := by
  have : Nonempty (Vertex t n) := ⟨root t n⟩
  exact ⟨fun u v => (root_reachable ht u).symm.trans (root_reachable ht v)⟩

theorem tree_isTree {t n : ℕ} (ht : 0 < t) : (tree t n).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨tree_connected ht, ?_⟩
  simp only [Nat.card_eq_fintype_card]
  rw [← Fintype.card_congr (incomingEquiv ht)]
  have hp : (fun v : Vertex t n => 0 < depth v) = (fun v => v ≠ root t n) := by
    funext v
    apply propext
    constructor
    · intro h he; subst v; simp [root_depth] at h
    · intro h
      have : depth v ≠ 0 := fun hz => h (unique_depth_zero v hz)
      omega
  change Fintype.card {v : Vertex t n // 0 < depth v} + 1 = _
  simp only [hp, Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  have : 0 < Fintype.card (Vertex t n) := Fintype.card_pos_iff.mpr ⟨root t n⟩
  omega

/-- The round-1 structural obligation is discharged. -/
theorem modelStructure : ModelStructure := by
  intro t n ht _hn
  have ht' : 0 < t := by omega
  refine ⟨{
    root := root t n
    depth := depth
    child := Child
    childDec := inferInstance
    isTree := tree_isTree ht'
    root_zero := ?_
    adj_iff := fun _ _ => Iff.rfl
    child_depth := fun _ _ h => h.1
    unique_parent := ?_
    depth_le := fun v => by have := v.1.isLt; unfold depth; omega
    child_count := children_count ht'
  }, rfl, rfl, rfl⟩
  · intro v
    exact ⟨unique_depth_zero v, fun h => h ▸ root_depth t n⟩
  · intro v hv
    have hp : 0 < depth v := by
      have : depth v ≠ 0 := fun hz => hv (unique_depth_zero v hz)
      omega
    exact ⟨parent ht' ⟨v, hp⟩, parent_child ht' _, fun u hu => child_parent_unique hu ht'⟩

#print axioms modelStructure
end Antimagic
