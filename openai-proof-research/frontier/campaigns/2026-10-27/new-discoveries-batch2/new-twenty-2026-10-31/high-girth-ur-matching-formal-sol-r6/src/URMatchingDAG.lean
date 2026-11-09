module
public import URMatchingBase
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Relation
@[expose] public section
namespace URMatching
universe u
/-- Finite DAGs admit a bijective topological ranking. Acyclicity here is
irreflexivity of the genuine transitive closure, not a graph field. -/
theorem finite_dag_topological {I : Type u} [Fintype I] (R : I → I → Prop)
    (acyc : ∀ i, ¬ Relation.TransGen R i i) :
    ∃ t : I ≃ Fin (Fintype.card I), ∀ i j, R i j → t i < t j := by
  classical
  let pred (i : I) := Finset.univ.filter (fun k => Relation.TransGen R k i)
  let rank (i : I) := (pred i).card
  have hrank : ∀ i j, R i j → rank i < rank j := by
    intro i j hij
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro k hk
      simp only [pred, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk.tail hij
    · intro he
      have hj : i ∈ pred j := by simp [pred, Relation.TransGen.single hij]
      rw [← he] at hj
      exact acyc i ((Finset.mem_filter.mp hj).2)
  let n := Fintype.card I
  let label := Fintype.equivFin I
  let code (i : I) := rank i * n + (label i).val
  have hc : Function.Injective code := by
    intro i j he
    have hm := congrArg (fun k => k % n) he
    have hi : (label i).val < n := (label i).isLt
    have hj : (label j).val < n := (label j).isLt
    have hl : (label i).val = (label j).val := by
      simpa [code, Nat.add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hm
    exact label.injective (Fin.ext hl)
  have hcode : ∀ i j, R i j → code i < code j := by
    intro i j hij
    have hr := hrank i j hij
    have hm := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hr)
    have hi : (label i).val < n := (label i).isLt
    dsimp [code]
    rw [Nat.succ_mul] at hm
    omega
  let : LinearOrder I := LinearOrder.lift' code hc
  let iso := Fintype.orderIsoFinOfCardEq I rfl
  refine ⟨iso.symm.toEquiv, ?_⟩
  intro i j hij
  exact iso.symm.strictMono (show i < j from hcode i j hij)
end URMatching
