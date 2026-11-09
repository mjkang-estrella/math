import Endpoint
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CommonBasis332371

def TwoBasePartition (N : Matroid V) (S A B : Set V) : Prop :=
  N.IsBase A ∧ N.IsBase B ∧ Disjoint A B ∧ A ∪ B = S

def dx : Finset V := Finset.univ.erase 1
def dy : Finset V := Finset.univ.erase 6

theorem check_noCommon : baseList.all (fun b => decide (¬ (b ⊆ dx ∧ b ⊆ dy ∧
    dx \ b ∈ baseList ∧ dy \ b ∈ baseList))) = true := by decide

theorem noCommon : ∀ b ∈ bases, ¬ (b ⊆ dx ∧ b ⊆ dy ∧ dx \ b ∈ bases ∧ dy \ b ∈ bases) := by
  intro b hb
  have h := of_decide_eq_true ((List.all_eq_true.mp check_noCommon) b (by simpa [bases] using hb))
  simpa only [bases, List.mem_toFinset] using h

lemma other_eq (S A B : Set V) (hd : Disjoint A B) (hu : A ∪ B = S) : B = S \ A := by
  apply Set.ext
  intro e
  constructor
  · intro he
    exact ⟨by rw [← hu]; exact Or.inr he,
      fun h => (Set.disjoint_left.mp hd) h he⟩
  · rintro ⟨he, hn⟩
    rw [← hu] at he
    exact he.resolve_left hn

lemma no_shared : ¬ ∃ B C D : Set V,
    TwoBasePartition M (M.E \ {1}) B C ∧ TwoBasePartition M (M.E \ {6}) B D := by
  rintro ⟨B,C,D,⟨hB,hC,hdx,hux⟩,⟨_,hD,hdy,huy⟩⟩
  change BP B at hB
  obtain ⟨b,hb,rfl⟩ := hB
  have cx := other_eq (M.E \ {1}) (b : Set V) C hdx hux
  have cy := other_eq (M.E \ {6}) (b : Set V) D hdy huy
  have bx : b ⊆ dx := by
    intro e he
    have : e ∈ M.E \ {1} := by rw [← hux]; exact Or.inl he
    simpa [dx,M] using this
  have byy : b ⊆ dy := by
    intro e he
    have : e ∈ M.E \ {6} := by rw [← huy]; exact Or.inl he
    simpa [dy,M] using this
  have hc : dx \ b ∈ bases := by
    change BP C at hC
    obtain ⟨c,hc,hce⟩ := hC
    have : c = dx \ b := by
      apply Finset.coe_injective
      rw [hce,cx]
      simp [dx,M]
    simpa [this] using hc
  have hd : dy \ b ∈ bases := by
    change BP D at hD
    obtain ⟨d,hd,hde⟩ := hD
    have : d = dy \ b := by
      apply Finset.coe_injective
      rw [hde,cy]
      simp [dy,M]
    simpa [this] using hd
  exact noCommon b hb ⟨bx,byy,hc,hd⟩

lemma first_partition : TwoBasePartition M (M.E \ {1})
    (({0,2,3,5} : Finset V) : Set V) (({4,6,7,8} : Finset V) : Set V) := by
  refine ⟨⟨{0,2,3,5},by simp [bases,baseList],rfl⟩,⟨{4,6,7,8},by simp [bases,baseList],rfl⟩,?_,?_⟩
  · exact Finset.disjoint_coe.mpr (by decide)
  · change _ = Set.univ \ {_}
    ext e; fin_cases e <;> simp

lemma second_partition : TwoBasePartition M (M.E \ {6})
    (({0,1,2,7} : Finset V) : Set V) (({3,4,5,8} : Finset V) : Set V) := by
  refine ⟨⟨{0,1,2,7},by simp [bases,baseList],rfl⟩,⟨{3,4,5,8},by simp [bases,baseList],rfl⟩,?_,?_⟩
  · exact Finset.disjoint_coe.mpr (by decide)
  · change _ = Set.univ \ {_}
    ext e; fin_cases e <;> simp

/-- Literal k=2 refutation: two deletions partition into bases, but no such
partitions share a base. The ground set has 2*4+1 elements and rank 4. -/
theorem counterexample : ∃ N : Matroid V,
    N.E = Set.univ ∧ N.E.ncard = 2 * 4 + 1 ∧ N.eRank = 4 ∧
    (∃ A B, TwoBasePartition N (N.E \ {1}) A B) ∧
    (∃ A B, TwoBasePartition N (N.E \ {6}) A B) ∧
    ¬ (∃ B C D, TwoBasePartition N (N.E \ {1}) B C ∧
      TwoBasePartition N (N.E \ {6}) B D) := by
  refine ⟨M,rfl,?_,?_,⟨_,_,first_partition⟩,⟨_,_,second_partition⟩,no_shared⟩
  · simp [M,Set.ncard_univ]
  · have h : M.IsBase (({0,2,3,5} : Finset V) : Set V) := first_partition.1
    rw [← h.encard_eq_eRank]
    norm_num [Set.encard_insert_of_notMem]

#print axioms counterexample
end CommonBasis332371
