import StructureR5
namespace EdgePattern.TreeModelsR5
open TreeModelsR4 TreeModelsR3
set_option linter.unusedSimpArgs false
universe u
variable {W : Type u} [Fintype W] (T : Rooted W)

noncomputable local instance : DecidableEq W := Classical.decEq W

def parent (i : Fin 4) : W := if i.val < 2 then T.left else T.right

structure Branches where
  vertex : Fin 4 → W
  injective : Function.Injective vertex
  mem : ∀ i, vertex i ∈ children T (parent T i)
    (if i.val < 2 then T.right else T.left)
  cover_left : children T T.left T.right = {vertex 0, vertex 1}
  cover_right : children T T.right T.left = {vertex 2, vertex 3}

noncomputable def Branches.leaves (B : Branches T) (i : Fin 4) : Finset W :=
  children T (B.vertex i) (parent T i)

theorem branches_exist (hT : TreeFamily T 3 2) : Nonempty (Branches T) := by
  classical
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp (root_children_card T hT).1
  obtain ⟨c,d,hcd,hf⟩ := Finset.card_eq_two.mp (root_children_card T hT).2
  have ha : a ∈ children T T.left T.right := by rw [he]; simp
  have hb : b ∈ children T T.left T.right := by rw [he]; simp
  have hc : c ∈ children T T.right T.left := by rw [hf]; simp
  have hd : d ∈ children T T.right T.left := by rw [hf]; simp
  have dis := root_children_disjoint T hT
  have hac : a ≠ c := fun h => Finset.disjoint_left.mp dis ha (h ▸ hc)
  have had : a ≠ d := fun h => Finset.disjoint_left.mp dis ha (h ▸ hd)
  have hbc : b ≠ c := fun h => Finset.disjoint_left.mp dis hb (h ▸ hc)
  have hbd : b ≠ d := fun h => Finset.disjoint_left.mp dis hb (h ▸ hd)
  let f : Fin 4 → W := ![a,b,c,d]
  refine ⟨⟨f,?_,?_,?_,?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f, Ne.symm]
  · intro i
    fin_cases i
    · simpa only [f, parent, Matrix.cons_val_zero, Fin.isValue, Fin.reduceFinMk, Fin.val_zero, Nat.reduceLT, ite_true] using ha
    · simpa [f, parent] using hb
    · simpa [f, parent] using hc
    · simpa [f, parent] using hd
  · simpa [f] using he
  · simpa [f] using hf

theorem Branches.adj (B : Branches T) (i : Fin 4) :
    T.graph.Adj (parent T i) (B.vertex i) :=
  ((mem_children T _ _ _).mp (B.mem i)).1

theorem Branches.ne_left (B : Branches T) (i : Fin 4) : B.vertex i ≠ T.left := by
  have hm := (mem_children T _ _ _).mp (B.mem i)
  by_cases hi : i.val < 2
  · exact (by simpa [parent,hi] using hm.1.ne.symm)
  · simpa [hi] using hm.2

theorem Branches.ne_right (B : Branches T) (i : Fin 4) : B.vertex i ≠ T.right := by
  have hm := (mem_children T _ _ _).mp (B.mem i)
  by_cases hi : i.val < 2
  · simpa [hi] using hm.2
  · exact (by simpa [parent,hi] using hm.1.ne.symm)

theorem Branches.leaves_card_le (B : Branches T) (hT : TreeFamily T 3 2) (i : Fin 4) :
    (B.leaves T i).card ≤ 2 :=
  children_card_le T hT _ _ (B.adj T i).symm

theorem Branches.leaf_ne_roots (B : Branches T) (ha : T.graph.IsAcyclic)
    (i : Fin 4) {z : W} (hz : z ∈ B.leaves T i) : z ≠ T.left ∧ z ≠ T.right := by
  obtain ⟨haz,hzp⟩ := (mem_children T _ _ _).mp hz
  have hadj := B.adj T i
  by_cases hi : i.val < 2
  · simp only [parent,hi,ite_true] at hadj hzp
    exact ⟨hzp,grandchild_ne_other_root T ha T.root_edge hadj haz⟩
  · simp only [parent,hi,ite_false] at hadj hzp
    exact ⟨grandchild_ne_other_root T ha T.root_edge.symm hadj haz,hzp⟩

theorem Branches.leaf_ne_branch (B : Branches T) (ha : T.graph.IsAcyclic)
    (i j : Fin 4) {z : W} (hz : z ∈ B.leaves T i) : z ≠ B.vertex j := by
  obtain ⟨haz,_⟩ := (mem_children T _ _ _).mp hz
  have hi := B.adj T i
  have hj := B.adj T j
  by_cases hip : i.val < 2 <;> by_cases hjp : j.val < 2
  · simp only [parent,hip,hjp,ite_true] at hi hj
    exact grandchild_not_sibling T ha hi haz hj
  · simp only [parent,hip,hjp,ite_true,ite_false] at hi hj
    exact grandchild_not_cross_branch T ha T.root_edge hi (B.ne_right T i)
      hj (B.ne_left T j) haz
  · simp only [parent,hip,hjp,ite_true,ite_false] at hi hj
    exact grandchild_not_cross_branch T ha T.root_edge.symm hi (B.ne_left T i)
      hj (B.ne_right T j) haz
  · simp only [parent,hip,hjp,ite_false] at hi hj
    exact grandchild_not_sibling T ha hi haz hj

theorem Branches.leaves_disjoint (B : Branches T) (ha : T.graph.IsAcyclic)
    (i j : Fin 4) (hij : i ≠ j) : Disjoint (B.leaves T i) (B.leaves T j) := by
  have hi := B.adj T i
  have hj := B.adj T j
  have hne : B.vertex i ≠ B.vertex j := fun h => hij (B.injective h)
  unfold Branches.leaves
  by_cases hip : i.val < 2 <;> by_cases hjp : j.val < 2
  · simp only [parent,hip,hjp,ite_true] at hi hj ⊢
    exact sibling_grandchildren_disjoint T ha hne hi hj
  · simp only [parent,hip,hjp,ite_true,ite_false] at hi hj ⊢
    exact cross_grandchildren_disjoint T ha T.root_edge hi (B.ne_right T i)
      hj (B.ne_left T j)
  · simp only [parent,hip,hjp,ite_true,ite_false] at hi hj ⊢
    exact cross_grandchildren_disjoint T ha T.root_edge.symm hi (B.ne_left T i)
      hj (B.ne_right T j)
  · simp only [parent,hip,hjp,ite_false] at hi hj ⊢
    exact sibling_grandchildren_disjoint T ha hne hi hj

theorem Branches.coverage (B : Branches T) (hT : TreeFamily T 3 2) (z : W) :
    z = T.left ∨ z = T.right ∨ (∃ i, z = B.vertex i) ∨ ∃ i, z ∈ B.leaves T i := by
  classical
  rcases branch_coverage T hT z with h | h | h | h | ⟨a,ha,hz⟩ | ⟨a,ha,hz⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rw [B.cover_left] at h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨0,h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨1,h⟩))
  · rw [B.cover_right] at h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨2,h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨3,h⟩))
  · rw [B.cover_left] at ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr ⟨0,by simpa [Branches.leaves,parent] using hz⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨1,by simpa [Branches.leaves,parent] using hz⟩))
  · rw [B.cover_right] at ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr ⟨2,by simpa [Branches.leaves,parent] using hz⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨3,by simpa [Branches.leaves,parent] using hz⟩))
end EdgePattern.TreeModelsR5
