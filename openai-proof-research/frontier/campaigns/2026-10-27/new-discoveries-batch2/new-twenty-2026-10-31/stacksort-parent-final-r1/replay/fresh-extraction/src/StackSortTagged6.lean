import StackSortDel5Final
noncomputable section
namespace StackSort.Del6
open Seeds2 Round4 Del5 Classical BigOperators
abbrev Tuple := List (List ℕ)
abbrev Tag := Sigma (fun _ : ℕ × ℕ => Sigma (fun _ : Tuple × Tuple => Children × Children))

def collisions (m r s : ℕ) :=
  (tuples m r ×ˢ tuples m s).filter (fun p => output p.1 = output p.2)
def tags (m r s : ℕ) : Finset Tag :=
  ((Finset.range 3 ×ˢ Finset.range 3).sigma fun tu =>
    (collisions m (r-1+tu.1) (s-1+tu.2)).sigma fun p =>
      childChoices (p.1.drop (r-1)) ×ˢ childChoices (p.2.drop (s-1)))
def erase (r s : ℕ) (x : Tag) :=
  ((x.2.1.1.take (r-1),x.2.2.1),(x.2.1.2.take (s-1),x.2.2.2))

theorem mem_tags {m r s : ℕ} {x : Tag} : x ∈ tags m r s ↔
    x.1.1 < 3 ∧ x.1.2 < 3 ∧
    x.2.1.1 ∈ tuples m (r-1+x.1.1) ∧ x.2.1.2 ∈ tuples m (s-1+x.1.2) ∧
    output x.2.1.1 = output x.2.1.2 ∧
    childrenTuple x.2.2.1 = x.2.1.1.drop (r-1) ∧
    childrenTuple x.2.2.2 = x.2.1.2.drop (s-1) := by
  rcases x with ⟨tu,p,c⟩
  simp [tags,collisions,mem_childChoices_iff,and_assoc]

theorem split_data {m k t : ℕ} {F : Tuple} {c : Children}
    (hF : F ∈ tuples m (k+t)) (hc : childrenTuple c = F.drop k) :
    (F.take k).length = k ∧ childrenArity c = t ∧ F.take k ++ childrenTuple c = F := by
  have hl := (mem_tuples.mp hF).2.1
  refine ⟨by simp [hl],?_,?_⟩
  · rw [← childrenTuple_length,hc,List.length_drop,hl]; omega
  · rw [hc]; exact List.take_append_drop k F

theorem erase_mem {m r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    {x : Tag} (hx : x ∈ tags m r s) :
    (erase r s x).1.1.length+1 = r ∧ (erase r s x).2.1.length+1 = s ∧
    (erase r s x).1.1 ++ childrenTuple (erase r s x).1.2 ∈
      tuples m ((erase r s x).1.1.length+childrenArity (erase r s x).1.2) ∧
    (erase r s x).2.1 ++ childrenTuple (erase r s x).2.2 ∈
      tuples m ((erase r s x).2.1.length+childrenArity (erase r s x).2.2) ∧
    output ((erase r s x).1.1 ++ childrenTuple (erase r s x).1.2) =
      output ((erase r s x).2.1 ++ childrenTuple (erase r s x).2.2) := by
  rcases mem_tags.mp hx with ⟨_,_,hF,hG,he,hc,hd⟩
  obtain ⟨hl,ht,hf⟩ := split_data hF hc
  obtain ⟨hk,hu,hg⟩ := split_data hG hd
  dsimp [erase]
  exact ⟨by omega,by omega,by rw [hf,hl,ht]; exact hF,
    by rw [hg,hk,hu]; exact hG,by rw [hf,hg]; exact he⟩

def decorate {m r s : ℕ} (p : ReducedPairs m r s) : Tag :=
  ⟨(childrenArity p.val.1.2,childrenArity p.val.2.2),
    ⟨(p.val.1.1 ++ childrenTuple p.val.1.2,p.val.2.1 ++ childrenTuple p.val.2.2),
    (p.val.1.2,p.val.2.2)⟩⟩

theorem decorate_mem {m r s : ℕ} (p : ReducedPairs m r s) : decorate p ∈ tags m r s := by
  have hr : r-1 = p.val.1.1.length := by have := p.property.1; omega
  have hs : s-1 = p.val.2.1.length := by have := p.property.2.1; omega
  rw [mem_tags]
  dsimp [decorate]
  rw [hr,hs]
  refine ⟨?_,?_,p.property.2.2.1,p.property.2.2.2.1,p.property.2.2.2.2,?_,?_⟩
  · cases p.val.1.2 <;> simp [childrenArity]
  · cases p.val.2.2 <;> simp [childrenArity]
  · simp
  · simp

theorem erase_decorate {m r s : ℕ} (p : ReducedPairs m r s) : erase r s (decorate p) = p.val := by
  have hr : r-1 = p.val.1.1.length := by have := p.property.1; omega
  have hs : s-1 = p.val.2.1.length := by have := p.property.2.1; omega
  simp [erase,decorate,hr,hs]

theorem decorate_erase {m r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    {x : Tag} (hx : x ∈ tags m r s) :
    decorate (⟨erase r s x,erase_mem hr hs hx⟩ : ReducedPairs m r s) = x := by
  rcases mem_tags.mp hx with ⟨_,_,hF,hG,_,hc,hd⟩
  obtain ⟨_,ht,hf⟩ := split_data hF hc
  obtain ⟨_,hu,hg⟩ := split_data hG hd
  simp only [decorate,erase,ht,hu,hf,hg]

noncomputable def tagsEquiv (m r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    {x // x ∈ tags m r s} ≃ ReducedPairs m r s where
  toFun x := ⟨erase r s x.val,erase_mem hr hs x.property⟩
  invFun p := ⟨decorate p,decorate_mem p⟩
  left_inv x := Subtype.ext (decorate_erase hr hs x.property)
  right_inv p := Subtype.ext (erase_decorate p)

end StackSort.Del6
