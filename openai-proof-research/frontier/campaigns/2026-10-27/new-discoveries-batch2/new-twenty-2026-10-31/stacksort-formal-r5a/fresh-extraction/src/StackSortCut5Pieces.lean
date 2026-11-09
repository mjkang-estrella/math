import StackSortCut5Labels

noncomputable section
namespace StackSort.Cut5
open Seeds2 Shuffle3 Round4
open Classical BigOperators
abbrev Tuple := List (List ℕ)
abbrev Pair := Tuple × Tuple
abbrev Index := ℕ × ℕ × ℕ × Finset ℕ

def indices (M r s : ℕ) : Finset Index :=
  ((Finset.Ico 1 M) ×ˢ (Finset.Ico 1 r) ×ˢ (Finset.Ico 1 s) ×ˢ
    (Finset.range M).powerset).filter (fun i => i.2.2.2.card = i.1)

def pieces (M r s : ℕ) := (indices M r s).sigma fun i =>
  labelledPairs (Finset.range M \ i.2.2.2) (r-i.2.1) (s-i.2.2.1) ×ˢ
    labelledIrreducibles i.2.2.2 i.2.1 i.2.2.1

def glue (p : Sigma (fun _ : Index => Pair × Pair)) : Pair :=
  (p.2.1.1 ++ p.2.2.1, p.2.1.2 ++ p.2.2.2)

def reducibles (M r s : ℕ) : Finset Pair :=
  (labelledPairs (Finset.range M) r s).filter (fun p => ¬ Irreducible p.1 p.2)

theorem mem_indices {M r s : ℕ} {i : Index} : i ∈ indices M r s ↔
    (1 ≤ i.1 ∧ i.1 < M) ∧ (1 ≤ i.2.1 ∧ i.2.1 < r) ∧
    (1 ≤ i.2.2.1 ∧ i.2.2.1 < s) ∧ i.2.2.2 ⊆ Finset.range M ∧ i.2.2.2.card = i.1 := by
  simp [indices, and_assoc]

theorem mem_pairs {A : Finset ℕ} {r s : ℕ} {p : Pair} :
    p ∈ labelledPairs A r s ↔ p.1 ∈ labelledTuples A r ∧
      p.2 ∈ labelledTuples A s ∧ output p.1 = output p.2 := by
  simp [labelledPairs, and_assoc]

theorem mem_irreducibles {A : Finset ℕ} {r s : ℕ} {p : Pair} :
    p ∈ labelledIrreducibles A r s ↔ p.1 ∈ labelledTuples A r ∧
      p.2 ∈ labelledTuples A s ∧ output p.1 = output p.2 ∧ Irreducible p.1 p.2 := by
  simp [labelledIrreducibles, and_assoc]

/-- Concatenation of two prescribed-label pieces lands in the reducible collision family. -/
theorem glue_mem {M r s : ℕ} {p : Sigma (fun _ : Index => Pair × Pair)}
    (hp : p ∈ pieces M r s) : glue p ∈ reducibles M r s := by
  obtain ⟨hi,hp,hq⟩ := (by simpa only [pieces,Finset.mem_sigma,Finset.mem_product] using hp)
  rcases mem_indices.mp hi with ⟨hb,ha,hc,hA,hcard⟩
  rcases mem_pairs.mp hp with ⟨hU,hV,he⟩
  rcases mem_irreducibles.mp hq with ⟨hB,hD,hbd,hI⟩
  have hd : Disjoint (Finset.range M \ p.1.2.2.2) p.1.2.2.2 := Finset.sdiff_disjoint
  have hu := labelled_append hU hB hd
  have hv := labelled_append hV hD hd
  rw [Finset.sdiff_union_of_subset hA] at hu hv
  have hlr : r-p.1.2.1+p.1.2.1 = r := by omega
  have hls : s-p.1.2.2.1+p.1.2.2.1 = s := by omega
  rw [hlr] at hu
  rw [hls] at hv
  apply Finset.mem_filter.mpr
  refine ⟨mem_pairs.mpr ⟨hu,hv,by simp only [glue,output_append,he,hbd]⟩, ?_⟩
  intro hi
  have hpos : 0 < (output p.2.1.1).length := by
    have hl := (mem_labelledTuples.mp hU).2.1
    have hne : p.2.1.1 ≠ [] := by intro hz; simp [hz] at hl; omega
    exact output_length_pos (mem_labelledTuples.mp hU).2.2 hne
  have hbpos : 0 < (output p.2.2.1).length := by rw [labelled_length hB,hcard]; omega
  exact hi _ ⟨_,_,rfl,rfl⟩ ⟨_,_,rfl,congrArg List.length he.symm⟩ hpos
    (by simp only [glue,output_append,List.length_append]; omega)

/-- Uniqueness retains all indices: suffix support and tuple lengths recover the tags. -/
theorem glue_injective {M r s : ℕ}
    {p q : Sigma (fun _ : Index => Pair × Pair)}
    (hp : p ∈ pieces M r s) (hq : q ∈ pieces M r s) (he : glue p = glue q) : p = q := by
  obtain ⟨hpi,hpp,hpb⟩ := (by simpa only [pieces,Finset.mem_sigma,Finset.mem_product] using hp)
  obtain ⟨hqi,hqp,hqb⟩ := (by simpa only [pieces,Finset.mem_sigma,Finset.mem_product] using hq)
  have ip := mem_indices.mp hpi
  have iq := mem_indices.mp hqi
  have pp := mem_pairs.mp hpp
  have qp := mem_pairs.mp hqp
  have pb := mem_irreducibles.mp hpb
  have qb := mem_irreducibles.mp hqb
  have hm := (mem_pairs.mp (Finset.mem_filter.mp (glue_mem hp)).1)
  have hnF := (mem_labelledTuples.mp hm.1).2.2
  have hnG := (mem_labelledTuples.mp hm.2.1).2.2
  have h := irreducible_suffix_unique hnF hnG rfl rfl pp.2.2
    (by rw [labelled_length pb.1,ip.2.2.2.2]; omega) pb.2.2.2
    (congrArg Prod.fst he) (congrArg Prod.snd he) qp.2.2
    (by rw [labelled_length qb.1,iq.2.2.2.2]; omega) qb.2.2.2
  have hA : p.1.2.2.2 = q.1.2.2.2 := by
    rw [← support_eq pb.1,← support_eq qb.1,h.2.1]
  have ha : p.1.2.1 = q.1.2.1 := by
    rw [← (mem_labelledTuples.mp pb.1).2.1,← (mem_labelledTuples.mp qb.1).2.1,h.2.1]
  have hc : p.1.2.2.1 = q.1.2.2.1 := by
    rw [← (mem_labelledTuples.mp pb.2.1).2.1,← (mem_labelledTuples.mp qb.2.1).2.1,h.2.2.2]
  have hb : p.1.1 = q.1.1 := by rw [← ip.2.2.2.2,← iq.2.2.2.2,hA]
  have hidx : p.1 = q.1 := Prod.ext hb (Prod.ext ha (Prod.ext hc hA))
  have hval : p.2 = q.2 := Prod.ext (Prod.ext h.1 h.2.2.1) (Prod.ext h.2.1 h.2.2.2)
  exact Sigma.ext hidx (heq_of_eq hval)

/-- Every reducible collision is obtained from a labelled remainder and final block. -/
theorem glue_surjective {M r s : ℕ} {q : Pair} (hq : q ∈ reducibles M r s)
    (hM : 0 < M) : ∃ p ∈ pieces M r s, glue p = q := by
  rcases Finset.mem_filter.mp hq with ⟨hq,hir⟩
  rcases mem_pairs.mp hq with ⟨hF,hG,he⟩
  have hnF := (mem_labelledTuples.mp hF).2.2
  have hnG := (mem_labelledTuples.mp hG).2.2
  obtain ⟨p⟩ := finalBlock_exists he (by rw [labelled_length hF,Finset.card_range]; exact hM)
  have hFl : p.leftPrefix ++ p.leftBlock ∈ labelledTuples (Finset.range M) r := p.left_eq ▸ hF
  have hGl : p.rightPrefix ++ p.rightBlock ∈ labelledTuples (Finset.range M) s := p.right_eq ▸ hG
  rcases labelled_split hFl with ⟨hU,hB,hd,hcomp⟩
  rcases labelled_split hGl with ⟨hV,hD,_,_⟩
  have hBD := support_collision p.block_collision
  have hUV := support_collision p.prefix_collision
  rw [← hBD] at hD
  rw [← hUV,hcomp] at hV
  rw [hcomp] at hU
  have hneU : p.leftPrefix ≠ [] := by
    intro hz
    have hzV : p.rightPrefix = [] := by
      apply (output_eq_nil_iff (mem_labelledTuples.mp hV).2.2).mp
      rw [← p.prefix_collision,hz]; rfl
    exact hir ((finalBlock_irreducible_iff hnF hnG p).mpr ⟨hz,hzV⟩)
  have hneV : p.rightPrefix ≠ [] := by
    intro hz
    apply hneU
    apply (output_eq_nil_iff (mem_labelledTuples.mp hU).2.2).mp
    rw [p.prefix_collision,hz]; rfl
  have hpre := output_length_pos (mem_labelledTuples.mp hU).2.2 hneU
  have hlenF : p.leftPrefix.length + p.leftBlock.length = r := by
    simpa only [List.length_append] using (mem_labelledTuples.mp hFl).2.1
  have hlenG : p.rightPrefix.length + p.rightBlock.length = s := by
    simpa only [List.length_append] using (mem_labelledTuples.mp hGl).2.1
  have hneB : p.leftBlock ≠ [] := by intro hz; have := p.block_pos; simp [hz,output] at this
  have hneD : p.rightBlock ≠ [] := by
    intro hz; have := p.block_pos; rw [p.block_collision,hz] at this; simp [output] at this
  have hbpos : 0 < (support p.leftBlock).card := by
    rw [← labelled_length hB]; exact p.block_pos
  have hbM : (support p.leftBlock).card < M := by
    have ht := labelled_length hFl
    rw [output_append,List.length_append,labelled_length hB,Finset.card_range] at ht
    omega
  have hsub : support p.leftBlock ⊆ Finset.range M := by
    have ht := support_eq hFl
    rw [support_append] at ht
    rw [← ht]
    exact Finset.subset_union_right
  let i : Index := ((support p.leftBlock).card,p.leftBlock.length,p.rightBlock.length,support p.leftBlock)
  have hi : i ∈ indices M r s := by
    apply mem_indices.mpr
    refine ⟨⟨by exact hbpos,by exact hbM⟩,?_,?_,hsub,rfl⟩
    · have := List.length_pos_iff.mpr hneB
      have := List.length_pos_iff.mpr hneU
      dsimp [i]; omega
    · have := List.length_pos_iff.mpr hneD
      have := List.length_pos_iff.mpr hneV
      dsimp [i]; omega
  refine ⟨⟨i,((p.leftPrefix,p.rightPrefix),(p.leftBlock,p.rightBlock))⟩,?_,?_⟩
  · apply Finset.mem_sigma.mpr
    refine ⟨hi,Finset.mem_product.mpr ⟨?_,?_⟩⟩
    · apply mem_pairs.mpr
      have hr : r-p.leftBlock.length = p.leftPrefix.length := by omega
      have hs : s-p.rightBlock.length = p.rightPrefix.length := by omega
      simpa only [i,hr,hs] using And.intro hU (And.intro hV p.prefix_collision)
    · exact mem_irreducibles.mpr ⟨hB,hD,p.block_collision,p.block_irreducible⟩
  · exact Prod.ext p.left_eq.symm p.right_eq.symm

/-- Literal finite bijection, before any rearrangement of the counting sums. -/
theorem pieces_card (M r s : ℕ) (hM : 0 < M) :
    (pieces M r s).card = (reducibles M r s).card := by
  apply Finset.card_bij (fun p _ => glue p)
  · exact fun _ hp => glue_mem hp
  · exact fun _ hp _ hq he => glue_injective hp hq he
  · intro q hq
    obtain ⟨p,hp,he⟩ := glue_surjective hq hM
    exact ⟨p,hp,he⟩

/-- Splitting into irreducible and reducible collisions is an additive identity in ℕ. -/
theorem XI_partition (M r s : ℕ) : XI M r s = II M r s + (reducibles M r s).card := by
  have he : (labelledIrreducibles (Finset.range M) r s) =
      (labelledPairs (Finset.range M) r s).filter (fun p => Irreducible p.1 p.2) := by
    ext p
    simp [mem_pairs,mem_irreducibles,and_assoc]
  have hc := Finset.card_filter_add_card_filter_not (s := labelledPairs (Finset.range M) r s)
    (p := fun p => Irreducible p.1 p.2)
  rw [← he,labelledIrreducibles_card,Finset.card_range] at hc
  simpa only [labelledPairs_card,Finset.card_range,reducibles] using hc.symm

end StackSort.Cut5
