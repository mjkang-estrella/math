import StackSortShuffle3Core
noncomputable section
namespace StackSort.Shuffle3
 theorem labelled_root_mem {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n)
    {L R : List ℕ} (hL : L ∈ labelWords A)
    (hR : R ∈ labelWords (Finset.range n \ A)) :
    rootGlue n (L,R) ∈ words (n+1) := by
  have hLn := labelWords_nodup hL
  have hRn := labelWords_nodup hR
  have hdis : ∀ x ∈ L, ∀ y ∈ R, x ≠ y := by
    intro x hx y hy he
    subst y
    have hxA : x ∈ A := by rw [← labelWords_support hL]; simpa using hx
    have hxR : x ∈ Finset.range n \ A := by rw [← labelWords_support hR]; simpa using hy
    exact (Finset.mem_sdiff.mp hxR).2 hxA
  have hp : (L ++ R).Perm (List.range n) := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_append.mpr ⟨hLn,hRn,hdis⟩) List.nodup_range).mpr
    intro x
    have hset : x ∈ L ↔ x ∈ A := by rw [← labelWords_support hL]; simp
    have hrset : x ∈ R ↔ x ∈ Finset.range n \ A := by rw [← labelWords_support hR]; simp
    simp only [List.mem_append, hset, hrset, Finset.mem_sdiff, List.mem_range]
    constructor
    · rintro (hx | ⟨hx,_⟩)
      · exact Finset.mem_range.mp (hA hx)
      · exact Finset.mem_range.mp hx
    · intro hx
      by_cases ha : x ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨Finset.mem_range.mpr hx,ha⟩
  apply mem_words.mpr
  rw [List.range_succ]
  have hr : (rootGlue n (L,R)).Perm ((L ++ R) ++ [n]) := by
    simpa [rootGlue, List.append_assoc] using
      (List.Perm.refl L).append (List.perm_append_comm (l₁ := [n]) (l₂ := R))
  exact hr.trans (hp.append_right [n])

def rootPair (n : ℕ) (p : Σ _A : Finset ℕ,
    (List ℕ × List ℕ) × (List ℕ × List ℕ)) : List ℕ × List ℕ :=
  (rootGlue n (p.2.1.1,p.2.2.1), rootGlue n (p.2.1.2,p.2.2.2))

 theorem rootPair_mem {n i : ℕ} {p} (hp : p ∈ shuffleDomain n i) :
    rootPair n p ∈ (words (n+1) ×ˢ words (n+1)).filter (fun q => s q.1 = s q.2) := by
  obtain ⟨hA,hp⟩ := Finset.mem_sigma.mp hp
  have hsub := (Finset.mem_powersetCard.mp hA).1
  obtain ⟨hpL,hpR⟩ := Finset.mem_product.mp hp
  obtain ⟨hLL,hsL⟩ := Finset.mem_filter.mp hpL
  obtain ⟨hRR,hsR⟩ := Finset.mem_filter.mp hpR
  obtain ⟨hL,hL'⟩ := Finset.mem_product.mp hLL
  obtain ⟨hR,hR'⟩ := Finset.mem_product.mp hRR
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨labelled_root_mem hsub hL hR, labelled_root_mem hsub hL' hR'⟩,?_⟩
  dsimp [rootPair,rootGlue]
  rw [s_split _ _ _ (labelWords_below hsub hL)
      (fun x hx => (labelWords_below Finset.sdiff_subset hR x hx).le),
    s_split _ _ _ (labelWords_below hsub hL')
      (fun x hx => (labelWords_below Finset.sdiff_subset hR' x hx).le), hsL, hsR]

 theorem rootPair_injOn (n i : ℕ) : Set.InjOn (rootPair n) (shuffleDomain n i) := by
  intro p hp q hq he
  have pL := Finset.mem_product.mp (Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_sigma.mp hp).2).1).1
  have qL := Finset.mem_product.mp (Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_sigma.mp hq).2).1).1
  have psub := (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hp).1).1
  have qsub := (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hq).1).1
  have h1 := rootGlue_injective n (labelWords_below psub pL.1)
    (labelWords_below qsub qL.1) (congrArg Prod.fst he)
  have h2 := rootGlue_injective n (labelWords_below psub pL.2)
    (labelWords_below qsub qL.2) (congrArg Prod.snd he)
  have hA : p.1 = q.1 := by
    rw [← labelWords_support pL.1, ← labelWords_support qL.1, h1.1]
  cases p with
  | mk A p =>
    cases q with
    | mk B q =>
      dsimp at hA
      subst B
      exact congrArg (Sigma.mk A) (Prod.ext (Prod.ext h1.1 h2.1) (Prod.ext h1.2 h2.2))

 theorem choose_split_bound (n i : ℕ) :
    Nat.choose n i * P i * P (n-i) ≤ P (n+1) := by
  rw [← shuffleDomain_card]
  exact Finset.card_le_card_of_injOn (rootPair n) (fun _ hp => rootPair_mem hp) (rootPair_injOn n i)
end StackSort.Shuffle3
