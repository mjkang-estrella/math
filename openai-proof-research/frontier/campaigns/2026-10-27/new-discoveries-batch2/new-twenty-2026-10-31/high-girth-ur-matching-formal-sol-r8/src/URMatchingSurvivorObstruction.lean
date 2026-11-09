module
public import URMatchingSurvivorHoles
public import URMatchingBipartiteObstruction
public import URMatchingFinite
@[expose] public section
namespace URMatching
open scoped Classical

theorem survivor_across {N h : ℕ} (σ : PermutationTuples N 100) :
    AcrossPartition (survivorGraph h σ) LeftSurvivor := by
  intro u v huv
  rcases survivor_bipartite σ u v huv with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · exact iff_of_true hu hv
  · exact iff_of_false hu (not_not.mpr hv)

theorem survivor_no_rectangle {N h a : ℕ} (σ : PermutationTuples N 100)
    (hn : SurvivorNoHole h a σ) (A B : Finset (Survivor h σ))
    (hA : A.card = a) (hB : B.card = a)
    (hl : ∀ v ∈ A, LeftSurvivor v) (hr : ∀ v ∈ B, ¬ LeftSurvivor v) :
    ∃ u ∈ A, ∃ v ∈ B, (survivorGraph h σ).Adj u v := by
  classical
  have ex (u : A) : ∃ x : Fin N, u.val.val = Sum.inl x := hl u.val u.property
  have ey (v : B) : ∃ y : Fin N, v.val.val = Sum.inr y := by
    have hv := hr v.val v.property
    cases he : v.val.val with
    | inl x => exact False.elim (hv ⟨x,he⟩)
    | inr y => exact ⟨y,rfl⟩
  choose x hx using ex
  choose y hy using ey
  have xi : Function.Injective x := by
    intro u v he
    apply Subtype.ext; apply Subtype.ext
    exact (hx u).trans ((congrArg Sum.inl he).trans (hx v).symm)
  have yi : Function.Injective y := by
    intro u v he
    apply Subtype.ext; apply Subtype.ext
    exact (hy u).trans ((congrArg Sum.inr he).trans (hy v).symm)
  let X := Finset.univ.image x
  let Y := Finset.univ.image y
  have hX : X.card = a := by simpa [X, Finset.card_image_of_injective _ xi] using hA
  have hY : Y.card = a := by simpa [Y, Finset.card_image_of_injective _ yi] using hB
  obtain ⟨u,v,⟨i,hi,hui⟩,⟨j,hj,hvj⟩,huv⟩ := hn X Y hX hY
    (by intro i hi; obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hi
        rw [← hx w]; exact w.val.property)
    (by intro j hj; obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hj
        rw [← hy w]; exact w.val.property)
  obtain ⟨u',_,hui'⟩ := Finset.mem_image.mp hi
  obtain ⟨v',_,hvj'⟩ := Finset.mem_image.mp hj
  have hu : u = u'.val := Subtype.ext (hui.trans ((congrArg Sum.inl hui'.symm).trans (hx u').symm))
  have hv : v = v'.val := Subtype.ext (hvj.trans ((congrArg Sum.inr hvj'.symm).trans (hy v').symm))
  exact ⟨u'.val,u'.property,v'.val,v'.property,hu ▸ hv ▸ huv⟩

theorem survivor_ur_card_lt {N h a : ℕ} (σ : PermutationTuples N 100)
    (hn : SurvivorNoHole h a σ) (M : Finset (Sym2 (Survivor h σ)))
    (hm : IsUR (survivorGraph h σ) M) : M.card < 2*a := by
  classical
  by_contra hc
  have ha : a ≤ M.card / 2 := by omega
  obtain ⟨A,B,hA,hB,hl,hr,_,hempty⟩ :=
    ur_partition_empty_rectangle (survivorGraph h σ) LeftSurvivor (survivor_across σ) M hm
  obtain ⟨A',hsubA,hcardA⟩ := Finset.exists_subset_card_eq (hA ▸ ha)
  obtain ⟨B',hsubB,hcardB⟩ := Finset.exists_subset_card_eq (hB ▸ ha)
  obtain ⟨u,hu,v,hv,huv⟩ := survivor_no_rectangle σ hn A' B' hcardA hcardB
    (fun v hv => hl v (hsubA hv)) (fun v hv => hr v (hsubB hv))
  exact hempty u (hsubA hu) v (hsubB hv) huv

theorem survivor_ur_number_lt {N h a : ℕ} (σ : PermutationTuples N 100)
    (hn : SurvivorNoHole h a σ) : urMatchingNumber (survivorGraph h σ) < 2*a := by
  obtain ⟨M,hm,he⟩ := exists_maximum_urMatching (survivorGraph h σ)
  rw [← he]
  exact survivor_ur_card_lt σ hn M hm
end URMatching
