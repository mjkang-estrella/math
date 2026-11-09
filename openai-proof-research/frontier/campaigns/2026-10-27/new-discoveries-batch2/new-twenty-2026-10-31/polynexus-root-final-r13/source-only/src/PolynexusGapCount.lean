import PolynexusGap

/-- A triangular set of the first two gaps; the third is the remainder. -/
def PGT (t : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (t+1)).biUnion fun x =>
    (Finset.range (t+1-x)).image fun y => (x,y)

theorem PGT_mem {t : ℕ} {p : ℕ × ℕ} : p ∈ PGT t ↔ p.1+p.2 ≤ t := by
  simp only [PGT, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x,hx,y,hy,he⟩
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp at h1 h2
    omega
  · intro h
    exact ⟨p.1, by omega, p.2, by omega, rfl⟩

theorem PGT_card (t : ℕ) : 2*(PGT t).card = (t+1)*(t+2) := by
  have hd : (Finset.range (t+1) : Set ℕ).PairwiseDisjoint
      (fun x => (Finset.range (t+1-x)).image fun y => (x,y)) := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.2
    intro p hp hq
    obtain ⟨a,_,ha⟩ := Finset.mem_image.1 hp
    obtain ⟨b,_,hb⟩ := Finset.mem_image.1 hq
    exact hxy (congrArg Prod.fst (ha.trans hb.symm))
  have hc : ∀ x : ℕ, ((Finset.range (t+1-x)).image fun y => (x,y)).card = t+1-x := by
    intro x
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h), Finset.card_range]
  rw [PGT, Finset.card_biUnion hd]
  simp only [hc]
  exact legLin (t+1)

/-- Fiber with fixed length-minus-one coordinates. -/
def PGF (n e f : ℕ) : Finset PGapData :=
  ((PGT (n-e-f-2)) ×ˢ (Finset.range (n-e) ×ˢ Finset.range (n-f))).image
    fun p => ((p.1.1,p.1.2,n-e-f-2-p.1.1-p.1.2),(e,f),p.2)

theorem PGF_mem {n e f : ℕ} (hef : e+f+2 ≤ n) {g : PGapData} :
    g ∈ PGF n e f ↔ g ∈ PGap n ∧ g.2.1 = (e,f) := by
  constructor
  · intro hg
    obtain ⟨⟨⟨x,y⟩,⟨a,b⟩⟩,hp,he⟩ := Finset.mem_image.1 hg
    rcases Finset.mem_product.1 hp with ⟨hxy,hab⟩
    have ht := PGT_mem.1 hxy
    have ha := Finset.mem_range.1 (Finset.mem_product.1 hab).1
    have hb := Finset.mem_range.1 (Finset.mem_product.1 hab).2
    rw [← he]
    refine ⟨PGap_mem.2 ?_, rfl⟩
    dsimp at ht ha hb ⊢
    omega
  · rintro ⟨hg,he⟩
    have h := PGap_mem.1 hg
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    dsimp at he1 he2
    refine Finset.mem_image.2 ⟨((g.1.1,g.1.2.1),g.2.2), ?_, ?_⟩
    · apply Finset.mem_product.2
      refine ⟨PGT_mem.2 ?_, Finset.mem_product.2 ⟨Finset.mem_range.2 ?_,Finset.mem_range.2 ?_⟩⟩ <;> dsimp <;> omega
    · apply Prod.ext
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · dsimp
            omega
      · exact Prod.ext he.symm rfl

theorem PGF_card (n e f : ℕ) :
    (PGF n e f).card = (PGT (n-e-f-2)).card*(n-e)*(n-f) := by
  have hi : Function.Injective (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      ((p.1.1,p.1.2,n-e-f-2-p.1.1-p.1.2),(e,f),p.2)) := by
    intro p q h
    apply Prod.ext
    · exact Prod.ext (congrArg (fun g : PGapData => g.1.1) h)
        (congrArg (fun g : PGapData => g.1.2.1) h)
    · exact congrArg (fun g : PGapData => g.2.2) h
  rw [PGF, Finset.card_image_of_injective _ hi, Finset.card_product,
    Finset.card_product, Finset.card_range, Finset.card_range]
  ring

def PLengths (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter fun p => p.1+p.2+2 ≤ n

theorem PLengths_mem {n : ℕ} {p : ℕ × ℕ} : p ∈ PLengths n ↔ p.1+p.2+2 ≤ n := by
  simp only [PLengths, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem PGap_fibers (n : ℕ) : PGap n = (PLengths n).biUnion fun p => PGF n p.1 p.2 := by
  ext g
  constructor
  · intro hg
    have h := PGap_mem.1 hg
    have hl : g.2.1 ∈ PLengths n := PLengths_mem.2 (by omega)
    exact Finset.mem_biUnion.2 ⟨g.2.1,hl,(PGF_mem (PLengths_mem.1 hl)).2 ⟨hg,rfl⟩⟩
  · intro hg
    obtain ⟨p,hp,hg⟩ := Finset.mem_biUnion.1 hg
    exact ((PGF_mem (PLengths_mem.1 hp)).1 hg).1

theorem PGap_card_sum (n : ℕ) : (PGap n).card =
    ∑ p ∈ PLengths n, (PGT (n-p.1-p.2-2)).card*(n-p.1)*(n-p.2) := by
  have hd : (PLengths n : Set (ℕ × ℕ)).PairwiseDisjoint (fun p => PGF n p.1 p.2) := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.2
    intro g hg hk
    have h1 := ((PGF_mem (PLengths_mem.1 hp)).1 hg).2
    have h2 := ((PGF_mem (PLengths_mem.1 hq)).1 hk).2
    exact hpq (h1.symm.trans h2)
  rw [PGap_fibers, Finset.card_biUnion hd]
  exact Finset.sum_congr rfl fun p _ => PGF_card n p.1 p.2

/-- The actual matrix zero-pair cardinality is the finite gap convolution.
The triangular factor is certified by `PGT_card`. -/
theorem PLeftM_card_sum (n : ℕ) : (PLeftM n).card =
    ∑ p ∈ PLengths n, (PGT (n-p.1-p.2-2)).card*(n-p.1)*(n-p.2) := by
  rw [PLeftM_card_gap, PGap_card_sum]
