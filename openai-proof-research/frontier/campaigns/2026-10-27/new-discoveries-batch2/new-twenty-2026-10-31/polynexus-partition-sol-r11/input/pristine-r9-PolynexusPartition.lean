import PolynexusCount

/-!
# Zero-pair partition and transpose involution (MathDB 352496)

The ordered pairs of legal triples (the actual nonzero operands, via the
proved block bijection) split into the nonzero-product pairs `POv`, counted
by `psi`, and the zero-product pairs `PDisjT`.  A zero-product pair has the
first middle interval strictly left of the second (`PLeftT`) or conversely
(`PRightT`); disjoint and exhaustive.  The map `(x,y) |-> (y^t,x^t)` with
`(a,b,e)^t = (b,a,e)` is an involution carrying `PLeftT` onto `PRightT`,
so the zero classes have equal size.  Transported to genuine matrices this
gives `psi n + 2 * card (PLeftM n) = (card (PNZ n))^2`.
-/

/-- Triple transpose `(a,b,e)^t = (b,a,e)`. -/
def PTri (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (x.2.1, x.1, x.2.2)

theorem PTri_invol : ∀ x : ℕ × ℕ × ℕ, PTri (PTri x) = x := by
  rintro ⟨a, b, e⟩
  rfl

theorem PTri_inj : Function.Injective PTri := by
  intro x y h
  have h1 : PTri (PTri x) = PTri (PTri y) := by rw [h]
  rw [PTri_invol x, PTri_invol y] at h1
  exact h1

theorem PTri_mem {n : ℕ} {x : ℕ × ℕ × ℕ} (h : x ∈ PLeg n) : PTri x ∈ PLeg n := by
  obtain ⟨h1, h2, h3⟩ := PLeg_mem.1 h
  exact PLeg_mem.2 ⟨h1, h3, h2⟩

/-- Transposition of a coupled diagonal block swaps the first two
parameters: the entry condition is the same conjunction reordered. -/
theorem PBlk_trans (n a b e : ℕ) : (PBlk n a b e)ᵀ = PBlk n b a e := by
  funext r s
  rw [Matrix.transpose_apply, PBlk_apply, PBlk_apply]
  by_cases h : PCnd a b e (↑s) (↑r)
  · have h' : PCnd b a e ↑r ↑s := by
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      exact ⟨h3, h4, h1, h2, by omega⟩
    rw [if_pos h, if_pos h']
  · have h' : ¬ PCnd b a e ↑r ↑s := by
      intro hc
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      exact h ⟨h4, h3, h2, h1, by omega⟩
    rw [if_neg h, if_neg h']

/-- Ordered pairs of legal triples with zero product and the first middle
interval strictly left of the second. -/
def PLeftT (n : ℕ) : Finset ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  (PLeg n ×ˢ PLeg n).filter fun p => p.1.2.1 + p.1.2.2 < p.2.1

/-- Ordered pairs of legal triples with zero product and the second middle
interval strictly left of the first. -/
def PRightT (n : ℕ) : Finset ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  (PLeg n ×ˢ PLeg n).filter fun p => p.2.1 + p.2.2.2 < p.1.2.1

/-- Zero-product pairs of legal triples: precisely the non-overlapping ones. -/
def PDisjT (n : ℕ) : Finset ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  (PLeg n ×ˢ PLeg n).filter fun p =>
    ¬ (p.1.2.1 ≤ p.2.1 + p.2.2.2 ∧ p.2.1 ≤ p.1.2.1 + p.1.2.2)

theorem mem_leftT {n : ℕ} {p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)}
    (h : p ∈ PLeftT n) : p.1 ∈ PLeg n ∧ p.2 ∈ PLeg n ∧ p.1.2.1 + p.1.2.2 < p.2.1 := by
  obtain ⟨hmem, hcond⟩ := Finset.mem_filter.1 h
  obtain ⟨h1, h2⟩ := Finset.mem_product.1 hmem
  exact ⟨h1, h2, hcond⟩

theorem mem_leftT' {n : ℕ} {x y : ℕ × ℕ × ℕ}
    (hx : x ∈ PLeg n) (hy : y ∈ PLeg n) (hlt : x.2.1 + x.2.2 < y.1) :
    (x, y) ∈ PLeftT n := by
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, hy⟩, ?_⟩
  exact hlt

theorem mem_rightT {n : ℕ} {p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)}
    (h : p ∈ PRightT n) : p.1 ∈ PLeg n ∧ p.2 ∈ PLeg n ∧ p.2.1 + p.2.2.2 < p.1.2.1 := by
  obtain ⟨hmem, hcond⟩ := Finset.mem_filter.1 h
  obtain ⟨h1, h2⟩ := Finset.mem_product.1 hmem
  exact ⟨h1, h2, hcond⟩

theorem mem_rightT' {n : ℕ} {x y : ℕ × ℕ × ℕ}
    (hx : x ∈ PLeg n) (hy : y ∈ PLeg n) (hlt : y.1 + y.2.2 < x.2.1) :
    (x, y) ∈ PRightT n := by
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, hy⟩, ?_⟩
  exact hlt

/-- The pair swap `(x,y) |-> (y^t,x^t)` on ordered triples. -/
def PSwapT (p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :
    (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) := (PTri p.2, PTri p.1)

theorem PSwapT_invol : ∀ p, PSwapT (PSwapT p) = p := by
  intro p
  show (PTri (PTri p.1), PTri (PTri p.2)) = p
  rw [PTri_invol p.1, PTri_invol p.2]

theorem PSwapT_inj : Function.Injective PSwapT := by
  intro p q h
  have h1 : PSwapT (PSwapT p) = PSwapT (PSwapT q) := by rw [h]
  rw [PSwapT_invol p, PSwapT_invol q] at h1
  exact h1

/-- The swap carries left zero pairs to right zero pairs. -/
theorem PSwapT_left_right {n : ℕ} {p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)}
    (h : p ∈ PLeftT n) : PSwapT p ∈ PRightT n := by
  obtain ⟨hx, hy, hlt⟩ := mem_leftT h
  exact mem_rightT' (PTri_mem hy) (PTri_mem hx) hlt

/-- and conversely, by involutivity of the swap. -/
theorem PSwapT_right_left {n : ℕ} {p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)}
    (h : p ∈ PRightT n) : PSwapT p ∈ PLeftT n := by
  obtain ⟨hx, hy, hlt⟩ := mem_rightT h
  exact mem_leftT' (PTri_mem hy) (PTri_mem hx) hlt

theorem PLeftR_disjoint (n : ℕ) : Disjoint (PLeftT n) (PRightT n) := by
  refine Finset.disjoint_left.2 fun p h1 h2 => ?_
  obtain ⟨_, _, hl⟩ := mem_leftT h1
  obtain ⟨_, _, hr⟩ := mem_rightT h2
  omega

theorem PDisjT_union (n : ℕ) : PDisjT n = PLeftT n ∪ PRightT n := by
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]
  push_neg
  tauto

theorem PDisjT_card (n : ℕ) :
    (PDisjT n).card = (PLeftT n).card+(PRightT n).card := by
  rw [PDisjT_union, Finset.card_union_of_disjoint (PLeftR_disjoint n)]

theorem PDisjT_compl (n : ℕ) :
    (PLeg n ×ˢ PLeg n) = (POv n) ∪ PDisjT n := by
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]
  by_cases h : p.1.2.1 ≤ p.2.1 + p.2.2.2 ∧ p.2.1 ≤ p.1.2.1 + p.1.2.2
  · simp [h, POv]
  · simp [h, POv, PDisjT]

theorem PUniv_card (n : ℕ) :
    (PLeg n ×ˢ PLeg n).card = (POv n).card+(PDisjT n).card := by
  have hd : Disjoint (POv n) (PDisjT n) := by
    refine Finset.disjoint_left.2 fun p h1 h2 => ?_
    obtain ⟨_, hov⟩ := Finset.mem_filter.1 h1
    obtain ⟨_, hdis⟩ := Finset.mem_filter.1 h2
    exact hdis hov
  rw [← PDisjT_compl n, Finset.card_union_of_disjoint hd]

/-- The swap is an involution of the zero pairs carrying `PLeftT` onto
`PRightT`, so the classes have equal cardinality. -/
theorem PLeftT_card_right (n : ℕ) : (PLeftT n).card = (PRightT n).card := by
  have key : PRightT n = (PLeftT n).image PSwapT := by
    ext q
    constructor
    · intro hq
      refine Finset.mem_image.2 ⟨PSwapT q, PSwapT_right_left hq, ?_⟩
      rw [PSwapT_invol]
    · intro hq
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.1 hq
      rw [← heq]
      exact PSwapT_left_right hp
  have hinj : Set.InjOn PSwapT ↑(PLeftT n) := fun a _ b _ h => PSwapT_inj h
  rw [key, Finset.card_image_of_injOn hinj]

/-- Matrix level: the ordered pairs of genuine nonzero matrices coming from
left zero pairs. -/
def PLeftM (n : ℕ) : Finset (Matrix (Fin n) (Fin n) ℕ × Matrix (Fin n) (Fin n) ℕ) :=
  (PLeftT n).image fun p => (PB n p.1, PB n p.2)

/-- Matrix level: the right zero pairs. -/
def PRightM (n : ℕ) : Finset (Matrix (Fin n) (Fin n) ℕ × Matrix (Fin n) (Fin n) ℕ) :=
  (PRightT n).image fun p => (PB n p.1, PB n p.2)

theorem PLeftM_card (n : ℕ) : (PLeftM n).card = (PLeftT n).card := by
  rw [PLeftM, Finset.card_image_of_injOn]
  intro x _ y _ hxy
  obtain ⟨hx1, hx2, _⟩ := mem_leftT (Finset.mem_coe.1 ‹_›)
  · obtain ⟨hy1, hy2, _⟩ := mem_leftT (Finset.mem_coe.1 ‹_›)
    have h1 : PB n x.1 = PB n y.1 := congrArg Prod.fst hxy
    have h2 : PB n x.2 = PB n y.2 := congrArg Prod.snd hxy
    obtain e1 := PB_inj hx1 hx2 h1
    obtain e2 := PB_inj hx2 hy2 h2
    rw [show x = (x.1, x.2) from rfl, show y = (y.1, y.2) from rfl, e1, e2]

/-- The zero pairs of genuine matrices are exactly the images of the
disjoint triple pairs: the matrix product is zero exactly when the middle
intervals are disjoint. -/
theorem PZeroM_eq (n : ℕ) :
    ((PNZ n) ×ˢ (PNZ n)).filter (fun p : _ × _ => p.1 * p.2 = 0) =
      (PDisjT n).image (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => (PB n p.1, PB n p.2)) := by
  ext q
  constructor
  · intro h
    obtain ⟨hmem, hzero⟩ := Finset.mem_filter.1 h
    obtain ⟨hx, hy⟩ := Finset.mem_product.1 hmem
    obtain ⟨x, hxmem, hxe⟩ := Finset.mem_image.1 hx
    obtain ⟨y, hymem, hye⟩ := Finset.mem_image.1 hy
    refine Finset.mem_image.2 ⟨(x, y), ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hxmem, hymem⟩, ?_⟩
      show ¬ (x.2.1 ≤ y.1+y.2.2 ∧ y.1 ≤ x.2.1+x.2.2)
      intro hov
      exact hzero (PBlk_mul_nonzero n x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2
        ⟨(PLeg_leg hxmem).1,(PLeg_leg hxmem).2,(PLeg_leg hymem).1,(PLeg_leg hymem).2⟩ hov)
    · show (PB n x, PB n y) = q
      rw [show q = (q.1, q.2) from rfl, ← hxe, ← hye]
  · intro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.1 h
    obtain ⟨hmem, hdis⟩ := Finset.mem_filter.1 hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.1 hmem
    have e1 : PB n p.1 = q.1 := congrArg Prod.fst heq
    have e2 : PB n p.2 = q.2 := congrArg Prod.snd heq
    refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · refine Finset.mem_product.2 ⟨?_, ?_⟩
      · exact Finset.mem_image.2 ⟨p.1, hx, e1⟩
      · exact Finset.mem_image.2 ⟨p.2, hy, e2⟩
    · rw [← e1, ← e2]
      exact PBlk_mul_disjoint_zero n p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2
        ⟨(PLeg_leg hx).1,(PLeg_leg hx).2,(PLeg_leg hy).1,(PLeg_leg hy).2⟩ hdis

/-- The exact partition signature: the nonzero-pair count plus twice the
left zero pairs equals the square of the number of nonzero operands. -/
theorem partition_card (n : ℕ) :
    psi n+2 * (PLeftM n).card = (PNZ n).card ^ 2 := by
  have h1 : (PNZ n).card ^ 2 = (PLeg n ×ˢ PLeg n).card := by
    rw [Finset.card_product, PNZ_card]
  rw [h1, PUniv_card, PDisjT_card, PLeftM_card, psi_eq]
  ring
