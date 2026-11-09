import PolynexusSrcPrd

/-!
# The actual nonzero pair set (MathDB 352496)

`PLeg n` is the finite set of legal zero-based parameter triples, `PNZ n`
the finite set of actual nonzero block matrices, and `psi n` the number of
ordered pairs of nonzero matrices whose ordinary product is nonzero.  The
reduction lemma expresses `psi n` as the cardinality of an explicit finite
tuple set with the overlap condition; no polynomial or proxy definition.
-/

/-- Legal triples `(a,b,e)` with `a+e+1 <= n` and `b+e+1 <= n`. -/
def PLeg (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range n).biUnion fun e =>
    (Finset.range (n - e) ×ˢ Finset.range (n - e)).image fun ab => (ab.1, ab.2, e)

theorem PLeg_mem {n : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ PLeg n ↔ t.2.2 < n ∧ t.1 < n - t.2.2 ∧ t.2.1 < n - t.2.2 := by
  constructor
  · intro h
    obtain ⟨e, he, hab⟩ := Finset.mem_biUnion.1 h
    obtain ⟨ab, hab', heq⟩ := Finset.mem_image.1 hab
    obtain ⟨hab1, hab2⟩ := Finset.mem_product.1 hab'
    have h22 : t.2.2 = e := by rw [← heq]
    have h11 : t.1 = ab.1 := by rw [← heq]
    have h21 : t.2.1 = ab.2 := by rw [← heq]
    refine ⟨?_, ?_, ?_⟩
    · rw [h22]; exact Finset.mem_range.1 he
    · rw [h11, h22]; exact Finset.mem_range.1 hab1
    · rw [h21, h22]; exact Finset.mem_range.1 hab2
  · rintro ⟨h1, h2, h3⟩
    refine Finset.mem_biUnion.2 ⟨t.2.2, Finset.mem_range.2 h1, ?_⟩
    refine Finset.mem_image.2 ⟨(t.1, t.2.1),
      Finset.mem_product.2 ⟨Finset.mem_range.2 h2, Finset.mem_range.2 h3⟩, ?_⟩
    rfl

/-- Membership in `PLeg n` gives both legality inequalities. -/
theorem PLeg_leg {n : ℕ} {t : ℕ × ℕ × ℕ} (h : t ∈ PLeg n) :
    t.1 + t.2.2 + 1 ≤ n ∧ t.2.1 + t.2.2 + 1 ≤ n := by
  obtain ⟨h1, h2, h3⟩ := PLeg_mem.1 h
  exact ⟨by omega, by omega⟩

/-- The block matrix attached to a triple `(a,b,e)`. -/
def PB (n : ℕ) (x : ℕ × ℕ × ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  PBlk n x.1 x.2.1 x.2.2

/-- `PB` is injective on legal triples. -/
theorem PB_inj {n : ℕ} {x y : ℕ × ℕ × ℕ} (hx : x ∈ PLeg n) (hy : y ∈ PLeg n)
    (h : PB n x = PB n y) : x = y := by
  obtain ⟨h1, h2, h3⟩ := PBlk_inj (PLeg_leg hx) (PLeg_leg hy) h
  rw [show x = (x.1, x.2.1, x.2.2) from rfl, show y = (y.1, y.2.1, y.2.2) from rfl,
    h1, h2, h3]

/-- The nonzero block matrices, as a finite set of actual matrices. -/
def PNZ (n : ℕ) : Finset (Matrix (Fin n) (Fin n) ℕ) :=
  (PLeg n).image (PB n)

/-- The ordered pair of blocks attached to a pair of triples. -/
def PBPair (n : ℕ) (q : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :
    Matrix (Fin n) (Fin n) ℕ × Matrix (Fin n) (Fin n) ℕ :=
  (PB n q.1, PB n q.2)

/-- The ordered pairs of nonzero matrices with nonzero ordinary product. -/
def PNzPairs (n : ℕ) :
    Finset (Matrix (Fin n) (Fin n) ℕ × Matrix (Fin n) (Fin n) ℕ) :=
  ((PNZ n) ×ˢ (PNZ n)).filter fun p => p.1 * p.2 ≠ 0

/-- The Polynexus operand pair count, as an actual cardinality. -/
def psi (n : ℕ) : ℕ := (PNzPairs n).card

/-- The overlap condition on a pair of triples: the middle interval of the
first block meets the row interval of the second. -/
def POv (n : ℕ) : Finset ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=
  (PLeg n ×ˢ PLeg n).filter fun p =>
    p.1.2.1 ≤ p.2.1 + p.2.2.2 ∧ p.2.1 ≤ p.1.2.1 + p.1.2.2

/-- The exact reduction: the pair count equals the number of ordered pairs
of legal triples whose middle intervals overlap.  The matrix product
condition is equivalent to interval overlap, with both directions proved
from the exact entry formula. -/
theorem psi_eq (n : ℕ) : psi n = (POv n).card := by
  have hPNz : PNzPairs n
      = (POv n).image fun q : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) => (PB n q.1, PB n q.2) := by
    ext p
    constructor
    · intro h
      obtain ⟨hmemP, hcond⟩ := Finset.mem_filter.1 h
      obtain ⟨hX1, hY1⟩ := Finset.mem_product.1 hmemP
      obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 hX1
      obtain ⟨y, hy, hye⟩ := Finset.mem_image.1 hY1
      refine Finset.mem_image.2 ⟨(x, y), ?_, ?_⟩
      · refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, hy⟩, ?_⟩
        by_cases hov : x.2.1 ≤ y.1 + y.2.2 ∧ y.1 ≤ x.2.1 + x.2.2
        · exact hov
        · exfalso
          refine hcond ?_
          rw [← hxe, ← hye]
          exact PBlk_mul_disjoint_zero n x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2
            ⟨(PLeg_leg hx).1, (PLeg_leg hx).2, (PLeg_leg hy).1, (PLeg_leg hy).2⟩ hov
      · show (PB n x, PB n y) = p
        rw [show p = (p.1, p.2) from rfl, ← hxe, ← hye]
    · rintro ⟨q, hq, heq⟩
      obtain ⟨hmem, hov⟩ := Finset.mem_filter.1 hq
      obtain ⟨hx, hy⟩ := Finset.mem_product.1 hmem
      have e1 : PB n q.1 = p.1 := congrArg Prod.fst heq
      have e2 : PB n q.2 = p.2 := congrArg Prod.snd heq
      refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · refine Finset.mem_product.2 ⟨?_, ?_⟩
        · exact Finset.mem_image.2 ⟨q.1, hx, e1⟩
        · exact Finset.mem_image.2 ⟨q.2, hy, e2⟩
      · rw [← e1, ← e2]
        exact PBlk_mul_nonzero n q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.1 q.2.2
          ⟨(PLeg_leg hx).1, (PLeg_leg hx).2, (PLeg_leg hy).1, (PLeg_leg hy).2⟩ hov
  rw [psi, hPNz, Finset.card_image_of_injOn]
  intro x y hx hy h
  obtain ⟨hxP, _⟩ := Finset.mem_filter.1 hx
  obtain ⟨hyP, _⟩ := Finset.mem_filter.1 hy
  obtain ⟨hx1, hx2⟩ := Finset.mem_product.1 hxP
  obtain ⟨hy1, hy2⟩ := Finset.mem_product.1 hyP
  have h1 : PB n x.1 = PB n y.1 := congrArg Prod.fst h
  have h2 : PB n x.2 = PB n y.2 := congrArg Prod.snd h
  obtain ⟨ha, hb, he⟩ := PBlk_inj (PLeg_leg hx1) (PLeg_leg hy1) h1
  obtain ⟨hc, hq2, hf⟩ := PBlk_inj (PLeg_leg hx2) (PLeg_leg hy2) h2
  rw [show x = ((x.1.1, x.1.2.1, x.1.2.2), (x.2.1, x.2.2.1, x.2.2.2)) from rfl,
    show y = ((y.1.1, y.1.2.1, y.1.2.2), (y.2.1, y.2.2.1, y.2.2.2)) from rfl,
    ha, hb, he, hc, hq2, hf]
