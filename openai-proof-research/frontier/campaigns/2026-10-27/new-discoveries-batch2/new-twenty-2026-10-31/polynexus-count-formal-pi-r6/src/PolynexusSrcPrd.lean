import PolynexusClose

/-!
# Source-level multiplication bridge (MathDB 352496)

The ordinary product of two legal source matrices, computed in the signed
one-based model, is exactly the ordinary product of the corresponding
coupled blocks: the dictionary is an equality of matrices, so no
multiplicity or value is lost.  Consequently every closure, zero and
nonzero statement for blocks transfers verbatim to source matrices.
-/

/-- Source products are block products, entrywise. -/
theorem PSrc_mul_eq_PBlk_mul {n : ℕ} {d d' : ℤ} {k m k' m' : ℕ}
    (h1 : PSrcLeg n d k m) (h2 : PSrcLeg n d' k' m') :
    PSrc n d k m * PSrc n d' k' m' =
      PBlk n (srcA k) (srcB d k) (srcE k m) *
        PBlk n (srcA k') (srcB d' k') (srcE k' m') := by
  rw [PSrc_eq_PBlk h1, PSrc_eq_PBlk h2]

/-- The product of two legal source matrices is the zero matrix exactly
in the two disjoint-interval cases `b+e < c` or `c+f < b` (block coords
`b = srcB d k`, `e = srcE k m`, `c = srcA k'`, `f = srcE k' m'`). -/
theorem PSrc_mul_eq_zero {n : ℕ} {d d' : ℤ} {k m k' m' : ℕ}
    (h1 : PSrcLeg n d k m) (h2 : PSrcLeg n d' k' m')
    (hd : srcB d k + srcE k m < srcA k' ∨ srcA k' + srcE k' m' < srcB d k) :
    PSrc n d k m * PSrc n d' k' m' = 0 := by
  rw [PSrc_mul_eq_PBlk_mul h1 h2]
  refine PBlk_mul_disjoint_zero n (srcA k) (srcB d k) (srcE k m) (srcA k')
    (srcB d' k') (srcE k' m')
    ⟨(srcDict_leg h1).1, (srcDict_leg h1).2, (srcDict_leg h2).1,
      (srcDict_leg h2).2⟩ ?_
  rcases hd with hh | hh
  · exact fun con => by have h2' := con.2; omega
  · exact fun con => by have h1' := con.1; omega

/-- The product of two legal source matrices is nonzero whenever the
coupled middle intervals overlap. -/
theorem PSrc_mul_ne_zero {n : ℕ} {d d' : ℤ} {k m k' m' : ℕ}
    (h1 : PSrcLeg n d k m) (h2 : PSrcLeg n d' k' m')
    (hov : srcB d k ≤ srcA k' + srcE k' m' ∧ srcA k' ≤ srcB d k + srcE k m) :
    PSrc n d k m * PSrc n d' k' m' ≠ 0 := by
  rw [PSrc_mul_eq_PBlk_mul h1 h2]
  exact PBlk_mul_nonzero n (srcA k) (srcB d k) (srcE k m) (srcA k')
    (srcB d' k') (srcE k' m')
    ⟨(srcDict_leg h1).1, (srcDict_leg h1).2, (srcDict_leg h2).1,
      (srcDict_leg h2).2⟩ hov
