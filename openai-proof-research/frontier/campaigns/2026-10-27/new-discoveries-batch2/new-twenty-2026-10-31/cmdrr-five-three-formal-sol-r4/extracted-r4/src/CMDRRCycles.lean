import CMDRRRepeat
import CMDRRCounts

namespace CMDRR.Source
variable {M W O : Type} [Fintype O]
variable {s : Matching M W} {d : Schedule M W O} (h : Source s d)

/-- Two distinct two-cycles in one actual row cannot coexist when the
single women are exactly u and v. The repeated-pair restriction is derived
from source occurrence counts, rather than supplied as a permutation axiom. -/
theorem row_twoCycles_overlap {u v : W}
    (hs : ∀ w, s.SingleWoman w → w = u ∨ w = v)
    (x y a b : Cell s) (hxy : x ≠ y) (hab : a ≠ b)
    (hx : h.U x = y) (hy : h.U y = x)
    (ha : h.U a = b) (hb : h.U b = a)
    (hm : a.1.1 = x.1.1) : a = x ∨ a = y := by
  have h1 := h.row_twoCycle_single x y hxy hx hy
  have h2 := h.row_twoCycle_single a b hab ha hb
  have hne : x.1.2 ≠ y.1.2 := by
    intro he
    apply hxy
    apply Subtype.ext
    apply Prod.ext
    · have hh := h.U_first x
      rw [hx] at hh
      exact hh.symm
    · exact he
  have hw : a.1.2 = x.1.2 ∨ a.1.2 = y.1.2 := by
    rcases hs _ h1.1 with hu | hv <;>
      rcases hs _ h1.2 with hu' | hv' <;>
      rcases hs _ h2.1 with hu'' | hv'' <;> simp_all
  rcases hw with hw | hw
  · exact Or.inl (Subtype.ext (Prod.ext hm hw))
  · apply Or.inr
    apply Subtype.ext
    apply Prod.ext
    · have hh := h.U_first x
      rw [hx] at hh
      exact hm.trans hh.symm
    · exact hw

end CMDRR.Source
