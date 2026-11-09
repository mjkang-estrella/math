import CMDRRCycles
import CMDRRSwap

namespace CMDRR.Source
variable {M W O : Type} [Fintype O]
variable {s : Matching M W} {d : Schedule M W O} (h : Source s d)

include h

/-- With only two singles, the source existential repeated opponent is
forced to be the other single. This pays the multiplicity, not just its bound. -/
theorem unique_other_woman_count {u v : W} (hu : s.SingleWoman u)
    (honly : ∀ w, s.SingleWoman w → w = u ∨ w = v) :
    count (fun o => (d.game o).Women u v) = 2 ∧
    ∀ w, w ≠ u → w ≠ v → count (fun o => (d.game o).Women u w) = 1 := by
  obtain ⟨t,htu,hts,htc,ht⟩ := h.2.2.2.2.2 u hu
  have he : t = v := (honly t hts).resolve_left htu
  subst t
  exact ⟨htc,ht⟩

theorem unique_other_man_count {u v : M} (hu : s.SingleMan u)
    (honly : ∀ m, s.SingleMan m → m = u ∨ m = v) :
    count (fun o => (d.game o).Men u v) = 2 ∧
    ∀ m, m ≠ u → m ≠ v → count (fun o => (d.game o).Men u m) = 1 := by
  obtain ⟨t,htu,hts,htc,ht⟩ := h.2.2.2.2.1 u hu
  have he : t = v := (honly t hts).resolve_left htu
  subst t
  exact ⟨htc,ht⟩
end CMDRR.Source
