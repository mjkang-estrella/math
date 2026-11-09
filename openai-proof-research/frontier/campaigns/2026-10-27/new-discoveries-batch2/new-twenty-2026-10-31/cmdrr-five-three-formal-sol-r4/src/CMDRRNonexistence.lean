import CMDRRSigns
import CMDRRNormalizationBridge

namespace CMDRR
/-- No canonical CMDRR(5,3) schedule, with unrestricted finite occurrences. -/
theorem canonical_noSource {O : Type} [Fintype O]
    (d : Schedule (Fin 5) (Fin 5) O) : ¬ Source canonical d :=
  fun h => h.canonical_sign_contradiction

/-- Source Definition 1.2: arbitrary five-element player types, arbitrary
three-pair spouse matching, and any finite occurrence schedule. -/
theorem noSource_five_three {M W O : Type}
    [Fintype M] [Fintype W] [Fintype O]
    (s : Matching M W) (d : Schedule M W O)
    (hm : Fintype.card M = 5) (hw : Fintype.card W = 5)
    (hs : count (fun p : M × W => s.spouse p.1 p.2) = 3) :
    ¬ Source s d := by
  intro h
  obtain ⟨e,f,_,hc⟩ := h.canonical_transport hm hw hs
  exact canonical_noSource (d.relabel e f) hc

/-- Literal universal nonexistence endpoint; k counts spouse pairs, not rounds. -/
theorem universalExistsFiveThree_negation (M W : Type)
    [Fintype M] [Fintype W] : ¬ ExistsFiveThree M W := by
  rintro ⟨hm,hw,s,hs,O,inst,d,h⟩
  exact noSource_five_three s d hm hw hs h

#print axioms canonical_noSource
#print axioms noSource_five_three
#print axioms universalExistsFiveThree_negation
end CMDRR
