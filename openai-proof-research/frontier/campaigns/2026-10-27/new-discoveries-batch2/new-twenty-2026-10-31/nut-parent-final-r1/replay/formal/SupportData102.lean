import SignedCatalogue
import NewCertificates0148
import NewCertificates0149
import NewCertificates0150
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport102
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 3, 2, 4, 5, 6] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0148.C4758, NewCertificates0148.C4759, NewCertificates0148.C4760, NewCertificates0148.C4761, NewCertificates0148.C4762, NewCertificates0148.C4763, NewCertificates0148.C4764, NewCertificates0148.C4765, NewCertificates0148.C4766, NewCertificates0148.C4767, NewCertificates0149.C4768, NewCertificates0149.C4769, NewCertificates0149.C4770, NewCertificates0149.C4771, NewCertificates0149.C4772, NewCertificates0149.C4773, NewCertificates0149.C4774, NewCertificates0149.C4775, NewCertificates0149.C4776, NewCertificates0149.C4777, NewCertificates0149.C4778, NewCertificates0149.C4779, NewCertificates0149.C4780, NewCertificates0149.C4781, NewCertificates0149.C4782, NewCertificates0149.C4783, NewCertificates0149.C4784, NewCertificates0149.C4785, NewCertificates0149.C4786, NewCertificates0149.C4787, NewCertificates0149.C4788, NewCertificates0149.C4789, NewCertificates0149.C4790, NewCertificates0149.C4791, NewCertificates0149.C4792, NewCertificates0149.C4793, NewCertificates0149.C4794, NewCertificates0149.C4795, NewCertificates0149.C4796, NewCertificates0149.C4797, NewCertificates0149.C4798, NewCertificates0149.C4799, NewCertificates0150.C4800, NewCertificates0150.C4801, NewCertificates0150.C4802, NewCertificates0150.C4803, NewCertificates0150.C4804, NewCertificates0150.C4805}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
theorem doubled_enumeration : ((supportEdges 807367439863153792).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 807367439863153792 D i ∧ offSum 807367439863153792 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 807367439863153792 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 807367439863153792 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 807367439863153792 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 807367439863153792 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport102
