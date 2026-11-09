import SignedCatalogue
import NewCertificates0212
import NewCertificates0213
import NewCertificates0214
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport147
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 3, 7, 2, 6, 4, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 3, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0212.C6792, NewCertificates0212.C6793, NewCertificates0212.C6794, NewCertificates0212.C6795, NewCertificates0212.C6796, NewCertificates0212.C6797, NewCertificates0212.C6798, NewCertificates0212.C6799, NewCertificates0212.C6800, NewCertificates0212.C6801, NewCertificates0212.C6802, NewCertificates0212.C6803, NewCertificates0212.C6804, NewCertificates0212.C6805, NewCertificates0212.C6806, NewCertificates0212.C6807, NewCertificates0212.C6808, NewCertificates0212.C6809, NewCertificates0212.C6810, NewCertificates0212.C6811, NewCertificates0212.C6812, NewCertificates0212.C6813, NewCertificates0212.C6814, NewCertificates0212.C6815, NewCertificates0213.C6816, NewCertificates0213.C6817, NewCertificates0213.C6818, NewCertificates0213.C6819, NewCertificates0213.C6820, NewCertificates0213.C6821, NewCertificates0213.C6822, NewCertificates0213.C6823, NewCertificates0213.C6824, NewCertificates0213.C6825, NewCertificates0213.C6826, NewCertificates0213.C6827, NewCertificates0213.C6828, NewCertificates0213.C6829, NewCertificates0213.C6830, NewCertificates0213.C6831, NewCertificates0213.C6832, NewCertificates0213.C6833, NewCertificates0213.C6834, NewCertificates0213.C6835, NewCertificates0213.C6836, NewCertificates0213.C6837, NewCertificates0213.C6838, NewCertificates0213.C6839, NewCertificates0213.C6840, NewCertificates0213.C6841, NewCertificates0213.C6842, NewCertificates0213.C6843, NewCertificates0213.C6844, NewCertificates0213.C6845, NewCertificates0213.C6846, NewCertificates0213.C6847, NewCertificates0214.C6848, NewCertificates0214.C6849, NewCertificates0214.C6850, NewCertificates0214.C6851}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 1, 0, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 2, 0, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 2, 0, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (3,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(0,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4)}
theorem doubled_enumeration : ((supportEdges 5518045625205133344).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5518045625205133344 D i ∧ offSum 5518045625205133344 D i ≤ 3) = {D0, D1, D2, D3, D4, D5} := by
  decide +kernel
theorem augmentation0 : augmentation 5518045625205133344 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5518045625205133344 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5518045625205133344 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5518045625205133344 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 5518045625205133344 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 5518045625205133344 D5 = U5 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5518045625205133344 = {U0, U1, U2, U3, U4, U5} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5518045625205133344 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport147
