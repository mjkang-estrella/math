import SignedCatalogue
import NewCertificates0245
import NewCertificates0246
import NewCertificates0247
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport170
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 3, 6, 1, 5, 7, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0245.C7868, NewCertificates0245.C7869, NewCertificates0245.C7870, NewCertificates0245.C7871, NewCertificates0246.C7872, NewCertificates0246.C7873, NewCertificates0246.C7874, NewCertificates0246.C7875, NewCertificates0246.C7876, NewCertificates0246.C7877, NewCertificates0246.C7878, NewCertificates0246.C7879, NewCertificates0246.C7880, NewCertificates0246.C7881, NewCertificates0246.C7882, NewCertificates0246.C7883, NewCertificates0246.C7884, NewCertificates0246.C7885, NewCertificates0246.C7886, NewCertificates0246.C7887, NewCertificates0246.C7888, NewCertificates0246.C7889, NewCertificates0246.C7890, NewCertificates0246.C7891, NewCertificates0246.C7892, NewCertificates0246.C7893, NewCertificates0246.C7894, NewCertificates0246.C7895, NewCertificates0246.C7896, NewCertificates0246.C7897, NewCertificates0246.C7898, NewCertificates0246.C7899, NewCertificates0246.C7900, NewCertificates0246.C7901, NewCertificates0246.C7902, NewCertificates0246.C7903, NewCertificates0247.C7904, NewCertificates0247.C7905, NewCertificates0247.C7906, NewCertificates0247.C7907}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 1, 0, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 2, 0, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,4)}
theorem doubled_enumeration : ((supportEdges 2750226066749571088).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2750226066749571088 D i ∧ offSum 2750226066749571088 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 2750226066749571088 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2750226066749571088 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2750226066749571088 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2750226066749571088 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2750226066749571088 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport170
