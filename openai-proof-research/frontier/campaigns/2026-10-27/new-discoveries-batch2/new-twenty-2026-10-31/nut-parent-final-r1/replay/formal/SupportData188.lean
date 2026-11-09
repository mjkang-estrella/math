import SignedCatalogue
import NewCertificates0277
import NewCertificates0278
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport188
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 1, 7, 2, 5, 6, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 2, 3, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0277.C8876, NewCertificates0277.C8877, NewCertificates0277.C8878, NewCertificates0277.C8879, NewCertificates0277.C8880, NewCertificates0277.C8881, NewCertificates0277.C8882, NewCertificates0277.C8883, NewCertificates0277.C8884, NewCertificates0277.C8885, NewCertificates0277.C8886, NewCertificates0277.C8887, NewCertificates0277.C8888, NewCertificates0277.C8889, NewCertificates0277.C8890, NewCertificates0277.C8891, NewCertificates0277.C8892, NewCertificates0277.C8893, NewCertificates0277.C8894, NewCertificates0277.C8895, NewCertificates0278.C8896, NewCertificates0278.C8897, NewCertificates0278.C8898, NewCertificates0278.C8899, NewCertificates0278.C8900, NewCertificates0278.C8901, NewCertificates0278.C8902, NewCertificates0278.C8903, NewCertificates0278.C8904, NewCertificates0278.C8905, NewCertificates0278.C8906, NewCertificates0278.C8907, NewCertificates0278.C8908, NewCertificates0278.C8909, NewCertificates0278.C8910, NewCertificates0278.C8911, NewCertificates0278.C8912, NewCertificates0278.C8913, NewCertificates0278.C8914, NewCertificates0278.C8915, NewCertificates0278.C8916, NewCertificates0278.C8917, NewCertificates0278.C8918, NewCertificates0278.C8919, NewCertificates0278.C8920, NewCertificates0278.C8921, NewCertificates0278.C8922, NewCertificates0278.C8923}
def U0 : QuotientMatrix := !![1, 1, 0, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,1)}
theorem doubled_enumeration : ((supportEdges 512315692509331842).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 512315692509331842 D i ∧ offSum 512315692509331842 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 512315692509331842 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 512315692509331842 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 512315692509331842 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 512315692509331842 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport188
