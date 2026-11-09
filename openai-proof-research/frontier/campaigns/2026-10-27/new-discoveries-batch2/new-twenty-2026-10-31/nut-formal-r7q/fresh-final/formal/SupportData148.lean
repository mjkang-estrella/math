import SignedCatalogue
import NewCertificates0214
import NewCertificates0215
import NewCertificates0216
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport148
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 6, 4, 7, 1, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0214.C6852, NewCertificates0214.C6853, NewCertificates0214.C6854, NewCertificates0214.C6855, NewCertificates0214.C6856, NewCertificates0214.C6857, NewCertificates0214.C6858, NewCertificates0214.C6859, NewCertificates0214.C6860, NewCertificates0214.C6861, NewCertificates0214.C6862, NewCertificates0214.C6863, NewCertificates0214.C6864, NewCertificates0214.C6865, NewCertificates0214.C6866, NewCertificates0214.C6867, NewCertificates0214.C6868, NewCertificates0214.C6869, NewCertificates0214.C6870, NewCertificates0214.C6871, NewCertificates0214.C6872, NewCertificates0214.C6873, NewCertificates0214.C6874, NewCertificates0214.C6875, NewCertificates0214.C6876, NewCertificates0214.C6877, NewCertificates0214.C6878, NewCertificates0214.C6879, NewCertificates0215.C6880, NewCertificates0215.C6881, NewCertificates0215.C6882, NewCertificates0215.C6883, NewCertificates0215.C6884, NewCertificates0215.C6885, NewCertificates0215.C6886, NewCertificates0215.C6887, NewCertificates0215.C6888, NewCertificates0215.C6889, NewCertificates0215.C6890, NewCertificates0215.C6891, NewCertificates0215.C6892, NewCertificates0215.C6893, NewCertificates0215.C6894, NewCertificates0215.C6895, NewCertificates0215.C6896, NewCertificates0215.C6897, NewCertificates0215.C6898, NewCertificates0215.C6899, NewCertificates0215.C6900, NewCertificates0215.C6901, NewCertificates0215.C6902, NewCertificates0215.C6903, NewCertificates0215.C6904, NewCertificates0215.C6905, NewCertificates0215.C6906, NewCertificates0215.C6907, NewCertificates0215.C6908, NewCertificates0215.C6909, NewCertificates0215.C6910, NewCertificates0215.C6911, NewCertificates0216.C6912, NewCertificates0216.C6913, NewCertificates0216.C6914, NewCertificates0216.C6915, NewCertificates0216.C6916, NewCertificates0216.C6917, NewCertificates0216.C6918, NewCertificates0216.C6919, NewCertificates0216.C6920, NewCertificates0216.C6921, NewCertificates0216.C6922, NewCertificates0216.C6923}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U6 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def U7 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
def D4 : Finset (Fin 8 × Fin 8) := {(0,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(0,5), (2,3)}
def D6 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4)}
def D7 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 5525988496730755104).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5525988496730755104 D i ∧ offSum 5525988496730755104 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7} := by
  decide +kernel
theorem augmentation0 : augmentation 5525988496730755104 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5525988496730755104 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5525988496730755104 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5525988496730755104 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 5525988496730755104 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 5525988496730755104 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 5525988496730755104 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 5525988496730755104 D7 = U7 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5525988496730755104 = {U0, U1, U2, U3, U4, U5, U6, U7} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5525988496730755104 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport148
