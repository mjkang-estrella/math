import SignedCatalogue
import NewCertificates0282
import NewCertificates0283
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport191
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 1, 7, 6, 2, 3, 4, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0282.C9028, NewCertificates0282.C9029, NewCertificates0282.C9030, NewCertificates0282.C9031, NewCertificates0282.C9032, NewCertificates0282.C9033, NewCertificates0282.C9034, NewCertificates0282.C9035, NewCertificates0282.C9036, NewCertificates0282.C9037, NewCertificates0282.C9038, NewCertificates0282.C9039, NewCertificates0282.C9040, NewCertificates0282.C9041, NewCertificates0282.C9042, NewCertificates0282.C9043, NewCertificates0282.C9044, NewCertificates0282.C9045, NewCertificates0282.C9046, NewCertificates0282.C9047, NewCertificates0282.C9048, NewCertificates0282.C9049, NewCertificates0282.C9050, NewCertificates0282.C9051, NewCertificates0282.C9052, NewCertificates0282.C9053, NewCertificates0282.C9054, NewCertificates0282.C9055, NewCertificates0283.C9056, NewCertificates0283.C9057, NewCertificates0283.C9058, NewCertificates0283.C9059, NewCertificates0283.C9060, NewCertificates0283.C9061, NewCertificates0283.C9062, NewCertificates0283.C9063, NewCertificates0283.C9064, NewCertificates0283.C9065, NewCertificates0283.C9066, NewCertificates0283.C9067, NewCertificates0283.C9068, NewCertificates0283.C9069, NewCertificates0283.C9070, NewCertificates0283.C9071, NewCertificates0283.C9072, NewCertificates0283.C9073, NewCertificates0283.C9074, NewCertificates0283.C9075}
def U0 : QuotientMatrix := !![1, 1, 0, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,1)}
theorem doubled_enumeration : ((supportEdges 950906363594162562).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 950906363594162562 D i ∧ offSum 950906363594162562 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 950906363594162562 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 950906363594162562 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 950906363594162562 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 950906363594162562 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport191
