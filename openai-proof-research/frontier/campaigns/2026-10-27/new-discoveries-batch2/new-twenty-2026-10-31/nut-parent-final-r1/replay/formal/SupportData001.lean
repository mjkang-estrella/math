import SignedCatalogue
import NewCertificates0001
import NewCertificates0002
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport001
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 4, 5, 6, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0001.C32, NewCertificates0001.C33, NewCertificates0001.C34, NewCertificates0001.C35, NewCertificates0001.C36, NewCertificates0001.C37, NewCertificates0001.C38, NewCertificates0001.C39, NewCertificates0001.C40, NewCertificates0001.C41, NewCertificates0001.C42, NewCertificates0001.C43, NewCertificates0001.C44, NewCertificates0001.C45, NewCertificates0001.C46, NewCertificates0001.C47, NewCertificates0001.C48, NewCertificates0001.C49, NewCertificates0001.C50, NewCertificates0001.C51, NewCertificates0001.C52, NewCertificates0001.C53, NewCertificates0001.C54, NewCertificates0001.C55, NewCertificates0001.C56, NewCertificates0001.C57, NewCertificates0001.C58, NewCertificates0001.C59, NewCertificates0001.C60, NewCertificates0001.C61, NewCertificates0001.C62, NewCertificates0001.C63, NewCertificates0002.C64, NewCertificates0002.C65, NewCertificates0002.C66, NewCertificates0002.C67, NewCertificates0002.C68, NewCertificates0002.C69, NewCertificates0002.C70, NewCertificates0002.C71, NewCertificates0002.C72, NewCertificates0002.C73, NewCertificates0002.C74, NewCertificates0002.C75, NewCertificates0002.C76, NewCertificates0002.C77, NewCertificates0002.C78, NewCertificates0002.C79}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(4,5)}
theorem doubled_enumeration : ((supportEdges 1381567834898858112).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1381567834898858112 D i ∧ offSum 1381567834898858112 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1381567834898858112 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1381567834898858112 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1381567834898858112 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1381567834898858112 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport001
