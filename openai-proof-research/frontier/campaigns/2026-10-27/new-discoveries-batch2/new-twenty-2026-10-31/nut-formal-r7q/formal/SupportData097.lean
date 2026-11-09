import SignedCatalogue
import NewCertificates0140
import NewCertificates0141
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport097
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 4, 5, 6, 2, 3, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0140.C4494, NewCertificates0140.C4495, NewCertificates0140.C4496, NewCertificates0140.C4497, NewCertificates0140.C4498, NewCertificates0140.C4499, NewCertificates0140.C4500, NewCertificates0140.C4501, NewCertificates0140.C4502, NewCertificates0140.C4503, NewCertificates0140.C4504, NewCertificates0140.C4505, NewCertificates0140.C4506, NewCertificates0140.C4507, NewCertificates0140.C4508, NewCertificates0140.C4509, NewCertificates0140.C4510, NewCertificates0140.C4511, NewCertificates0141.C4512, NewCertificates0141.C4513, NewCertificates0141.C4514, NewCertificates0141.C4515, NewCertificates0141.C4516, NewCertificates0141.C4517, NewCertificates0141.C4518, NewCertificates0141.C4519, NewCertificates0141.C4520, NewCertificates0141.C4521, NewCertificates0141.C4522, NewCertificates0141.C4523, NewCertificates0141.C4524, NewCertificates0141.C4525, NewCertificates0141.C4526, NewCertificates0141.C4527, NewCertificates0141.C4528, NewCertificates0141.C4529, NewCertificates0141.C4530, NewCertificates0141.C4531, NewCertificates0141.C4532, NewCertificates0141.C4533, NewCertificates0141.C4534, NewCertificates0141.C4535, NewCertificates0141.C4536, NewCertificates0141.C4537, NewCertificates0141.C4538, NewCertificates0141.C4539, NewCertificates0141.C4540, NewCertificates0141.C4541}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,3)}
theorem doubled_enumeration : ((supportEdges 3538867098113542272).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3538867098113542272 D i ∧ offSum 3538867098113542272 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 3538867098113542272 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 3538867098113542272 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3538867098113542272 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3538867098113542272 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport097
