import SignedCatalogue
import NewCertificates0201
import NewCertificates0202
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport138
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 5, 4, 3, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0201.C6452, NewCertificates0201.C6453, NewCertificates0201.C6454, NewCertificates0201.C6455, NewCertificates0201.C6456, NewCertificates0201.C6457, NewCertificates0201.C6458, NewCertificates0201.C6459, NewCertificates0201.C6460, NewCertificates0201.C6461, NewCertificates0201.C6462, NewCertificates0201.C6463, NewCertificates0202.C6464, NewCertificates0202.C6465, NewCertificates0202.C6466, NewCertificates0202.C6467, NewCertificates0202.C6468, NewCertificates0202.C6469, NewCertificates0202.C6470, NewCertificates0202.C6471, NewCertificates0202.C6472, NewCertificates0202.C6473, NewCertificates0202.C6474, NewCertificates0202.C6475, NewCertificates0202.C6476, NewCertificates0202.C6477, NewCertificates0202.C6478, NewCertificates0202.C6479, NewCertificates0202.C6480, NewCertificates0202.C6481, NewCertificates0202.C6482, NewCertificates0202.C6483}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 1, 0, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1523706006386258112).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1523706006386258112 D i ∧ offSum 1523706006386258112 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1523706006386258112 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1523706006386258112 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1523706006386258112 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport138
