import SignedCatalogue
import NewCertificates0017
import NewCertificates0018
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport012
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 6, 4, 5, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0017.C560, NewCertificates0017.C561, NewCertificates0017.C562, NewCertificates0017.C563, NewCertificates0017.C564, NewCertificates0017.C565, NewCertificates0017.C566, NewCertificates0017.C567, NewCertificates0017.C568, NewCertificates0017.C569, NewCertificates0017.C570, NewCertificates0017.C571, NewCertificates0017.C572, NewCertificates0017.C573, NewCertificates0017.C574, NewCertificates0017.C575, NewCertificates0018.C576, NewCertificates0018.C577, NewCertificates0018.C578, NewCertificates0018.C579, NewCertificates0018.C580, NewCertificates0018.C581, NewCertificates0018.C582, NewCertificates0018.C583, NewCertificates0018.C584, NewCertificates0018.C585, NewCertificates0018.C586, NewCertificates0018.C587, NewCertificates0018.C588, NewCertificates0018.C589, NewCertificates0018.C590, NewCertificates0018.C591}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 519137061572214912).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 519137061572214912 D i ∧ offSum 519137061572214912 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 519137061572214912 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 519137061572214912 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 519137061572214912 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport012
