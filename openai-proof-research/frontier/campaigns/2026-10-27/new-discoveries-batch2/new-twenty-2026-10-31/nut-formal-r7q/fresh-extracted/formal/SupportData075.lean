import SignedCatalogue
import NewCertificates0111
import NewCertificates0112
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport075
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 6, 5, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0111.C3574, NewCertificates0111.C3575, NewCertificates0111.C3576, NewCertificates0111.C3577, NewCertificates0111.C3578, NewCertificates0111.C3579, NewCertificates0111.C3580, NewCertificates0111.C3581, NewCertificates0111.C3582, NewCertificates0111.C3583, NewCertificates0112.C3584, NewCertificates0112.C3585, NewCertificates0112.C3586, NewCertificates0112.C3587, NewCertificates0112.C3588, NewCertificates0112.C3589, NewCertificates0112.C3590, NewCertificates0112.C3591, NewCertificates0112.C3592, NewCertificates0112.C3593, NewCertificates0112.C3594, NewCertificates0112.C3595, NewCertificates0112.C3596, NewCertificates0112.C3597, NewCertificates0112.C3598, NewCertificates0112.C3599, NewCertificates0112.C3600, NewCertificates0112.C3601, NewCertificates0112.C3602, NewCertificates0112.C3603, NewCertificates0112.C3604, NewCertificates0112.C3605}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1805405414928441472).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1805405414928441472 D i ∧ offSum 1805405414928441472 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1805405414928441472 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1805405414928441472 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1805405414928441472 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport075
