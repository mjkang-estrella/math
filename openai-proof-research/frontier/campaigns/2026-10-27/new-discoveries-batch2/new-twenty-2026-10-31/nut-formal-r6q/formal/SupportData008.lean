import SignedCatalogue
import NewCertificates0012
import NewCertificates0013
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport008
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 5, 4, 6, 3, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0012.C384, NewCertificates0012.C385, NewCertificates0012.C386, NewCertificates0012.C387, NewCertificates0012.C388, NewCertificates0012.C389, NewCertificates0012.C390, NewCertificates0012.C391, NewCertificates0012.C392, NewCertificates0012.C393, NewCertificates0012.C394, NewCertificates0012.C395, NewCertificates0012.C396, NewCertificates0012.C397, NewCertificates0012.C398, NewCertificates0012.C399, NewCertificates0012.C400, NewCertificates0012.C401, NewCertificates0012.C402, NewCertificates0012.C403, NewCertificates0012.C404, NewCertificates0012.C405, NewCertificates0012.C406, NewCertificates0012.C407, NewCertificates0012.C408, NewCertificates0012.C409, NewCertificates0012.C410, NewCertificates0012.C411, NewCertificates0012.C412, NewCertificates0012.C413, NewCertificates0012.C414, NewCertificates0012.C415, NewCertificates0013.C416, NewCertificates0013.C417, NewCertificates0013.C418, NewCertificates0013.C419, NewCertificates0013.C420, NewCertificates0013.C421, NewCertificates0013.C422, NewCertificates0013.C423, NewCertificates0013.C424, NewCertificates0013.C425, NewCertificates0013.C426, NewCertificates0013.C427, NewCertificates0013.C428, NewCertificates0013.C429, NewCertificates0013.C430, NewCertificates0013.C431}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 2534629561866420352).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2534629561866420352 D i ∧ offSum 2534629561866420352 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2534629561866420352 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2534629561866420352 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2534629561866420352 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2534629561866420352 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport008
