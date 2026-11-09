import SignedCatalogue
import NewCertificates0013
import NewCertificates0014
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport009
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 6, 2, 5, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0013.C432, NewCertificates0013.C433, NewCertificates0013.C434, NewCertificates0013.C435, NewCertificates0013.C436, NewCertificates0013.C437, NewCertificates0013.C438, NewCertificates0013.C439, NewCertificates0013.C440, NewCertificates0013.C441, NewCertificates0013.C442, NewCertificates0013.C443, NewCertificates0013.C444, NewCertificates0013.C445, NewCertificates0013.C446, NewCertificates0013.C447, NewCertificates0014.C448, NewCertificates0014.C449, NewCertificates0014.C450, NewCertificates0014.C451, NewCertificates0014.C452, NewCertificates0014.C453, NewCertificates0014.C454, NewCertificates0014.C455, NewCertificates0014.C456, NewCertificates0014.C457, NewCertificates0014.C458, NewCertificates0014.C459, NewCertificates0014.C460, NewCertificates0014.C461, NewCertificates0014.C462, NewCertificates0014.C463, NewCertificates0014.C464, NewCertificates0014.C465, NewCertificates0014.C466, NewCertificates0014.C467, NewCertificates0014.C468, NewCertificates0014.C469, NewCertificates0014.C470, NewCertificates0014.C471, NewCertificates0014.C472, NewCertificates0014.C473, NewCertificates0014.C474, NewCertificates0014.C475, NewCertificates0014.C476, NewCertificates0014.C477, NewCertificates0014.C478, NewCertificates0014.C479}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 4874117626353188992).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 4874117626353188992 D i ∧ offSum 4874117626353188992 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 4874117626353188992 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 4874117626353188992 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 4874117626353188992 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 4874117626353188992 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport009
