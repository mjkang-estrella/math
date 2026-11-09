import SignedCatalogue
import NewCertificates0235
import NewCertificates0236
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport160
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 6, 3, 4, 2, 7, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0235.C7540, NewCertificates0235.C7541, NewCertificates0235.C7542, NewCertificates0235.C7543, NewCertificates0235.C7544, NewCertificates0235.C7545, NewCertificates0235.C7546, NewCertificates0235.C7547, NewCertificates0235.C7548, NewCertificates0235.C7549, NewCertificates0235.C7550, NewCertificates0235.C7551, NewCertificates0236.C7552, NewCertificates0236.C7553, NewCertificates0236.C7554, NewCertificates0236.C7555, NewCertificates0236.C7556, NewCertificates0236.C7557, NewCertificates0236.C7558, NewCertificates0236.C7559, NewCertificates0236.C7560, NewCertificates0236.C7561, NewCertificates0236.C7562, NewCertificates0236.C7563, NewCertificates0236.C7564, NewCertificates0236.C7565, NewCertificates0236.C7566, NewCertificates0236.C7567, NewCertificates0236.C7568, NewCertificates0236.C7569, NewCertificates0236.C7570, NewCertificates0236.C7571}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1014745202504011872).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1014745202504011872 D i ∧ offSum 1014745202504011872 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1014745202504011872 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1014745202504011872 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1014745202504011872 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport160
