import SignedCatalogue
import NewCertificates0196
import NewCertificates0197
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport133
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 3, 1, 5, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0196.C6292, NewCertificates0196.C6293, NewCertificates0196.C6294, NewCertificates0196.C6295, NewCertificates0196.C6296, NewCertificates0196.C6297, NewCertificates0196.C6298, NewCertificates0196.C6299, NewCertificates0196.C6300, NewCertificates0196.C6301, NewCertificates0196.C6302, NewCertificates0196.C6303, NewCertificates0197.C6304, NewCertificates0197.C6305, NewCertificates0197.C6306, NewCertificates0197.C6307, NewCertificates0197.C6308, NewCertificates0197.C6309, NewCertificates0197.C6310, NewCertificates0197.C6311, NewCertificates0197.C6312, NewCertificates0197.C6313, NewCertificates0197.C6314, NewCertificates0197.C6315, NewCertificates0197.C6316, NewCertificates0197.C6317, NewCertificates0197.C6318, NewCertificates0197.C6319, NewCertificates0197.C6320, NewCertificates0197.C6321, NewCertificates0197.C6322, NewCertificates0197.C6323}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 2525835685116027072).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2525835685116027072 D i ∧ offSum 2525835685116027072 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 2525835685116027072 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2525835685116027072 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2525835685116027072 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport133
