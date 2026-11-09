import SignedCatalogue
import NewCertificates0239
import NewCertificates0240
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport163
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 6, 7, 2, 3, 1, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 1, 2, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0239.C7652, NewCertificates0239.C7653, NewCertificates0239.C7654, NewCertificates0239.C7655, NewCertificates0239.C7656, NewCertificates0239.C7657, NewCertificates0239.C7658, NewCertificates0239.C7659, NewCertificates0239.C7660, NewCertificates0239.C7661, NewCertificates0239.C7662, NewCertificates0239.C7663, NewCertificates0239.C7664, NewCertificates0239.C7665, NewCertificates0239.C7666, NewCertificates0239.C7667, NewCertificates0239.C7668, NewCertificates0239.C7669, NewCertificates0239.C7670, NewCertificates0239.C7671, NewCertificates0239.C7672, NewCertificates0239.C7673, NewCertificates0239.C7674, NewCertificates0239.C7675, NewCertificates0239.C7676, NewCertificates0239.C7677, NewCertificates0239.C7678, NewCertificates0239.C7679, NewCertificates0240.C7680, NewCertificates0240.C7681, NewCertificates0240.C7682, NewCertificates0240.C7683}
def U0 : QuotientMatrix := !![0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 507513738680652000).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 507513738680652000 D i ∧ offSum 507513738680652000 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 507513738680652000 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 507513738680652000 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 507513738680652000 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport163
