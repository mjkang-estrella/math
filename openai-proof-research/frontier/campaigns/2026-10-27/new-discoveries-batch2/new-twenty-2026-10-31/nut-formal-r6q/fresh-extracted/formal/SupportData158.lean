import SignedCatalogue
import NewCertificates0233
import NewCertificates0234
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport158
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 7, 4, 6, 2, 1, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0233.C7476, NewCertificates0233.C7477, NewCertificates0233.C7478, NewCertificates0233.C7479, NewCertificates0233.C7480, NewCertificates0233.C7481, NewCertificates0233.C7482, NewCertificates0233.C7483, NewCertificates0233.C7484, NewCertificates0233.C7485, NewCertificates0233.C7486, NewCertificates0233.C7487, NewCertificates0234.C7488, NewCertificates0234.C7489, NewCertificates0234.C7490, NewCertificates0234.C7491, NewCertificates0234.C7492, NewCertificates0234.C7493, NewCertificates0234.C7494, NewCertificates0234.C7495, NewCertificates0234.C7496, NewCertificates0234.C7497, NewCertificates0234.C7498, NewCertificates0234.C7499, NewCertificates0234.C7500, NewCertificates0234.C7501, NewCertificates0234.C7502, NewCertificates0234.C7503, NewCertificates0234.C7504, NewCertificates0234.C7505, NewCertificates0234.C7506, NewCertificates0234.C7507}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 1525121181194670240).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1525121181194670240 D i ∧ offSum 1525121181194670240 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1525121181194670240 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1525121181194670240 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1525121181194670240 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1525121181194670240 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport158
