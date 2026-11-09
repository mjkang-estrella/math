import SignedCatalogue
import NewCertificates0220
import NewCertificates0221
import NewCertificates0222
import NewCertificates0223
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport151
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 7, 1, 2, 6, 4, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 2, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0220.C7068, NewCertificates0220.C7069, NewCertificates0220.C7070, NewCertificates0220.C7071, NewCertificates0221.C7072, NewCertificates0221.C7073, NewCertificates0221.C7074, NewCertificates0221.C7075, NewCertificates0221.C7076, NewCertificates0221.C7077, NewCertificates0221.C7078, NewCertificates0221.C7079, NewCertificates0221.C7080, NewCertificates0221.C7081, NewCertificates0221.C7082, NewCertificates0221.C7083, NewCertificates0221.C7084, NewCertificates0221.C7085, NewCertificates0221.C7086, NewCertificates0221.C7087, NewCertificates0221.C7088, NewCertificates0221.C7089, NewCertificates0221.C7090, NewCertificates0221.C7091, NewCertificates0221.C7092, NewCertificates0221.C7093, NewCertificates0221.C7094, NewCertificates0221.C7095, NewCertificates0221.C7096, NewCertificates0221.C7097, NewCertificates0221.C7098, NewCertificates0221.C7099, NewCertificates0221.C7100, NewCertificates0221.C7101, NewCertificates0221.C7102, NewCertificates0221.C7103, NewCertificates0222.C7104, NewCertificates0222.C7105, NewCertificates0222.C7106, NewCertificates0222.C7107, NewCertificates0222.C7108, NewCertificates0222.C7109, NewCertificates0222.C7110, NewCertificates0222.C7111, NewCertificates0222.C7112, NewCertificates0222.C7113, NewCertificates0222.C7114, NewCertificates0222.C7115, NewCertificates0222.C7116, NewCertificates0222.C7117, NewCertificates0222.C7118, NewCertificates0222.C7119, NewCertificates0222.C7120, NewCertificates0222.C7121, NewCertificates0222.C7122, NewCertificates0222.C7123, NewCertificates0222.C7124, NewCertificates0222.C7125, NewCertificates0222.C7126, NewCertificates0222.C7127, NewCertificates0222.C7128, NewCertificates0222.C7129, NewCertificates0222.C7130, NewCertificates0222.C7131, NewCertificates0222.C7132, NewCertificates0222.C7133, NewCertificates0222.C7134, NewCertificates0222.C7135, NewCertificates0223.C7136, NewCertificates0223.C7137, NewCertificates0223.C7138, NewCertificates0223.C7139}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U6 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U7 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U8 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(1,5), (2,4)}
def D6 : Finset (Fin 8 × Fin 8) := {(0,5)}
def D7 : Finset (Fin 8 × Fin 8) := {(0,5), (3,4)}
def D8 : Finset (Fin 8 × Fin 8) := {(0,5), (2,4)}
theorem doubled_enumeration : ((supportEdges 5010820886829228192).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5010820886829228192 D i ∧ offSum 5010820886829228192 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8} := by
  decide +kernel
theorem augmentation0 : augmentation 5010820886829228192 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5010820886829228192 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5010820886829228192 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5010820886829228192 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 5010820886829228192 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 5010820886829228192 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 5010820886829228192 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 5010820886829228192 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 5010820886829228192 D8 = U8 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5010820886829228192 = {U0, U1, U2, U3, U4, U5, U6, U7, U8} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5010820886829228192 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport151
