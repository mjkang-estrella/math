import SignedCatalogue
import NewCertificates0247
import NewCertificates0248
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport171
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 5, 6, 7, 1, 3, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0247.C7908, NewCertificates0247.C7909, NewCertificates0247.C7910, NewCertificates0247.C7911, NewCertificates0247.C7912, NewCertificates0247.C7913, NewCertificates0247.C7914, NewCertificates0247.C7915, NewCertificates0247.C7916, NewCertificates0247.C7917, NewCertificates0247.C7918, NewCertificates0247.C7919, NewCertificates0247.C7920, NewCertificates0247.C7921, NewCertificates0247.C7922, NewCertificates0247.C7923, NewCertificates0247.C7924, NewCertificates0247.C7925, NewCertificates0247.C7926, NewCertificates0247.C7927, NewCertificates0247.C7928, NewCertificates0247.C7929, NewCertificates0247.C7930, NewCertificates0247.C7931, NewCertificates0247.C7932, NewCertificates0247.C7933, NewCertificates0247.C7934, NewCertificates0247.C7935, NewCertificates0248.C7936, NewCertificates0248.C7937, NewCertificates0248.C7938, NewCertificates0248.C7939, NewCertificates0248.C7940, NewCertificates0248.C7941, NewCertificates0248.C7942, NewCertificates0248.C7943, NewCertificates0248.C7944, NewCertificates0248.C7945, NewCertificates0248.C7946, NewCertificates0248.C7947, NewCertificates0248.C7948, NewCertificates0248.C7949, NewCertificates0248.C7950, NewCertificates0248.C7951, NewCertificates0248.C7952, NewCertificates0248.C7953, NewCertificates0248.C7954, NewCertificates0248.C7955}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 2750239363765420048).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2750239363765420048 D i ∧ offSum 2750239363765420048 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 2750239363765420048 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2750239363765420048 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2750239363765420048 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 2750239363765420048 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2750239363765420048 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2750239363765420048 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport171
