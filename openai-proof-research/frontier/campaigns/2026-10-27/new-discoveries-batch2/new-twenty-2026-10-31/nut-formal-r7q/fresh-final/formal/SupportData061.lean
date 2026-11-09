import SignedCatalogue
import NewCertificates0089
import NewCertificates0090
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport061
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 5, 6, 3, 2, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0089.C2862, NewCertificates0089.C2863, NewCertificates0089.C2864, NewCertificates0089.C2865, NewCertificates0089.C2866, NewCertificates0089.C2867, NewCertificates0089.C2868, NewCertificates0089.C2869, NewCertificates0089.C2870, NewCertificates0089.C2871, NewCertificates0089.C2872, NewCertificates0089.C2873, NewCertificates0089.C2874, NewCertificates0089.C2875, NewCertificates0089.C2876, NewCertificates0089.C2877, NewCertificates0089.C2878, NewCertificates0089.C2879, NewCertificates0090.C2880, NewCertificates0090.C2881, NewCertificates0090.C2882, NewCertificates0090.C2883, NewCertificates0090.C2884, NewCertificates0090.C2885, NewCertificates0090.C2886, NewCertificates0090.C2887, NewCertificates0090.C2888, NewCertificates0090.C2889, NewCertificates0090.C2890, NewCertificates0090.C2891, NewCertificates0090.C2892, NewCertificates0090.C2893, NewCertificates0090.C2894, NewCertificates0090.C2895, NewCertificates0090.C2896, NewCertificates0090.C2897, NewCertificates0090.C2898, NewCertificates0090.C2899, NewCertificates0090.C2900, NewCertificates0090.C2901, NewCertificates0090.C2902, NewCertificates0090.C2903, NewCertificates0090.C2904, NewCertificates0090.C2905, NewCertificates0090.C2906, NewCertificates0090.C2907, NewCertificates0090.C2908, NewCertificates0090.C2909}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 1, 0, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 1, 0, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 1, 0, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 2532931795118243968).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2532931795118243968 D i ∧ offSum 2532931795118243968 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 2532931795118243968 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2532931795118243968 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2532931795118243968 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2532931795118243968 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2532931795118243968 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport061
