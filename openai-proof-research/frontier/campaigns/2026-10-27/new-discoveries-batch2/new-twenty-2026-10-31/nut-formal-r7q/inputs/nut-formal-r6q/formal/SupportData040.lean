import SignedCatalogue
import NewCertificates0062
import NewCertificates0063
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport040
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 5, 6, 4, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0062.C1994, NewCertificates0062.C1995, NewCertificates0062.C1996, NewCertificates0062.C1997, NewCertificates0062.C1998, NewCertificates0062.C1999, NewCertificates0062.C2000, NewCertificates0062.C2001, NewCertificates0062.C2002, NewCertificates0062.C2003, NewCertificates0062.C2004, NewCertificates0062.C2005, NewCertificates0062.C2006, NewCertificates0062.C2007, NewCertificates0062.C2008, NewCertificates0062.C2009, NewCertificates0062.C2010, NewCertificates0062.C2011, NewCertificates0062.C2012, NewCertificates0062.C2013, NewCertificates0062.C2014, NewCertificates0062.C2015, NewCertificates0063.C2016, NewCertificates0063.C2017, NewCertificates0063.C2018, NewCertificates0063.C2019, NewCertificates0063.C2020, NewCertificates0063.C2021, NewCertificates0063.C2022, NewCertificates0063.C2023, NewCertificates0063.C2024, NewCertificates0063.C2025, NewCertificates0063.C2026, NewCertificates0063.C2027, NewCertificates0063.C2028, NewCertificates0063.C2029, NewCertificates0063.C2030, NewCertificates0063.C2031, NewCertificates0063.C2032, NewCertificates0063.C2033, NewCertificates0063.C2034, NewCertificates0063.C2035, NewCertificates0063.C2036, NewCertificates0063.C2037, NewCertificates0063.C2038, NewCertificates0063.C2039, NewCertificates0063.C2040, NewCertificates0063.C2041}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,4)}
theorem doubled_enumeration : ((supportEdges 2966412160836583552).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2966412160836583552 D i ∧ offSum 2966412160836583552 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2966412160836583552 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2966412160836583552 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2966412160836583552 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2966412160836583552 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport040
