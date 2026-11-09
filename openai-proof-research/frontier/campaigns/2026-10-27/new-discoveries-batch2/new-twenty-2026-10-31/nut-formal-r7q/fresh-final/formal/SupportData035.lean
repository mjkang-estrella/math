import SignedCatalogue
import NewCertificates0056
import NewCertificates0057
import NewCertificates0058
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport035
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 6, 5, 1, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0056.C1794, NewCertificates0056.C1795, NewCertificates0056.C1796, NewCertificates0056.C1797, NewCertificates0056.C1798, NewCertificates0056.C1799, NewCertificates0056.C1800, NewCertificates0056.C1801, NewCertificates0056.C1802, NewCertificates0056.C1803, NewCertificates0056.C1804, NewCertificates0056.C1805, NewCertificates0056.C1806, NewCertificates0056.C1807, NewCertificates0056.C1808, NewCertificates0056.C1809, NewCertificates0056.C1810, NewCertificates0056.C1811, NewCertificates0056.C1812, NewCertificates0056.C1813, NewCertificates0056.C1814, NewCertificates0056.C1815, NewCertificates0056.C1816, NewCertificates0056.C1817, NewCertificates0056.C1818, NewCertificates0056.C1819, NewCertificates0056.C1820, NewCertificates0056.C1821, NewCertificates0056.C1822, NewCertificates0056.C1823, NewCertificates0057.C1824, NewCertificates0057.C1825, NewCertificates0057.C1826, NewCertificates0057.C1827, NewCertificates0057.C1828, NewCertificates0057.C1829, NewCertificates0057.C1830, NewCertificates0057.C1831, NewCertificates0057.C1832, NewCertificates0057.C1833, NewCertificates0057.C1834, NewCertificates0057.C1835, NewCertificates0057.C1836, NewCertificates0057.C1837, NewCertificates0057.C1838, NewCertificates0057.C1839, NewCertificates0057.C1840, NewCertificates0057.C1841, NewCertificates0057.C1842, NewCertificates0057.C1843, NewCertificates0057.C1844, NewCertificates0057.C1845, NewCertificates0057.C1846, NewCertificates0057.C1847, NewCertificates0057.C1848, NewCertificates0057.C1849, NewCertificates0057.C1850, NewCertificates0057.C1851, NewCertificates0057.C1852, NewCertificates0057.C1853, NewCertificates0057.C1854, NewCertificates0057.C1855, NewCertificates0058.C1856, NewCertificates0058.C1857, NewCertificates0058.C1858, NewCertificates0058.C1859, NewCertificates0058.C1860, NewCertificates0058.C1861, NewCertificates0058.C1862, NewCertificates0058.C1863, NewCertificates0058.C1864, NewCertificates0058.C1865}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 5010839698787025024).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5010839698787025024 D i ∧ offSum 5010839698787025024 D i ≤ 3) = {D0, D1, D2, D3, D4} := by
  decide +kernel
theorem augmentation0 : augmentation 5010839698787025024 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5010839698787025024 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5010839698787025024 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5010839698787025024 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 5010839698787025024 D4 = U4 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5010839698787025024 = {U0, U1, U2, U3, U4} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5010839698787025024 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport035
