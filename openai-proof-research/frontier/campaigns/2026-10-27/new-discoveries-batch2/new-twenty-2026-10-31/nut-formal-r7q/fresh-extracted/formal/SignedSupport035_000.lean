import SupportData035
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport035
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0056.C1794, NewCertificates0056.C1795, NewCertificates0056.C1796, NewCertificates0056.C1797, NewCertificates0056.C1798, NewCertificates0056.C1799, NewCertificates0056.C1800, NewCertificates0056.C1801, NewCertificates0056.C1802, NewCertificates0056.C1803, NewCertificates0056.C1804, NewCertificates0056.C1805, NewCertificates0056.C1806, NewCertificates0056.C1807, NewCertificates0056.C1808, NewCertificates0056.C1809} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0056.C1810, NewCertificates0056.C1811, NewCertificates0056.C1812, NewCertificates0056.C1813, NewCertificates0056.C1814, NewCertificates0056.C1815, NewCertificates0056.C1816, NewCertificates0056.C1817, NewCertificates0056.C1818, NewCertificates0056.C1819, NewCertificates0056.C1820, NewCertificates0056.C1821, NewCertificates0056.C1822, NewCertificates0056.C1823, NewCertificates0057.C1824, NewCertificates0057.C1825} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0057.C1826, NewCertificates0057.C1827, NewCertificates0057.C1828, NewCertificates0057.C1829, NewCertificates0057.C1830, NewCertificates0057.C1831, NewCertificates0057.C1832, NewCertificates0057.C1833, NewCertificates0057.C1834, NewCertificates0057.C1835, NewCertificates0057.C1836, NewCertificates0057.C1837, NewCertificates0057.C1838, NewCertificates0057.C1839, NewCertificates0057.C1840, NewCertificates0057.C1841} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0057.C1842, NewCertificates0057.C1843, NewCertificates0057.C1844, NewCertificates0057.C1845, NewCertificates0057.C1846, NewCertificates0057.C1847, NewCertificates0057.C1848, NewCertificates0057.C1849, NewCertificates0057.C1850, NewCertificates0057.C1851, NewCertificates0057.C1852, NewCertificates0057.C1853, NewCertificates0057.C1854, NewCertificates0057.C1855, NewCertificates0058.C1856, NewCertificates0058.C1857} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0056.obstruction1794
  · exact NewCertificates0056.obstruction1795
  · exact NewCertificates0056.obstruction1796
  · exact NewCertificates0056.obstruction1797
  · exact NewCertificates0056.obstruction1798
  · exact NewCertificates0056.obstruction1799
  · exact NewCertificates0056.obstruction1800
  · exact NewCertificates0056.obstruction1801
  · exact NewCertificates0056.obstruction1802
  · exact NewCertificates0056.obstruction1803
  · exact NewCertificates0056.obstruction1804
  · exact NewCertificates0056.obstruction1805
  · exact NewCertificates0056.obstruction1806
  · exact NewCertificates0056.obstruction1807
  · exact NewCertificates0056.obstruction1808
  · exact NewCertificates0056.obstruction1809
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0056.obstruction1810
  · exact NewCertificates0056.obstruction1811
  · exact NewCertificates0056.obstruction1812
  · exact NewCertificates0056.obstruction1813
  · exact NewCertificates0056.obstruction1814
  · exact NewCertificates0056.obstruction1815
  · exact NewCertificates0056.obstruction1816
  · exact NewCertificates0056.obstruction1817
  · exact NewCertificates0056.obstruction1818
  · exact NewCertificates0056.obstruction1819
  · exact NewCertificates0056.obstruction1820
  · exact NewCertificates0056.obstruction1821
  · exact NewCertificates0056.obstruction1822
  · exact NewCertificates0056.obstruction1823
  · exact NewCertificates0057.obstruction1824
  · exact NewCertificates0057.obstruction1825
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0057.obstruction1826
  · exact NewCertificates0057.obstruction1827
  · exact NewCertificates0057.obstruction1828
  · exact NewCertificates0057.obstruction1829
  · exact NewCertificates0057.obstruction1830
  · exact NewCertificates0057.obstruction1831
  · exact NewCertificates0057.obstruction1832
  · exact NewCertificates0057.obstruction1833
  · exact NewCertificates0057.obstruction1834
  · exact NewCertificates0057.obstruction1835
  · exact NewCertificates0057.obstruction1836
  · exact NewCertificates0057.obstruction1837
  · exact NewCertificates0057.obstruction1838
  · exact NewCertificates0057.obstruction1839
  · exact NewCertificates0057.obstruction1840
  · exact NewCertificates0057.obstruction1841
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0057.obstruction1842
  · exact NewCertificates0057.obstruction1843
  · exact NewCertificates0057.obstruction1844
  · exact NewCertificates0057.obstruction1845
  · exact NewCertificates0057.obstruction1846
  · exact NewCertificates0057.obstruction1847
  · exact NewCertificates0057.obstruction1848
  · exact NewCertificates0057.obstruction1849
  · exact NewCertificates0057.obstruction1850
  · exact NewCertificates0057.obstruction1851
  · exact NewCertificates0057.obstruction1852
  · exact NewCertificates0057.obstruction1853
  · exact NewCertificates0057.obstruction1854
  · exact NewCertificates0057.obstruction1855
  · exact NewCertificates0058.obstruction1856
  · exact NewCertificates0058.obstruction1857
end Nut8.FiniteSupport035
