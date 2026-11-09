import SupportData036
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport036
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0058.C1866, NewCertificates0058.C1867, NewCertificates0058.C1868, NewCertificates0058.C1869, NewCertificates0058.C1870, NewCertificates0058.C1871, NewCertificates0058.C1872, NewCertificates0058.C1873, NewCertificates0058.C1874, NewCertificates0058.C1875, NewCertificates0058.C1876, NewCertificates0058.C1877, NewCertificates0058.C1878, NewCertificates0058.C1879, NewCertificates0058.C1880, NewCertificates0058.C1881, NewCertificates0058.C1882, NewCertificates0058.C1883, NewCertificates0058.C1884, NewCertificates0058.C1885, NewCertificates0058.C1886, NewCertificates0058.C1887, NewCertificates0059.C1888, NewCertificates0059.C1889, NewCertificates0059.C1890, NewCertificates0059.C1891, NewCertificates0059.C1892, NewCertificates0059.C1893, NewCertificates0059.C1894, NewCertificates0059.C1895, NewCertificates0059.C1896, NewCertificates0059.C1897} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0058.obstruction1866
  · exact NewCertificates0058.obstruction1867
  · exact NewCertificates0058.obstruction1868
  · exact NewCertificates0058.obstruction1869
  · exact NewCertificates0058.obstruction1870
  · exact NewCertificates0058.obstruction1871
  · exact NewCertificates0058.obstruction1872
  · exact NewCertificates0058.obstruction1873
  · exact NewCertificates0058.obstruction1874
  · exact NewCertificates0058.obstruction1875
  · exact NewCertificates0058.obstruction1876
  · exact NewCertificates0058.obstruction1877
  · exact NewCertificates0058.obstruction1878
  · exact NewCertificates0058.obstruction1879
  · exact NewCertificates0058.obstruction1880
  · exact NewCertificates0058.obstruction1881
  · exact NewCertificates0058.obstruction1882
  · exact NewCertificates0058.obstruction1883
  · exact NewCertificates0058.obstruction1884
  · exact NewCertificates0058.obstruction1885
  · exact NewCertificates0058.obstruction1886
  · exact NewCertificates0058.obstruction1887
  · exact NewCertificates0059.obstruction1888
  · exact NewCertificates0059.obstruction1889
  · exact NewCertificates0059.obstruction1890
  · exact NewCertificates0059.obstruction1891
  · exact NewCertificates0059.obstruction1892
  · exact NewCertificates0059.obstruction1893
  · exact NewCertificates0059.obstruction1894
  · exact NewCertificates0059.obstruction1895
  · exact NewCertificates0059.obstruction1896
  · exact NewCertificates0059.obstruction1897
end Nut8.FiniteSupport036
