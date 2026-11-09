import SupportData037
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport037
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0059.C1898, NewCertificates0059.C1899, NewCertificates0059.C1900, NewCertificates0059.C1901, NewCertificates0059.C1902, NewCertificates0059.C1903, NewCertificates0059.C1904, NewCertificates0059.C1905, NewCertificates0059.C1906, NewCertificates0059.C1907, NewCertificates0059.C1908, NewCertificates0059.C1909, NewCertificates0059.C1910, NewCertificates0059.C1911, NewCertificates0059.C1912, NewCertificates0059.C1913, NewCertificates0059.C1914, NewCertificates0059.C1915, NewCertificates0059.C1916, NewCertificates0059.C1917, NewCertificates0059.C1918, NewCertificates0059.C1919, NewCertificates0060.C1920, NewCertificates0060.C1921, NewCertificates0060.C1922, NewCertificates0060.C1923, NewCertificates0060.C1924, NewCertificates0060.C1925, NewCertificates0060.C1926, NewCertificates0060.C1927, NewCertificates0060.C1928, NewCertificates0060.C1929} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0059.obstruction1898
  · exact NewCertificates0059.obstruction1899
  · exact NewCertificates0059.obstruction1900
  · exact NewCertificates0059.obstruction1901
  · exact NewCertificates0059.obstruction1902
  · exact NewCertificates0059.obstruction1903
  · exact NewCertificates0059.obstruction1904
  · exact NewCertificates0059.obstruction1905
  · exact NewCertificates0059.obstruction1906
  · exact NewCertificates0059.obstruction1907
  · exact NewCertificates0059.obstruction1908
  · exact NewCertificates0059.obstruction1909
  · exact NewCertificates0059.obstruction1910
  · exact NewCertificates0059.obstruction1911
  · exact NewCertificates0059.obstruction1912
  · exact NewCertificates0059.obstruction1913
  · exact NewCertificates0059.obstruction1914
  · exact NewCertificates0059.obstruction1915
  · exact NewCertificates0059.obstruction1916
  · exact NewCertificates0059.obstruction1917
  · exact NewCertificates0059.obstruction1918
  · exact NewCertificates0059.obstruction1919
  · exact NewCertificates0060.obstruction1920
  · exact NewCertificates0060.obstruction1921
  · exact NewCertificates0060.obstruction1922
  · exact NewCertificates0060.obstruction1923
  · exact NewCertificates0060.obstruction1924
  · exact NewCertificates0060.obstruction1925
  · exact NewCertificates0060.obstruction1926
  · exact NewCertificates0060.obstruction1927
  · exact NewCertificates0060.obstruction1928
  · exact NewCertificates0060.obstruction1929
end Nut8.FiniteSupport037
