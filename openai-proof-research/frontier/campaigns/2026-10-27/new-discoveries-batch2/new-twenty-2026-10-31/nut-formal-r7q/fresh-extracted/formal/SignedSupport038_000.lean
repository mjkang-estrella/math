import SupportData038
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport038
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0060.C1930, NewCertificates0060.C1931, NewCertificates0060.C1932, NewCertificates0060.C1933, NewCertificates0060.C1934, NewCertificates0060.C1935, NewCertificates0060.C1936, NewCertificates0060.C1937, NewCertificates0060.C1938, NewCertificates0060.C1939, NewCertificates0060.C1940, NewCertificates0060.C1941, NewCertificates0060.C1942, NewCertificates0060.C1943, NewCertificates0060.C1944, NewCertificates0060.C1945, NewCertificates0060.C1946, NewCertificates0060.C1947, NewCertificates0060.C1948, NewCertificates0060.C1949, NewCertificates0060.C1950, NewCertificates0060.C1951, NewCertificates0061.C1952, NewCertificates0061.C1953, NewCertificates0061.C1954, NewCertificates0061.C1955, NewCertificates0061.C1956, NewCertificates0061.C1957, NewCertificates0061.C1958, NewCertificates0061.C1959, NewCertificates0061.C1960, NewCertificates0061.C1961} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0060.obstruction1930
  · exact NewCertificates0060.obstruction1931
  · exact NewCertificates0060.obstruction1932
  · exact NewCertificates0060.obstruction1933
  · exact NewCertificates0060.obstruction1934
  · exact NewCertificates0060.obstruction1935
  · exact NewCertificates0060.obstruction1936
  · exact NewCertificates0060.obstruction1937
  · exact NewCertificates0060.obstruction1938
  · exact NewCertificates0060.obstruction1939
  · exact NewCertificates0060.obstruction1940
  · exact NewCertificates0060.obstruction1941
  · exact NewCertificates0060.obstruction1942
  · exact NewCertificates0060.obstruction1943
  · exact NewCertificates0060.obstruction1944
  · exact NewCertificates0060.obstruction1945
  · exact NewCertificates0060.obstruction1946
  · exact NewCertificates0060.obstruction1947
  · exact NewCertificates0060.obstruction1948
  · exact NewCertificates0060.obstruction1949
  · exact NewCertificates0060.obstruction1950
  · exact NewCertificates0060.obstruction1951
  · exact NewCertificates0061.obstruction1952
  · exact NewCertificates0061.obstruction1953
  · exact NewCertificates0061.obstruction1954
  · exact NewCertificates0061.obstruction1955
  · exact NewCertificates0061.obstruction1956
  · exact NewCertificates0061.obstruction1957
  · exact NewCertificates0061.obstruction1958
  · exact NewCertificates0061.obstruction1959
  · exact NewCertificates0061.obstruction1960
  · exact NewCertificates0061.obstruction1961
end Nut8.FiniteSupport038
