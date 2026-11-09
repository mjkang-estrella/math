import SupportData039
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport039
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0061.C1962, NewCertificates0061.C1963, NewCertificates0061.C1964, NewCertificates0061.C1965, NewCertificates0061.C1966, NewCertificates0061.C1967, NewCertificates0061.C1968, NewCertificates0061.C1969, NewCertificates0061.C1970, NewCertificates0061.C1971, NewCertificates0061.C1972, NewCertificates0061.C1973, NewCertificates0061.C1974, NewCertificates0061.C1975, NewCertificates0061.C1976, NewCertificates0061.C1977, NewCertificates0061.C1978, NewCertificates0061.C1979, NewCertificates0061.C1980, NewCertificates0061.C1981, NewCertificates0061.C1982, NewCertificates0061.C1983, NewCertificates0062.C1984, NewCertificates0062.C1985, NewCertificates0062.C1986, NewCertificates0062.C1987, NewCertificates0062.C1988, NewCertificates0062.C1989, NewCertificates0062.C1990, NewCertificates0062.C1991, NewCertificates0062.C1992, NewCertificates0062.C1993} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0061.obstruction1962
  · exact NewCertificates0061.obstruction1963
  · exact NewCertificates0061.obstruction1964
  · exact NewCertificates0061.obstruction1965
  · exact NewCertificates0061.obstruction1966
  · exact NewCertificates0061.obstruction1967
  · exact NewCertificates0061.obstruction1968
  · exact NewCertificates0061.obstruction1969
  · exact NewCertificates0061.obstruction1970
  · exact NewCertificates0061.obstruction1971
  · exact NewCertificates0061.obstruction1972
  · exact NewCertificates0061.obstruction1973
  · exact NewCertificates0061.obstruction1974
  · exact NewCertificates0061.obstruction1975
  · exact NewCertificates0061.obstruction1976
  · exact NewCertificates0061.obstruction1977
  · exact NewCertificates0061.obstruction1978
  · exact NewCertificates0061.obstruction1979
  · exact NewCertificates0061.obstruction1980
  · exact NewCertificates0061.obstruction1981
  · exact NewCertificates0061.obstruction1982
  · exact NewCertificates0061.obstruction1983
  · exact NewCertificates0062.obstruction1984
  · exact NewCertificates0062.obstruction1985
  · exact NewCertificates0062.obstruction1986
  · exact NewCertificates0062.obstruction1987
  · exact NewCertificates0062.obstruction1988
  · exact NewCertificates0062.obstruction1989
  · exact NewCertificates0062.obstruction1990
  · exact NewCertificates0062.obstruction1991
  · exact NewCertificates0062.obstruction1992
  · exact NewCertificates0062.obstruction1993
end Nut8.FiniteSupport039
