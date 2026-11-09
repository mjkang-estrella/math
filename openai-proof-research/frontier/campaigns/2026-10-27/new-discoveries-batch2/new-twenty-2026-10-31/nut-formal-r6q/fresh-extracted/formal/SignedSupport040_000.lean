import SupportData040
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport040
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0062.C1994, NewCertificates0062.C1995, NewCertificates0062.C1996, NewCertificates0062.C1997, NewCertificates0062.C1998, NewCertificates0062.C1999, NewCertificates0062.C2000, NewCertificates0062.C2001, NewCertificates0062.C2002, NewCertificates0062.C2003, NewCertificates0062.C2004, NewCertificates0062.C2005, NewCertificates0062.C2006, NewCertificates0062.C2007, NewCertificates0062.C2008, NewCertificates0062.C2009, NewCertificates0062.C2010, NewCertificates0062.C2011, NewCertificates0062.C2012, NewCertificates0062.C2013, NewCertificates0062.C2014, NewCertificates0062.C2015, NewCertificates0063.C2016, NewCertificates0063.C2017, NewCertificates0063.C2018, NewCertificates0063.C2019, NewCertificates0063.C2020, NewCertificates0063.C2021, NewCertificates0063.C2022, NewCertificates0063.C2023, NewCertificates0063.C2024, NewCertificates0063.C2025} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0063.C2026, NewCertificates0063.C2027, NewCertificates0063.C2028, NewCertificates0063.C2029, NewCertificates0063.C2030, NewCertificates0063.C2031, NewCertificates0063.C2032, NewCertificates0063.C2033, NewCertificates0063.C2034, NewCertificates0063.C2035, NewCertificates0063.C2036, NewCertificates0063.C2037, NewCertificates0063.C2038, NewCertificates0063.C2039, NewCertificates0063.C2040, NewCertificates0063.C2041} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0062.obstruction1994
  · exact NewCertificates0062.obstruction1995
  · exact NewCertificates0062.obstruction1996
  · exact NewCertificates0062.obstruction1997
  · exact NewCertificates0062.obstruction1998
  · exact NewCertificates0062.obstruction1999
  · exact NewCertificates0062.obstruction2000
  · exact NewCertificates0062.obstruction2001
  · exact NewCertificates0062.obstruction2002
  · exact NewCertificates0062.obstruction2003
  · exact NewCertificates0062.obstruction2004
  · exact NewCertificates0062.obstruction2005
  · exact NewCertificates0062.obstruction2006
  · exact NewCertificates0062.obstruction2007
  · exact NewCertificates0062.obstruction2008
  · exact NewCertificates0062.obstruction2009
  · exact NewCertificates0062.obstruction2010
  · exact NewCertificates0062.obstruction2011
  · exact NewCertificates0062.obstruction2012
  · exact NewCertificates0062.obstruction2013
  · exact NewCertificates0062.obstruction2014
  · exact NewCertificates0062.obstruction2015
  · exact NewCertificates0063.obstruction2016
  · exact NewCertificates0063.obstruction2017
  · exact NewCertificates0063.obstruction2018
  · exact NewCertificates0063.obstruction2019
  · exact NewCertificates0063.obstruction2020
  · exact NewCertificates0063.obstruction2021
  · exact NewCertificates0063.obstruction2022
  · exact NewCertificates0063.obstruction2023
  · exact NewCertificates0063.obstruction2024
  · exact NewCertificates0063.obstruction2025
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0063.obstruction2026
  · exact NewCertificates0063.obstruction2027
  · exact NewCertificates0063.obstruction2028
  · exact NewCertificates0063.obstruction2029
  · exact NewCertificates0063.obstruction2030
  · exact NewCertificates0063.obstruction2031
  · exact NewCertificates0063.obstruction2032
  · exact NewCertificates0063.obstruction2033
  · exact NewCertificates0063.obstruction2034
  · exact NewCertificates0063.obstruction2035
  · exact NewCertificates0063.obstruction2036
  · exact NewCertificates0063.obstruction2037
  · exact NewCertificates0063.obstruction2038
  · exact NewCertificates0063.obstruction2039
  · exact NewCertificates0063.obstruction2040
  · exact NewCertificates0063.obstruction2041
end Nut8.FiniteSupport040
