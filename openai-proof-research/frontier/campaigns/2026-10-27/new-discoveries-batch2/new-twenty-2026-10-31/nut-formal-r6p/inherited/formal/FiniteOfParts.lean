import NutInterface
namespace Nut8
/-- Catalogue coverage and per-support exclusion compose into the finite obstruction. -/
theorem finite_of_parts (hc : Coverage8) (hp : PerSupport) : FiniteObstruction := by
  intro C ε s ha
  obtain ⟨e, code, hcode, hsupp⟩ := hc C s (admissible_structural C ε s ha)
  apply obstruction_of_relabel e C
  exact hp code hcode (C.submatrix e e) s
    (admissible_structural _ ε s (admissible_relabel e C ε s ha)) hsupp
end Nut8
