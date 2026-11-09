import Coverage8
import FiniteOfParts
import EndpointOfFinite
namespace Nut8
/-- Conditional assembly: compiled by replay only when Coverage8.lean is supplied. -/
theorem nut8_target (hp : PerSupport) : Target :=
  endpoint_of_finite (finite_of_parts coverage8 hp)
end Nut8
