import FiniteOfParts
import EndpointOfFinite
namespace Nut8
/-- Fully checked composition, retaining exactly the two outstanding finite parts. -/
theorem target_of_parts (hc : Coverage8) (hp : PerSupport) : Target :=
  endpoint_of_finite (finite_of_parts hc hp)
end Nut8
