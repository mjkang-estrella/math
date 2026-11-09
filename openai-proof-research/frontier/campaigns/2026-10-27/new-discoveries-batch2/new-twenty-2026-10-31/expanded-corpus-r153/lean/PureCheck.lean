import Delta153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delta153
-- This is a finite computation, not a full source endpoint.
theorem pure_lower_check : pureLower 18 11 original = true := by decide
#print axioms pure_lower_check
end Delta153
