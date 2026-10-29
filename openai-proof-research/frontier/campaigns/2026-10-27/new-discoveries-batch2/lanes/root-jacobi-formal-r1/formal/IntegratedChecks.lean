import SourceChecks
import BinomialOddSum
import OddPrimitiveSequence
set_option autoImplicit false
set_option warningAsError true
#check JacobiShifted.SourceClaim
#check sourceKappa_one
#check JacobiShifted.binomialOddSum_valuation
#check JacobiShifted.Midpoint.h_odd_normalForm_ring
#check JacobiShifted.Midpoint.h_odd_extraction_divisible
#check JacobiShifted.MidpointRational.h_odd_primitive_closed
example (q : ℚ) : JacobiShifted.TwoLocal q ↔ JacobiShifted.MidpointRational.TwoLocal q := Iff.rfl
