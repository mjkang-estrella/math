import Checkers
namespace Schrijver
-- Bits zero and twenty-six are adjacent across the cycle boundary.
example : validMask 27 2 (2^26 + 1) = false := by decide
-- An ordinary path would accept this two-element set.
example : (decode 27 (2^26 + 1)).card = 2 := by decide
example : validMask 27 12 21669205 = true := by decide
-- Corrupt the witness by setting bit one, adjacent to bit zero.
example : validMask 27 12 (21669205 + 2) = false := by decide
end Schrijver
