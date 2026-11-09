import BaseEndpoints
-- Must FAIL: the degree-10 witness does not inhabit the forbidden closed degree 12.
theorem reviewBad : XorMagic.ClosedExists 4 12 := XorMagic.Base16Closed10.exists_literal
