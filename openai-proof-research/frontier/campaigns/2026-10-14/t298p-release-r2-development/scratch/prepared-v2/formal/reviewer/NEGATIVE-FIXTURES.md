# Intentionally rejected Lean fixtures

Every `.lean` file under negative-fixtures is deliberately broken. These files
are not proved theorems, support lemmas or successful build targets. Their `.log`
files record expected compiler rejection. The independent audit regenerates each
fixture from the original author source and requires a nonzero compiler status
with an error diagnostic, then compares fixture and log bytes to these references.

The five controls change the k^4 denominator to k^2, drop the column-Gram premise,
drop the endpoint comparison, reverse the gap increment, or weaken strict error
control to non-strict. Fresh types/axioms for the 18 valid declarations are audited
separately. Expected rejection is a sensitivity check, not an analytic proof.
