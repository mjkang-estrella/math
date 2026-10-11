# Retained data-inspection error

A terminal schema inspection incorrectly requested `brace["witnesses"]`.
The actual key is `extensions`, printed immediately beforehand. It raised
`KeyError: 'witnesses'`. This did not run mathematical diagnostics or
change data. The original combined stdout/stderr capture is retained
as `inspection-schema-failure-combined.log`, with the exact inspection
source in `inspection-schema-failure.py.disabled`. The final checker
uses `extensions` and validates every retained C171 and first-P8 matching.
