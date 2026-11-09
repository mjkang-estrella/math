# Formal audit

The final theorem `MonochromaticBox.mathdb317856` matches the original question, using real coefficients and standard library definitions. All intermediate definitions and theorems are included in `Checks.lean`; the rebuild rejects missing or duplicate coverage.

`rebuild.py` is adapted from the provided premagic certificate. `pins.json` and `lean-toolchain` use exactly the same verified dependencies. Build logs are emitted after deleting previous local compiled objects. Source SHA-256 digests, actual compiler version, dependency pins, and the union of observed axioms are recorded in `build/audit.json`.

The human source-to-formal correspondence is described in the packet README. Source archives are evidentiary inputs; they are not axioms imported into Lean.
