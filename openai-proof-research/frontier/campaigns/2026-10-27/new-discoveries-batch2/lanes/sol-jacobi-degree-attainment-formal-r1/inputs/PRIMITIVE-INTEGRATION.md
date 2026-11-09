# Odd primitive component integrated

Root read the completed thread, all four proof modules, replay program, and
all 193 actual type/axiom reports. The four modules and OddPrimitiveAudit are
copied byte-identically into formal/; hashes are in primitive-import-map.json.

Root ran a fresh source-only extraction/replay in verification/primitive-root-replay/.
All twelve proof modules and four audit/inventory checks passed; the initial
extraction contained no oleans. All 193 new declarations (140 explicit and 53
generated), 186 midpoint declarations and 54 filtration declarations use only
permitted axioms. Exhaustive origin/safety inventory passed. The four actual
audit/inventory logs reproduce the worker outputs byte-for-byte. Root peak
sampled process-tree RSS was 2745200 KiB, below the 3 GiB guard. The pinned Lean
binary SHA and mathlib revision were asserted by the replay.

The triangular operator is genuinely bijective on rational polynomials and its
inverse preserves the explicit odd-denominator condition after division by a
specified power of two. The constructed primitive has its derivative and odd
normalization proved; uniqueness uses a proved derivation-kernel classification.
The closed h_odd_primitive_closed theorem instantiates the concrete midpoint
sequence without recurrence, primitive-existence, or preservation premises.
No rational-ring divisibility shortcut is used.

Combined imports with the literal source definitions/checks and binomial
valuation component are tested separately, including definitional equality of
the two TwoLocal predicates; logs are in primitive-combined-imports/.

Remaining: literal source/logarithm identification with the midpoint Riccati
sequence, degree bounds and coordinate scaling, Catalan attainment, final
SourceClaim assembly, manuscript and independent final review/packet replay.
This is a component acceptance only. Candidate credit 0; total 32/60 unchanged.
Original audit logs retain EOF blank lines to preserve byte identity; only that
cosmetic whitespace check is disabled when staging this integration.
