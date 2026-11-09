Round 3 preserves every inherited Lean source byte-for-byte, including Definitions,
Plane5, Structure, Endpoint, Closure, FiniteSystem, TruthTableCNF and PG5CNF.
The source comparison receipt is provenance.json. Consequently the literal Plane,
Minimal, TimeIs and Conjecture20 statements and their correspondence established
in rounds 1 and 2 are unchanged. No journal-version or novelty claim is added.

The new RUP implementation uses natural-number variables, with forbidden-bit
literals: (n,true) is negative. decodeVar sends 0–30 to A, 31–61 to X, 62–92
to I, 93–123 to J and 124+31*v+p to B_v,p. holds_decode transports clause
satisfaction to the pullback valuation. InputLink proves the selected literal
clauses belong to the actual Lean gate families or the actual direct families.
Thus the pilot has no assumption equating an external DIMACS file with Lean.

The Python export is compared byte-for-byte against Lean #eval output. #eval
is used solely to export data; it is absent from the proof dependency chain.
SAT solving and independent Python RUP checking are evidence, not Lean proof.

The unnormalized certificate was chosen for the pilot. It requires no normalization
units and no collineation hypothesis. The normalized certificate remains external
solver/checker evidence, without a formal symmetry claim.
