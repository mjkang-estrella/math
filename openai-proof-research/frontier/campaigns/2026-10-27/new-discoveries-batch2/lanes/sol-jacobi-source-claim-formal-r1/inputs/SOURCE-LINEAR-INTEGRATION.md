# Literal source linear bridge integrated (partial assignment)

Root read all seven new proof modules, the audit and inventory implementation,
and all 240 actual type/axiom reports, including compiler-generated auxiliaries.
Copies into formal/ are byte-identical: source-bridge-import-map.json.

Root's fresh source-only replay in verification/source-bridge-root-replay/
passed 20 proof modules plus six source/audit/inventory checks. No prebuilt
oleans were present in the extraction. All proof logs are empty. All 240
declarations inventoried by the seven module origins are safe and use only
permitted axioms. The source bridge, inherited audits, and inventory logs
reproduce the worker byte-for-byte. Peak sampled process-tree RSS:
2748788 KiB. Binary hash and mathlib revision asserted.
The generated name finitePower._unsafe_rec has actual isUnsafe=false in the
inventory; the check uses Lean's declaration metadata, not its name spelling.

The finite-source logarithm is preserved literally, with naturality and exact
midpoint evaluation proved. R1 derives from the actual factorial products and
curve relation; R2 derives from the inverse-factorial coefficient recurrence.
Tau normalization is proved for every logarithmic coefficient. The map of the
integral sequence through a=(u+v)/2,b=(u-v)/2 has its recurrence proved; no
integrality preservation is claimed for that rational substitution.

The main all-order logarithmic chain identity is STILL ABSENT. Only n=1 is
identified with scaledH. Accordingly the assignment is partial, and this
integration accepts only the closed literal_source_linear_bridge and supporting
results. No full source/Riccati bridge, SourceClaim, acceptance, or credit is
claimed. Count stays 32/60.

Next: prove f*delta(log f)=delta(f) coefficientwise for the literal finite
power-sum logarithm, derive its Riccati recurrence from R2, identify scaledH,
and extract the odd imaginary derivative identity. Degree bounds, Catalan
attainment, final arithmetic assembly and final review remain afterward.

The byte-preserving logs have cosmetic trailing blank lines; staging permits
only that whitespace exception.
