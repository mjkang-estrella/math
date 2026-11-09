# Round 4a handback: partial, not acceptance

The requested unconditional spectralOrder and unitCount are NOT proved. Neither TransferCountEvaluation nor PrimitivePeriodData has been proved unconditionally. No self-acceptance or credit is requested; root decides.

CountR4Period.lean proves the frequency root primitive at exactly addOrderOf k, the full one-period denominator identity, the trace constant coefficient, cyclic trace invariance under X ↦ zX, coefficient vanishing whenever e does not divide the degree, and the trace degree bound. It combines these into primitive_trace_shape: trace = 2 + C(trace.coeff e) X^e. The denominator proof applies the primitive-root factorization over the polynomial coefficient ring and evaluates the resulting bivariate identity at 1.

PrimitivePeriodData is now conditional on only PrimitiveTopCoefficient (formal/CountR4Period.lean), asserting that the top coefficient equals parityCoefficient e. CountFinal3.lean proves ChanLevine.Round4.spectralOrder and unitCount conditionally on exactly Round3.TransferCountEvaluation and Round4.PrimitiveTopCoefficient. The count evaluation remains unchanged and unproved: it still needs finite weighted inclusion–exclusion with the rotor factor, and a closed-walk/matching correspondence. These conditional endpoints do not solve MathDB 338887.

All 19 round-3a modules are frozen byte-identically, including its audits and controls. Frozen hashes are recorded before and after. No Sem modules were created. New modules are CountR4Period, CountFinal3, CountR4Controls, CountR4Audit.

Validation uses strict serial Lean 4.34.1 and leanchecker on each module after fresh source extraction, the inherited exact Python checker (104 positive-level cases), negative controls, and a declaration audit of the full reachable type/value dependency closure of local endpoint/control declarations, including generated declarations. Audit instrumentation is excluded from theorem seeds. Local flags and upstream executable metadata are reported separately in results.json. Numerical checks are diagnostics, not general proofs. Development failures are retained.

Next round: compute the top coefficient by extracting the degree-one coefficient matrix J_k = z^k [[0,z],[-1,0]] from each factor; use J^2 = -z I, separate odd/even e, and use the primitive half-power identity in the even case. This closes PrimitiveTopCoefficient and hence PrimitivePeriodData. Then prove TransferCountEvaluation from the literal finite configuration fibre; this is the untouched major combinatorial obligation. The existing denominator, invariance, degree and constant results need no further hypotheses.

There were no child agents, git operations, shared-ledger edits, network calls, uploads, external messages or browser tabs. All writes were lane-local. No upstream truth audit or novelty clearance is claimed. Root alone decides acceptance.
