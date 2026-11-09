# Counting lane handback — partial, not acceptance

MathDB 338887 is not fully proved by this packet. No acceptance or credit is requested. Root decides.

CountFinal.lean provides unconditional `ChanLevine.rotationCount : RotationCount` and `ChanLevine.arithmeticOrbit : ArithmeticOrbit`. It provides ONLY `ChanLevine.unitCount : SpectralOrder → UnitCount`. The requested unconditional `unitCount : UnitCount` remains open.

New modules:

- CountRotation: translation of configurations, preservation of the frozen CycleTest and chip level, exact weight shift, and an equivalence of counted fibres. It proves the rotation target without premises.
- CountArithmetic: exact unit-times-gcd decomposition, equal-gcd unit orbit, the Bézout kernel computation, and unit lifting through the gcd modulus. It proves the arithmetic target without premises. The decomposition proof follows the proof of mathlib's ZMod.eq_unit_mul_divisor but retains the exact gcd witness.
- CountFourier: finite Fourier inversion and injectivity over any characteristic-zero field with a primitive additive character; compatibility with unit multiplication; a primitive character into a cyclotomic extension of ℚ; and reduction of UnitCount to the single explicit Prop SpectralOrder.
- CountTransfer: the corrected domino determinant, direct 2×2 Cayley–Hamilton, and matrix and trace Lucas recurrences over any commutative ring. These identities are proved but not yet connected to the configuration generating function.
- CountControls: small kernel-decided examples and negative identities.
- CountAudit: complete declaration dependency inventory from all local declarations in the final/control import closure, including generated declarations, with recursive type and value dependencies and a transitive axiom inventory.

The seven original modules are byte-identical to round 1, both in this lane and the extracted replay. The round-1 zip input has the exact required SHA-256. New modules all use Count names; no Sem module was created. No child agents, git, shared ledger edits, network, uploads, external messages or browser tabs were used. All writes remain inside this lane.

Validation: see results.json and fresh-extraction/logs/replay-result.json. Every source module receives a strict serial build and leanchecker. The independent exact checker covers all 104 positive-level cases for 3 ≤ n ≤ 10 and m ≤ 2n, checking count symmetries, arithmetic orbit, matching expansion, period trace and determinant, period reduction, and coefficient formula. These are diagnostics, not a proof of the analytic gap. Original failed development logs remain available. The first checker run failed only because its polynomial remainder representation retained a trailing zero; the normalization was corrected and rerun. Two attempts importing analytic Fourier infrastructure failed the -M3500 memory cap; the final algebraic Fourier route fits that cap.

Audit limitation: all 26,234 declarations in the reachable closure of the 158 local declarations were inventoried. No unsafe or partial flags occur, no local extern/implemented_by flags occur, and the only axioms are propext, Classical.choice and Quot.sound. There are 62 upstream extern/implemented_by declarations (for example Nat.gcd, Int.emod and List.attachWith). Therefore the stronger requirement of no such metadata anywhere in the upstream closure is not passed. Nothing is silently waived. Audit instrumentation itself is not part of the theorem dependency seed. See the full CountAudit log for every declaration.

# Exact remaining Prop and next round

The only residual counting premise is `ChanLevine.SpectralOrder` in CountFourier.lean. For every n ≥ 3, m ≥ 1, and frequencies k,l with equal additive order, it asserts equality of the finite Fourier coefficients of the frozen testCount vector, using a primitive additive character into a cyclotomic field over ℚ. This is the algebraic root-of-unity form of the unproved transfer-matrix evaluation; it is a Prop definition, not an axiom.

Next implement the finite/truncated generating function connecting CycleTest counts to the matching expansion, retaining the factor z per forced facing pair. Prove the matching expansion equals the cyclic domino trace. Formalize period reduction and the primitive-root denominator product. Then prove the period trace identity using polynomial degree, substitution invariance, the constant coefficient and the parity-dependent top coefficient. The already proved Lucas recurrence propagates the period trace to n vertices. Extract coefficients to prove SpectralOrder, and replace conditional unitCount with the exact unconditional target. The finite Fourier inversion is already discharged and does not require the heavy analytic ZMod.dft imports. Resolve the blanket upstream metadata audit requirement with root; the frozen base itself reaches kernel arithmetic with extern metadata.
