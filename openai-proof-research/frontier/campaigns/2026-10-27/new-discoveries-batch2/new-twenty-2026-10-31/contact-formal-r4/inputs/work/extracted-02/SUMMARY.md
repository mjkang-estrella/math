# MathDB 365301: formalization r3, partial and zero credit

The required `ContactPilot.refutation : ¬ ContactPilot.SourceConjecture` is
absent. The campaign count stays 21/40 beyond the previous 39. Root acceptance
and independent review remain required; this lane does not self-accept.

The first ordered obligation is closed: `numerator_denominator_reduced` proves
that every common divisor in ℂ[Z,W] of the exact assigned n and q is a unit.
The proof establishes irreducibility of both numerator factors, rules out
divisibility into q by evaluation, and combines relative primality in the
original bivariate ring. No rational-function-field surrogate is used.

The second obligation advances substantially. `CayleyPolynomials.lean` defines
the cleared degree-(3,2) pair, proves the two clearing identities, proves the
boundary zero at (-1,1) and denominator nonzeroness as a polynomial, and gives
the beta(n/q) representation under explicit coordinate/q nonzero premises.
`BidiskReduced.lean` proves `bidisk_pair_reduced` for the actual cleared pair.
Its proof factors cayleyN into three irreducibles, excludes all three from
cayleyQ by exact evaluation, then uses invertible linear combinations.

The next exact lemma is denominator stability on the whole open bidisk.
The support degree bounds, reflected-numerator identity, unconditional graph
representation, uniform Cayley zero-set transfer, contact-two exclusion and
literal refutation remain unproved. Definitions and all nine inherited Lean
modules are byte-identical. No inherited source statement was weakened.

The final validation receipts and declaration counts are recorded in
results.json and work/extracted-02/replay-logs. This is a source-only partial
certificate, not an accepted solution. See REPRODUCE.md and the correspondence
table. Input before/after hashes and copied-input identity checks are under
inputs/. Novelty limitations from the supplied independent review remain;
no external research or new novelty clearance is claimed.
