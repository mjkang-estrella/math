# W015 parent disposition

2026-10-08. Accept the independent routing review with its implementation
clarifications. Verified new complete factoring improvement: NONE.

The exact odd-modulus halving invariant, multiplicity accounting, monic
simultaneous interval evaluator and scoped fragmentation proof survive audit.
The completed cost is O~(C_route+1+R+sqrt(H)+sqrt(U)), with actual bit work,
intermediate records, exponent width and all nonunit recovery charged. Fix a
finite routing depth: nonunits belonging to primes above H never enter the
prefix, so routing until no points remain need not terminate.

Use power-of-two block widths dividing each dyadic interval length; otherwise
unpaid tails could invalidate the batching description. Include H! in the
prefix queries and check its gcd first. A proper gcd returns a factor; a full
gcd is localized by interval bisection. Only when H! is a unit may all stopped
factorial quotients be taken. Active-product localization handles arbitrary
odd composites, including prime powers. This closes the original description's
unstated stopped-numerator branch. For arbitrary finite depth retain the
log(t+1) exponent cost; a polynomially bounded depth absorbs it into the
stated polynomial-logarithmic overhead.

The literal interval router does not supply the routing parameters needed for
the conditional N^(1/6) calculation. Early stopping leaves a large residual;
reaching the binary mixing scale materializes linearly many ordinary intervals.
This is an obstruction to this representation and cost recipe, not an actual
lower bound on every evaluator or factoring algorithm. Early factor discovery
and different representations are outside that obstruction.

The parent separately derived [valuation compression](W015-valuation-compression.md)
while the audit ran. Through the stated first s rounds it replaces the image
interval list by O(log n) preimage progressions, proving concretely that the
representation restriction can be removed. That later lemma is NOT included
in the completed independent audit. Its remaining long odd-product computation
returns to the usual N^(1/4) scale; no end-to-end improvement is claimed.

The known-prime factorial source remains known-prime/supplied-arithmetic-data
scope. Neither its exponent saving nor logarithmic refinement has been
transferred to unknown-factor composite inputs.

Evidence: the fixed parent certificate retains six cases, 1236 assertions,
5140 point visits and zero failures, including one prime algebra control.
It did not implement the fast evaluator or prove its complexity. The parent
observed its original exit 0; the later run record states this provenance.
The independent review did not rerun it. All 18 review delivery entries and
the manifest trust anchor matched (W015-parent-intake-hashes.json). The last
scripts/check.sh run passed the 12 Python tests, source screen, Lean build and
axiom audit after certificate implementation; later edits are documentation.

Continue with the separate W016 sparse-progression operation and the W014
global-cost correction, preserving task handles. A cut-product proposal beyond
the binary mixing scale needs an explicit new recurrence and recovery costs;
the uncut progression is only a unit times the original factorial.
