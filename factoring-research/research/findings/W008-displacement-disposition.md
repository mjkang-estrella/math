# W008 — displacement closure and scalar-tree disposition

2026-10-08. Parent intake of completed task C.
[Report](W008-displacement-review.md) and frozen inputs are preserved;
all eleven delivery hashes passed. No factoring experiment, source or
Lean change, or new complexity improvement.

Accept the exact determinant formula in the [parent calculation](W008-displacement-product.md)
and its transfer to generic characteristic-zero split-list inputs.
One multiplication of two factors, each of displacement rank two in the
explicit family, gives displacement rank K. For K=2 a single factor
already has full rank, so unbounded growth refers to increasing K.

Accept only the explicit dense-generator consequence: K generator columns
force quadratic allocation when all K-by-K entries are materialized.
The same witness has a compact anti-diagonal displacement and scalar
norm 1. It is therefore especially unsuitable as a lower bound for
scalar norm computation, all implicit representations, or factoring.

The audited scalar norm tree has a correct multiplicative update, but
its leaf acquisition recreates G(T)=product_(c,d)(T-c-d), a degree-K^2
polynomial. The specified elementary implementation costs Theta(K^4)
ring work; replacing its polynomial arithmetic by the already paid fast
control recovers K^2*poly(log N), not a saving. Leaving G factored saves
storage but the specified direct evaluations still take K^4 work.

Disposition: close bounded Hankel-displacement-rank closure and this
shared dense-G implementation as subquadratic routes. Keep direct
compact-grid products and genuinely different scalar computations open.
A cheap determinant identity alone does not pay for the acquired norms.
The next parent-led acquisition mechanism is [W009](../hypotheses/W009.md),
while independent W007 growth audits continue.
