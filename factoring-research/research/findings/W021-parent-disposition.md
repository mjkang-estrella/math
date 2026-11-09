# W021 parent disposition

Both review reports were read completely. All 26 quadratic-review payloads
and 25 Frobenius-review payloads match their local delivery manifests. The
two *parent-intake-hashes.json files record the full checks. No external full
manifest hash was supplied in either terminal summary. Primary results below
are imported within the reviewers' stated read scope, not independently
reproved by the parent. Verified new complete factoring improvement: **NONE**.

## Quadratic product: accept with explicit scope

For a supplied unit alpha modulo arbitrary N, binary A,D,C of width W, and
length L, accept the exact block product and digit relabelling. For each
fixed epsilon>0, the reviewed composite-ring Turing-machine construction gives

    O_epsilon(L^(3/4+epsilon) * O~(log N)
              + (W+log L+1) * I(log N))

bit work, where I is integer multiplication cost. Use van der Hoeven--Lecerf
Theorem 5.5 for the Turing-machine claim; KU Corollary 4.3 alone supplies the
RAM statement. The extension-ring embedding used to meet the former's k>=2
condition is explicit and constant-size. This is a supplied-product theorem,
not a unit-cost ring-operation count or an implemented fast evaluator.

Binary exponent setup is additive, using finite differences. Balanced
localization repeats that setup at O(log L) levels even though the main
length term sums geometrically. Zero integer exponent locations must be
removed with coverage re-established; a zero polynomial is inadmissible.
Small lengths use a direct fallback. No high-order base assumption is needed.

The rectangular coefficient box has Theta(b^3) slots. This is the storage
and construction bound we use; no further claim about every specialized
coefficient remaining nonzero modulo every composite N is needed. The digit
map is applied after multiplication. It cannot be used as a multiplicative
map into a fixed small-degree box.

The independent fixed certificate passed 8 cases in 3,873 charged events.
It used literal polynomial evaluation, not KU/vdH--L, so it checks the exact
algebra only. Its retained execution-directory deviation did not change code
or cases. The parent did not rerun it. The fast theorem's constants can be
enormous; no practical crossover or complete speedup follows from this proof.

No novelty is accepted: the result combines known block identities, digit
segmentation and multivariate evaluation. Linear exponents have a stronger
square-root product comparator. The review's broad q-holonomic classification
and its uncited-from-memory subexponential baseline are not needed or promoted
by this disposition; neither is a global claim that improving 3/4 is an open
problem after an exhaustive literature survey. The correct matched factoring
baseline still depends on randomization and proof/heuristic assumptions.

The parent's later fixed-degree/batch-offset continuation was outside this
review. W022 develops a concrete quartic root-chart family; its coverage and
costs have a separate audit. A quadratic defining congruence never licenses
calling an arbitrary modular root table a quadratic integer exponent.

## Frobenius folding: keep identities and finite evidence, revise mechanism

Accept the unfolded first-support coefficient at the smaller prime and the
coprime-r Frobenius permutation. Folding loses the integer degree divisibility
marker. Whole-vector content and individual coordinate gcds are different:
the former divides the base-2 Fermat gcd, while the latter may give additional
witnesses. Corrected r=2 and coprime r=3 reduce to base-2 Fermat gcd; raw r=3
also permits the scalar gcd(N,2^N+1). The prime-sharing r cases must be compared
against plain gcd(N,r), including the complete public menu.

The fixed 24-case certificate used 18,668 events, retained all coefficient
vectors and verified them independently. It found extra witnesses on some
toy cases but supplies no input distribution, completeness or speed theorem.
No coefficient-independence probability is accepted. The parent did not rerun
it. The primitive is a finite cyclotomic recurrence filter, not the full AKS
algorithm and not an inherited factor-extraction guarantee from primality.

Adaptive truncation modulo X^(B+1) preserves support and eventually exposes
the first prime index, but its literal arrays and computation cost remain
large. That is a concrete repair of aliasing, not a compressed-prefix oracle.
W022 B changes the target again: an explicit derivative coefficient with
factor-selective multiplicity on a specified semiprime family. Its residue
acquisition is still expensive and is under independent review.
