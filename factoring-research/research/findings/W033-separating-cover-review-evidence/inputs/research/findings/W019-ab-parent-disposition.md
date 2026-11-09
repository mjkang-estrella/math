# W019 A/B parent disposition

2026-10-08 local. Both reports read in full. C is still a separate live audit.
Verified new complete factoring improvement: **NONE**.

## A: useful N-only coverage, at an already known exponent

Accept the signed modular rectangle, the square-modulus weighted-sum
constraint, the simple-root construction and the collision consumer with
the review's exact integer boundaries. In particular, use X>=4sqrt(N/m),
U=ceil(sqrt(mN)/X), V=ceil(m/U), W<=6sqrt(mN); mathematical floors for
negative indices; every repeated coefficient tag; and all giant ceilings.
The reviewed small-factor cutoff and perfect-power preprocessing extend
coverage to all composite inputs. The resulting mathematical composition
has expected N^(1/5)*poly(log N) bit cost, not an implemented new solver.

This reaches a known exponent and is not a deterministic improvement.
The independent prior-art comparison identifies Harvey's shared weighted
sum consumer and Harvey--Hittmeir's modular stationary constraint as close
antecedents. Accept the computation, not a priority claim. The later
rank-three lattice paper was inspected only in the stated passages; its
entire theorem is not certified by that comparison.

Accept A7's shared square roots. Signed-v character classes, inverses modulo
m^2 and the C2=eta*C0 chart factor are essential. At most U+2V+1 root calls
construct the implicit array. Materializing the pair entries still costs UV;
near the unbalanced endpoint even U+V has order m. Retain the exact carry
correction alpha^s=alpha^r*beta^(-c) and shifted interval. There is no supplied
sublinear collision evaluator. The N^(1/6) balance remains conditional on
an absent algorithm and on all acquisition/recovery costs being paid.

All 28 payloads and 29 checksum entries matched the terminal manifest hash;
see [A intake](W019-A-parent-intake-hashes.json). No experiment ran.

Constructive continuation: the parent has now proposed
[annihilator-based collision extraction](W020-collision-annihilator-extraction.md).
It changes full-match recovery rather than importing A's uniqueness rule
as a universal requirement. That new random-base argument is under its own
audit and is not accepted by this A disposition.

## B: repair the pivot law; retain the known computation

Accept cancellation and polynomial group-operation cost, but withdraw the
parent's uniform per-sample half-success claim with arbitrary pivot. With
swaps, success means the generated subgroup is noncyclic. Failure does not
always mean the new sample lies in the old pivot subgroup. In
C2 x C_(2^k), starting with the long factor's top involution gives success
only 2^(-k); the counterexample is retained, not weakened away.

Accept the repaired law: a maximal-order pivot gives success at least one
half for a fresh uniform sample; retaining the larger-order pivot after
failure gives at most four expected samples from an arbitrary starting
pivot. Individual odd parts of verified annihilators preserve the relevant
cyclic subgroups. They cannot themselves bias this success event, although
sample generation, selection and dependence can.

Accept the squarefree odd semiprime quadratic-form interface as proved by
the complete ambiguous-form enumeration. For N=1 mod4, use D=-4N and
extract from any nontrivial involution except the known J. For N=3 mod4,
use D=-N; the 2-part is cyclic and its unique nontrivial involution already
splits N, so cancellation is unnecessary. Do not extend this interface to
nonfundamental discriminants without proof.

The mechanism is already in Schoof's class-group factoring method and in
general p-group basis algorithms. No novelty or improved exponent is
retained. The one frozen certificate's 11 assertions passed with 4,454
charged events; it checks small groups and 73 semiprimes below 400, not
uniform class-group sampling or asymptotics. Parent did not rerun it.

All 24 payload hashes matched; the full manifest hash matches its local
checksum and the prefix supplied in the terminal message. That terminal
message did not supply a full external anchor. See
[B intake](W019-B-parent-intake-hashes.json).

Constructive response: [W020 annihilator amortization](W020-annihilator-amortization.md)
uses each small-order result to strengthen a common divisor constraint and
shrink the next interval. Its proposed total search cost is O~(sqrt(W)+K)
instead of K independent interval searches. This is a concrete new parent
derivation under independent review; the single-search exponent bottleneck
and generation/analytic assumptions remain.
