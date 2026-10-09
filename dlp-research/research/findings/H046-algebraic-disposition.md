# H046 algebraic cards: conditional gates, not algorithmic lower bounds

2026-10-09 UTC. Paper review of A–D in H046-operators-factory-raw.md.
Working exponent 1/2; verified complete-work improvement **NONE**. No solver
test admitted. Card B's accepted deterministic correction is in the separate
H046-isogeny-subfield-bound.md. This record narrows the remaining proposals.

## A: polynomial filters and materialized resultants

A nonzero degree-D polynomial F defines at most 2D finite curve points via
F(x(P))=0, hence density delta<=2D/q in the q-subgroup. Rational roots can fail
to lift to subgroup points; repetitions do not increase coverage. A product
of |J| Semaev resultants has degree AT MOST 2D|J|. Specialization and leading
coefficient cancellation prevent claiming exact degree without a further proof.

Under an applicable random-list model with pair-list parameter L, the
first-moment requirement L² delta of order at least q implies
D of order at least q²/(2L²). It does not by itself give constant success.
The elementary inequality

    D |J| + L/|J| >= 2 sqrt(D L)

bounds this expression, not the work of every implementation. An upper-cost
invoice softO(D|J|+|I|+delta L|J|), |I||J|=L, does not become a lower bound
by substituting it into the inequality. A claimed materialization obstruction
must first prove the actual representation size and required writes. No
general closure of polynomial filters, or equality with ordinary BSGS, follows.

The [BDLS primary paper, Theorem 4.11 and Algorithm 2](https://arxiv.org/pdf/2003.10118)
gives an upper field-operation cost for a specified elliptic index system,
with zero indices excluded. It is not automatically a theorem about an
arbitrary F-root filter. Root preparation, point generation, product formation,
exception handling and exact signed witness extraction remain charged. A
known-root product of quadratics is a possible construction, not free input.
The raw cost and success claims therefore need a precisely compatible reporter
and list distribution. The independent-progression refinement is a separate
question; deterministic or common-step progressions do not inherit H021 for free.

## C: halving an interval product

Let 1<=L<q/2 and H'=[(q+1)/2]G. The subgroup points whose doubles have abscissa
x(jG) for some 1<=j<=L are exactly

    +/- [1, floor(L/2)]G
    union +/- (H' + [0, ceil(L/2)-1]G).

Even j=2a halves to aG, while odd j=2a+1 halves to H'+aG; [2] is bijective
on the odd q-subgroup. This proves the set identity, with floor/ceiling
corrections missing in the raw report. It does not equate rational functions
without their denominators, multiplicities and leading constants.

If the FULL group E(Fp) has odd order and p>3, its short-Weierstrass cubic has
no rational root and is irreducible; its nonzero two-torsion is defined over
Fp³. The other geometric preimages are translations by these torsion points,
so a norm representation of their factors is available. Odd order of only the
chosen subgroup is insufficient for this assertion. Constructing the norm
and all exceptional/leading factors is still paid for a full function-VALUE
identity. For membership/zero testing restricted to the rational odd-order
subgroup, the exact rational preimage sets above suffice: the other geometric
preimages are nonrational, so this norm need not be evaluated. The raw extra
length-L norm-product charge is not an inherent cost of membership testing.

Evaluating 2^t independent interval products of length L/2^t using a named
square-root evaluator supplies the strategy upper invoice softO(sqrt(2^t L)),
before any extra factors and query generation. This invoice offers no improved
upper bound over a direct evaluation. It is neither a lower bound on that
strategy's actual costs nor a proof excluding shared computation between
recursive queries. No universally losing halving-recursion theorem is accepted.

## D: an explicit conditional join threshold

For a fixed filter of actual density delta=q^(-gamma), 0<gamma<1, the H021
independent-list construction uses n of order q^((1+gamma)/4). With a paid
join taking n^(2-theta) work, the advertised leading exponent must include
input construction as well as pair outputs:

    max((1+gamma)(2-theta)/4, (1-gamma)/2, (1+gamma)/4).

Assume the success law really applies, output caps preserve constant success,
and setup/extraction/recovery costs also fit. Under those assumptions, the
join term is below 1/2 exactly when theta>2gamma/(1+gamma); the other two
terms are below 1/2 for 0<gamma<1. Reaching the output exponent (1-gamma)/2
requires theta>=4gamma/(1+gamma), AND gamma<=1/3 so inputs also fit, with all
other costs bounded by that exponent. For gamma=0.1 the respective thresholds
are theta>2/11 and theta>=4/11. Thus a join barely below n^1.818 does not
automatically achieve q^0.45 total work.

Relative to enumerating n² pairs, the square-root boundary corresponds to a
fraction d^(-1/2), for d of order q^gamma. A strict exponent saving needs a
smaller power-law fraction. This does not identify which pairs to examine,
price a block selector, or supply a selective reporting algorithm.

The proposed multiplicative-root filter requires d|(p-1), a suitable supplied
or uniformly generated curve family, its actual subgroup cardinality, compact
construction and cheap membership. Listing all (p-1)/d roots would cost about
q^0.9 at gamma=0.1 when p is comparable to q, already larger than the intended
solver work. Compact membership can be cheaper than listing, but the missing
join must exploit it constructively. Storing pair outputs, indices, labels,
sorting, candidate verification, restarts and all failed work remain charged.
The primary paper's evaluation upper bounds do not prove the raw proposed
universal Omega(block length) bound for every compact aggregate.

## Evidence and review scope

Original provider/task: Factory claude-opus-5-5,
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h046-primary-public-operators-factory-opus-20261009-r1`.
Raw report retained verbatim with its source and cross-exposure limitations.
Native Astra /root/h007_additive_relations completed independent mathematical
review. Native Sol /root/h034_c4_implementation separately checked costs and
freshly read BDLS Algorithm 2, Theorem 4.11, Example 4.13 and section 4.14.
Root independently checked the threshold algebra, moment-model distinction,
halving set identity and source scope, and alone integrated the records.

The raw final "known walls" paragraph contains unsourced genus estimates,
unqualified transfer probabilities and orbit assertions. None is adopted as
a new negative theorem. Existing archived findings retain their own scopes.
No claim of new prior-art novelty is established by archive search alone.

No experiments, scripts, imports, instances or seeds used; H034 cap unchanged.
No Lean claim or Audit addition. Existing project checks are recorded in STATE
and do not certify these paper arguments. Next decisive evidence is an actual
structured reporter with a compatible success law and complete paid invoice;
the exponent threshold alone is not an algorithm or an admitted experiment.
