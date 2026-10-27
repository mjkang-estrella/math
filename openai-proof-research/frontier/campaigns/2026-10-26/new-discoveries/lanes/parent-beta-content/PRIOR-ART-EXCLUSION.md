# Excluded from discovery credit — direct prior theorem corollary

**Decision: credit0; no Lean/paper/acceptance investment.** This supersedes the
candidate/novelty-pending status in the earlier PROOF.md. The mathematical
argument is preserved, but the stronger existing result below supplies its
load-bearing heterogeneous coverage claim directly.

## Actual primary prior body

IMC2024, First Day, August7,2024, Official Solutions, Problem5, proposed by
Fedor Petrov. Current official URL (followed from the competition's actual
Problems&Solutions page, not a guessed paper identifier):
https://www.imc-math.org.uk/archive/problems/2024/IMC_2024_Day_1_Solutions.pdf

The downloaded actual5-page PDF is preserved in prior-imc/ with receipt/hash,
text extraction and rendered page5. Root personally read the entire solution
and inspected the rendered page. The former /imc2024/... URL now404s; the
current /archive/problems/2024/... URL returned a genuine PDF. Failed routes
are labeled HTML in fetch-receipts, not mistaken for sources.

The problem statement uses IID uniform ball points, but its solution explicitly
proves the STRONGER deterministic inequality (its Eq1): for any fixed generic
x_1,...,x_n in the ball and collinear p,q with p between0 andq,

 sum_{epsilon in{+-1}^n} 1[p in conv(epsilon_i*x_i)]
 >= sum_{epsilon in{+-1}^n} 1[q in conv(epsilon_i*x_i)].

This is exactly the finite-sign inequality tested in our previous checker. Its
proof uses signed facet-simplex decompositions and nonnegative coefficients;
it does not have an IID premise. The probabilistic specialization in the
contest statement does not limit this deterministic theorem.

## Direct application to the source model (parent deduction)

For independent centrally symmetric X_i, the joint law is invariant under
EVERY independent coordinate sign change, even when all marginal laws differ.
Take expectations of the deterministic inequality. Each summand on a given
side has the same expectation, so cancellation of2^n gives

 P[p in conv(X_1,...,X_n)] >= P[q in conv(X_1,...,X_n)].

Beta marginals with arbitrary beta_i>=-1 are centrally symmetric and, in d>=2,
assign zero mass to proper affine hyperplanes, including uniform-sphere
marginals at beta_i=-1. The finitely many relevant facet/determinant
nongeneric configurations therefore have probability0. Usual general-position
conditions are applied only to relevant small subsets; the contest's informal
parenthetical is not used for impossible subsets larger than d+1.

Rotational invariance gives a nonincreasing radial coverage h(r). The source
expected beta-content is E[h(sqrt(T_beta))], where T_beta has Beta(d/2,beta+1)
law. For beta2>beta1>-1 the density ratio is a positive constant times
(1-t)^(beta2-beta1), decreasing in t. The standard covariance identity therefore
proves the claimed increase immediately. The sphere test-point endpoint has
content0. If strict increase is intended, h is continuous and nonconstant
(positive near0, tending to0 at1), and the strictly decreasing density ratio
gives strict covariance. These are routine applications, not a new coverage
mechanism or a further countable result.

The source is Kabluchko--Steigenberger2503.22488v1 Theorem6.8 and Conjecture6.15
p52; source/proposed proof is already archived in this lane. No claim is made
that IMC explicitly named this2025 conjecture, or that somebody already posted
its beta-content specialization. The exclusion is the campaign's **immediate
known-corollary** rule, not an invented prior exact-conjecture publication.
Cascos2009 remains relevant background, but the old observation about its IID
hypothesis no longer establishes novelty in view of Petrov's stronger theorem.

The live MathDB label can remain open despite a direct known corollary.
No external update or posting was made. Accepted tally remains21/30.
