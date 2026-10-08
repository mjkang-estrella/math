# H006 independent structured-relation cards

Native Astra /root/h006_structured_relation_ideas, independent initial brief;
no experiments, edits, children or other H006 initial proposals read. Root records
these as hypotheses, not proof of low rank, competitive cost or originality.
Main improvement NONE. Ordinary prime-order E/Fp, q comparable to p.

## T1: exact tensor exponentiation for decomposition

Fix m=5 and factor-base size B approximately q^(1/5). Enumerate B distinct valid
x-coordinates v_i, retaining both signs; charge root testing/construction. For
random known R=aG+bQ form A_R(i1,...,i5)=S6(v_i1,...,v_i5,x(R)), represented
as a tensor train (TT) over Fp. Construct the fixed-m Semaev arithmetic circuit
and initial cores explicitly, with all large constants/setup charged; no full
B^5 tensor or free rank oracle is allowed in a putatively fast implementation.

Binary exponentiate entrywise to p-1. Each Hadamard product uses Kronecker-product
cores, followed by right-to-left then left-to-right EXACT finite-field rank
factorizations. No approximate numerical truncation. Set Z=1-A^(p-1), an exact
zero indicator. Use suffix row-space bases to select a nonzero entry one index
at a time, not cancellation-prone sums. Verify the constant number of point-sign
assignments using actual group addition; retain only useful valid relations.
Collect relations including Q directly, then recover via a dependency whose
Q coefficient is nonzero. Relation rank/success and sparse linear algebra are
additional explicit assumptions, not automatic from polynomial zeros.

TT multiplication/recompression is known; exact field elimination replaces
numerical orthogonalization. Primary TT reference:
https://www.researchgate.net/profile/Ivan-Oseledets/publication/220412263_Tensor-Train_Decomposition/links/5bbfb5c5299bf1004c5a56e3/Tensor-Train-Decomposition.pdf
PKM's decomposition gap motivates the application, not its rank assumption:
https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf
YYTK's conditional Groebner analyses do not automatically cover this recurrence:
https://nutmic2019.imj-prg.fr/confpapers/SemaevECDLP.pdf

Let r bound ranks AFTER EVERY exact compression, including circuit construction;
raw multiplication ranks may be r^2. The proposer estimates conservative per-
attempt work soft-O(B*r^6) and temporary storage O(B*r^4). Assuming O(B/sigma)
attempts suffice including useful relation/rank overhead, total proposed work is
W_setup + soft-O(B^2*r^6/sigma+B^2), including actual construction, failed attempts,
random scalar combinations, extraction, signs, storage and linear-algebra retries.
With r=q^rho and sigma=q^(-s), a sufficient exponent threshold is6rho+s<1/10,
plus sub-square-root setup. Constant sigma requires rho<1/60. These are unverified
conditional bounds; no cost saving is supported yet. Fixed S6 constants may be
prohibitive at practical sizes even if asymptotic rank behavior were favorable.

Crucial unsupported primitive: sustained LOW INTERMEDIATE ranks. Low initial
polynomial rank does not imply low zero-indicator rank (H001), and a sparse final
indicator does not imply cheap computation of it. Every power's exact rank matters.

Cheapest proposed falsifier is paper analysis of intermediate A^(2^j) middle
unfoldings. A growing Omega(B) rank at both adjacent middle cuts would force
Omega(B^3)=Omega(q^(3/5)) explicit dense-core storage, defeating this specified
representation. Symmetry transfers the middle-cut rank for the identical mode grid.
A finite exact-rank diagnostic could only reject its frozen finite schedule;
it cannot prove asymptotics. No experiment authorized before this analysis.

## D1: diagonal multiplicative-orbit gcd

Assume B divides p-1 and H={t:t^B=1}; factor-base x lie in u+H and are valid curve
coordinates. For c1=1 and c2,...,cm in H chosen independently of uniform R, set
f_(c,R)(t)=S_(m+1)(u+c1*t,...,u+cm*t,x(R)). Its degree is bounded for fixed m.
Compute gcd(f,t^B-1) via binary modular exponentiation, factor the bounded-degree
gcd and verify membership/signs. Charge subgroup discovery, enumeration/root
checks and degeneracies, including a zero substituted polynomial. This genuinely
batches a whole diagonal orbit, assuming its polynomial construction is charged.

But B tuples yield at most2^m B signed sums. Uniform independent R gives at most
2^m B/q expected verified decompositions per orbit, without assuming independence
among those sums. The specified independent orbit/target procedure needs expected
Omega(q/B) trials per relation. If it recovers B independent factor-base logarithms
using Omega(B) relations, it pays Omega(q) orbit trials before other costs.
This rejects that named all-log collection method; it is not a universal lower
bound on adaptive target-dependent selection or all relation-solving strategies.

Multiplicative factor bases are known PKM prior art. Novelty of this particular
gcd application is unestablished. Reopening requires an actual cheaply productive
target-dependent orbit selector; merely naming it moves the decomposition oracle.
No experiment is warranted for D1 as specified. T1 alone proceeds to independent
mathematical/cost scrutiny, without broad Lean or implementation work.

## Root's original intermediate-rank draft (historical; review now complete)

The following preserves the initial proposed argument and its then-open gaps.
The corrected reviewed scope and proof are in ../findings/H006-random-grid-rank-draft.md.
Native Astra and Claude Opus accepted the frozen random-V dense-core obstruction
after explicit evaluation/genericity/sampling and addition-chain repairs. No
Lean proof or universal structured-factor-base exclusion is claimed.

For bivariate F with a point(x0,y0) satisfying F=0 and Fx,Fy nonzero, expand
F(x,y)^t in(x-x0). For k<=t<p, its kth coefficient has vanishing order exactly
t-k at y0: the leading term is binom(t,k)*Fx(x0,y)^k*F(x0,y)^(t-k), while
other partitions use fewer nonconstant factors and vanish to higher order.
Distinct orders would give t+1 independent coefficient functions, hence
separation rank>=t+1. This is a proposed paper lemma, not a Lean theorem.

Applying it to S6(x,y,c1,c2,c3,z) requires proving an appropriate simple mixed
factor/smooth point after specialization. Geometric sums suggest f3 factors at
x(R +/-P3 +/-P4 +/-P5), but that exact specialization and degeneracies must be
checked. Formal coefficient rank is NOT automatically sampled matrix rank.
A finite-grid transfer must establish nonzero evaluation minors, valid-curve-x
sampling, shared constants/target conditions and a controlled degree/error bound.
Disjoint row/column subsets within the same V can at most give Omega(B) minors;
claiming B independent new values in each mode would change the factor base.

If such a transfer holds for an explicitly frozen family at some t=2^j=O(B),
symmetry could force both middle TT ranksOmega(B), so dense cores already store
Omega(B^3). This would reject that dense TT schedule on that family, not all
structured factor bases, all succinct core representations or coordinate methods.
Native Astra /root/h002_arithmetic_ideas reviews this proposal and the original
cost/yield assumptions read-only. No grid, polynomial circuit or experiment is
frozen or executed yet; genericity and finite-field transfer are material gaps.
