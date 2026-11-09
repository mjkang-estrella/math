# W030 digit recursion and unbalanced frontier: parent disposition

Both reviews are terminal. **Verified complete factoring improvement: NONE.**
The parent read the entire 261-line [kernel report](W030-digit-kernel-review.md),
its prior-art scope, and the entire 214-line
[frontier report](W030-unbalanced-frontier-review.md). No experiment was run
by either child or repeated by the parent. Original report bytes are preserved.

## Digit recursion: accept the computation, correct several statements

The four-term integer cut is exact. The low/low term is the FULL product
a0*b0. High digits removed from the residual must still be retained while
forming the row-only and column-only labels. With a fixed sign the new
base alpha^(B^2) remains a unit. The frozen carry is a column scalar.
At zero residual precision the product is genuinely product(1-r_i*s_j).

The monic product/remainder-tree computation is valid over Z/NZ and costs
soft O(n+m) for one carry. For a common unit carry progression of length T,
building n*b baby roots and evaluating at m*ceil(T/b) giant points gives

    min_(1<=b<=T) O~(n*b+m*ceil(T/b))
       = O~(sqrt(n*m*T)+n+m).

The boundary cases b=1 and b=T supply the n+m terms. Actual powers,
prefactors, tags and localization are paid. This is a real supplied
separable-bucket primitive, not a consumer for a residual convolution.
The following corrections delimit acceptance.

1. A rank-one BILINEAR EXPONENT is not a separable multiplicative label.
   The report's sentence identifying those two is false. For exponent
   a*b on a,b in {0,1}, the value matrix is [[1,1],[1,alpha]], with
   determinant alpha-1; a matrix r_i*s_j has determinant zero. The
   terminal algorithm works because the residual interaction is ZERO
   and the exponent is a row term plus a column term.
2. Localization selects a NONUNIT aggregate, gcd>1 INCLUDING gcd=N,
   and descends when needed. A proper aggregate gcd need not exist when
   different rows of a zero column vanish at different prime components.
3. For signed columns, terminal injectivity on every U<M,V<M rectangle
   requires splitting positive and negative intervals, or retaining the
   at-most-two occurrences per prefix. An unsplit signed interval can
   have length >=M. The constant does not improve the pair cost.
4. T separate fixed-carry calls cost O~(T*(n+m)); they are not generally
   the same order as the b=1 joint call O~(n+m*T). The latter builds its
   degree-n polynomial once and evaluates all points together.
5. A power of a checked unit cannot become a nonunit. The proposed later
   power gcd exit is unnecessary on the actual interface. Nonunit checks
   for arbitrary supplied labels belong to the generalized primitive.
6. For M=N^theta, b=N^eta and polylogarithmic ell, the logarithm of the
   dense box is on the scale (log N)^2/log ell, not superpolynomial in
   log N. The BOX is superpolynomial in N in that regime. This repairs
   the language without making that dense implementation cheap.

Accept the scoped cost conclusion: terminal calls reproduce the surviving
pair count on short rectangles. Earlier-prefix indexing bounds are upper
bounds. Full rank over Q only obstructs a fixed number of linear features
for arbitrary vectors. Literal subset and dense-box counts price those
implementations, not all support merging, special root tables or circuits.

The prior-art search is narrow; several sources were read only at statement
or abstract scope. No absence theorem, unseen proof chain or novelty claim
is adopted. Excluding unapplied numerical theorems from this report does
not prove that rigorous exact reconstruction could never help. The monic
ring identities above can be checked directly.

All 16 local delivery payloads and 10 frozen inputs match the manifest.
No external terminal manifest hash was supplied for this round.
[Kernel intake](W030-digit-kernel-parent-intake-hashes.json).

## Unbalanced frontier: accepted with the completed interface

Accept the scaled cover in the a,b rectangle, its valuation strata, actual
weight labels s*a and N*b, and the filter residue s*a*(p-1)^2. This is a
new covering proof: s*a may exceed M, so it is not a literal application
of the old strict u,v rectangle. q=N/p may be composite. Choose s separately
at each base, adjusting it to be an ell-unit; do not discard needed bases.

Adopt the integer rounding recipes and tight widths. For scaled M choose
the least positive ell-power with P^2*M^3>=N^2, A=ceil(sqrt M), B=ceil(M/A),
and W=2*P*s*A+ceil(N*B/P). They work also at M=3. For the unscaled interior
use the review's U clamping and range-dependent W, not N*(U+V). The public
dyadic range schedule has no gap at P=N^(2/5); prime scheduling and all
valuation sums cost polynomial logarithmic factors.

The hypothetical consumer must charge by supplied occurrence counts and
preserve the ACTUAL scaled labels. A theorem only for consecutive synthetic
rows at input N*s would not suffice. Under the completed hypothesis the
local envelope remains (N/P)^(1/3); the small-factor branch sqrt(P) gives
the displayed full envelope N^(1/5) times polynomial logs. This is an
optimized upper-cost model, not a factoring lower bound.

W020 recovery makes the full composition conditional EXPECTED Las Vegas
time. Each trial must cover the full frozen range/base schedule; restarting
on one uncovered range does not inherit its trial-success bound. Neither
a new deterministic bound nor an improvement over known randomized
subexponential factoring follows from this envelope.

All 23 delivery payloads and 18 frozen inputs match. The manifest matches
the externally supplied terminal SHA-256 as well.
[Frontier intake](W030-unbalanced-frontier-parent-intake-hashes.json).

## Constructive consequence

W030 reduced the root representation and supplied exact cuts, but neither
its direct recursive consumer nor its conditional complete-range envelope
improves complete factoring complexity. The parent has already developed
[W031](../hypotheses/W031.md): price a joint quadratic-chart/carry consumer,
and independently reverse a compact Lucas circuit to expose its low jet.
The reversed-jet identities and first informative coefficient have a new
separate review. Rechecking W030 identities is not the next bottleneck.
