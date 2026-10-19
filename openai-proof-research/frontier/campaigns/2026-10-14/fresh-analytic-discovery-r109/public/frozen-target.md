# T082C109 — logarithm-free disjoint-annulus count

Author research target, not a theorem or nomination. Original prose CC BY 4.0.

For complex F,G in L^3(R^2), define
B_(e,R)(F,G)(x,y) = integral_(e<|t|<R) F(x+t,y)G(x,y+t) dt/t.
Use the common almost-everywhere representative and rational endpoints of source082. For each integer n>=1 let S_n(F,G)(x,y) be the supremum of the sum of |B_(e_j,R_j)(F,G)(x,y)| over all lists of at most n pairwise disjoint open intervals (e_j,R_j) in (0,infinity), with positive rational endpoints. Choices may depend arbitrarily and measurably on (x,y); touching endpoints are allowed and the empty sum is zero.

Target: there exists one finite absolute C such that, for every n>=1 and every such complex F,G,

    ||S_n(F,G)||_(L^(3/2)(R^2)) <= C sqrt(n) ||F||_3 ||G||_3.

C is independent of n, both inputs, every scale, endpoint separation, and the choice of the intervals. There is no finite-frequency, fixed-partition, smooth-truncation, dyadic-only, real-input, or finite-scale replacement. No r=2 variation or supremum-inside-norm jump assertion is silently included.

Stipulated source: all theorems and operative proof operations of openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, under their printed hypotheses. Source082's annular manuscript thm:count already proves the same statement with an extra log(2+n); prop:smooth-switches already gives sqrt(n) for smooth annuli. Its frequency-block and rough-kernel operations are credited in full. No upstream truth audit is undertaken.

Chronology: this freeze follows actual source reading identifying the rough frequency-block summation, the parent-r3 asymmetric-exponent screen, the three-family comparison, and preliminary examination of whether one may integrate all frequency blocks together. It precedes development of a complete new estimate or counterexample. Initial broad catalogue/history outputs were partly truncated; the reading ledger will not represent them as a complete semantic audit. No contribution or correctness gate is assigned here.
