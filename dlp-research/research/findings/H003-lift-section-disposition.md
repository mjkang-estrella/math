# H003 section review: valid conditional representation, no concentration mechanism

Grok independently reviewed the concrete section proposal. Root accepts the
geometric D/J normalization, Hensel displacement, homogeneity relation, small-image
support count and conditional dictionary solver as paper derivations. This does
not prove that any proposed section has concentrated corrections. No pilot or
general ring implementation is funded. Verified ECDLP gain remains NONE.

The corrected expression is g=((D+aU+bV)/J+phi)/(2y). The reviewer agrees J must
divide D too. Canonical representatives need not lie on the lifted curve modp²:
an on-curve recurrence must first correct y, or evaluate the odd division polynomial
in x,A,B directly. A q-torsion lift exists uniquely because q!=p. The root coordinate
and invariant differential give the displayed positive sign.

The one infinitesimal scaling dependence does not remove every coefficient
deformation at j=0 or1728. The bounded-image dictionary lower bound remains
scoped to small-image g. Realizing an arbitrary f by a section simply re-expresses
the predictor; it is not a hardness proof. The complete correction k*s(P)−s(kP)
can be written without the torsion section, but saying that D,J,U,V 'cancel' does
not demonstrate numerical concentration or independence from section choice.

## Recurrence and derivative objections not adopted wholesale

The raw review wrongly prescribes holding y independent when differentiating a
mixed x,y recurrence, and says reducing y² to the cubic changes the desired
derivative. For odd q, the desired psi_q is a polynomial in x,A,B. Its partials
are those of that polynomial. An equivalent expression using y must either be
reduced using y²=x³+Ax+B, or differentiated with the induced y variation on the
curve. Keeping y fixed generally differentiates a different off-curve extension.
Finite differences modp² likewise must use a consistently lifted curve point.

The review's particular window-extension formula divides by psi_(n−1); that is
not necessary for every logarithmic evaluator. Standard odd/even doubling
recurrences can recursively memoize a bounded-width set at each halving level
using division by2y, or use normalized even division polynomials and the cubic.
No such evaluator has been implemented for this candidate. Do not adopt the
claimed necessity of that additional quotient as a correction to all methods.
Any later implementation must show the exact window invariant, valid units,
and derivative convention before a run. No broad library follows from this issue.

## Full-cost and experiment decision

The proposed interval-containment training and independently shifted target give
a conditional success bound; canonical k' lifts modulo p must all be enumerated.
Streaming updates need the explicit modp wrap correction by[p]P and legal-lift
test. Large constant factors from252 sections and multiple dictionary windows
must be paid; one sample is not universally optimal without setup costs.

Neither quadratic carry tuning nor Teichmueller multiplicativity establishes
that complete corrections cluster in an interval. The tiny252-section sweep
would be a many-parameter exploratory search without a mechanism connecting its
outcomes to large instances. Retain these high-risk families without that pilot.
A future proposal must supply a named structural concentration claim or a more
decisive bridge. A finite failure alone does not disprove all large-instance bias.

Despite the no-experiment brief, the report states a p5,q7 numerical formula
witness without source, commands, operation counts or retained output. It does
not establish whether that was hand calculation or executed scratch code.
Root did not rerun it, and its numbers are not accepted as experimental evidence.
Preserve the report and this provenance limitation. Symbolic arguments above
stand separately from that unsupported computation. No new Lean claim or runtime.
