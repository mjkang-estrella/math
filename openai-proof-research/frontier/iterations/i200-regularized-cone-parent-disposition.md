# I200 parent disposition: large-delta lift, small-delta question unresolved

2026-10-12. **No substantial nomination. Eight accepted, two remaining.**
The [report](i200-regularized-cone-bridge.md) and
[analytic argument](../experiments/i200_regularized_cone/analytic-attempt.md)
were delivered by the completed Sol/high/ultrafast task with no pending
child runs. I199 and I201 were separately confirmed running; their files
were not read as dependencies or edited by this integration.

## Checked scope of the deductions

The parent read the full report and analytic record, the literature and
reading notes, and the source's complete cone/epigraph construction. Under
the stipulated source operations, the following written checks pass:

* Let L=[G_1 U|...|G_m U], C=L^T g L and v=L^T w. Since C=P-vv^T with
  P positive semidefinite, it has at most one negative eigenvalue. If it
  had none, a joint linear Gram factor would make the source K_0
  spectrahedral. Its accepted nonliftability excludes that case. Hence
  sigma=-lambda_min(C)>0 and sigma<=||v||^2.
* For delta>=sigma, factoring C+delta I gives a joint linear Gram factor
  of Q_delta. The source's skew-block construction is an affine pencil
  of size at most (r+1)(mr+1). Its generalized Schur complement depends
  only on Q_delta, so it agrees with the source cone even for singular X
  and even when the number of Gram columns differs from r+1.
* The alternative Gram cone is closed: integrating a represented biform
  on the product of unit spheres bounds the traces of its positive
  semidefinite Gram matrices. Subsequential compactness gives a limiting
  Gram matrix. This proves the attained threshold
  0<delta_SOS<=sigma for this particular method, not for arbitrary lifts.
* The denominator-cleared patch uses the degree-one homogeneity of
  tr(A^(-1)Q_delta(y)). Its graph equality is exact and its degree is at
  most 4r+4. The inverse-Hessian expansion in (A1) is correct; its kernel
  is radial when y!=0. The source epigraph supplies convexity of the
  remaining term. Thus the covariance contraction in (A2) is strictly
  positive for the displayed transverse immersed patch and a strictly
  positive affine moment functional. This patch cannot provide the
  desired negative moment defect.

These are scoped parent checks of technical statements, not independent
acceptance reviews. No assertion is made that absence of a bilinear Gram
factor rules out a more general finite semidefinite lift.

## Exact remaining gap and disposition

Liftability of K_delta for 0<delta<delta_SOS remains unresolved in this
record. A new obstruction would need valid control on the remaining
singular strata (y=0 and singular A), including the source's center and
analytic-selection quantifiers. A constructive resolution would need an
exact matching/lift argument valid at singular X. The positive square
root, a piecewise positivity certificate or an approximation alone is
not that argument.

The large-delta Gram construction and repaired-patch calculation do not
meet the substantial-contribution gate. The cone branch is parked pending
a new mechanism; I199 and I201 continue independently. No new agent is
launched merely to repeat either failed route.

## Provenance and preservation

The five detached written-output hashes and full-read PDF hash match the
returned values. The in-place corpus input hashes match I198's retained
source files. The source directory contains exactly the literature note
and the declared PDF. The unrelated I31 digest remains unchanged.
No source proof audit, numerical experiment or historical replay was run.

| Artifact | SHA-256 |
| --- | --- |
| report | `1a231ddb2aa064e1ff89980ea895c8fee519d054f956cc2d33cdca1848b2f45f` |
| analytic | `497eba54cd8ea6853c639d57dc09107801d46c0a253f29c16da55b79b05639ca` |
| reading log | `e4e5495c8923fa9e323901d986307b91cebaed3a2c60b78cb55fe45f3cb407d2` |
| authentication | `d6624ddcda3e8bbcb06d718944301510ec929232a12bb3643146851a3f163fd5` |
| literature | `113c56d2511f317715b57d231bc87441f9bce56ccf0d44b21108551b3ead38ac` |
| Netzer–Sanyal PDF | `4ee0218bcd4ce05f6ccc00983ccaf3392bfe64994c2046ca4bb41b509406c162` |

This outcome commit includes only the completed I200 package, this note,
and current ledger updates. Unrelated files and active-agent outputs are
excluded. Publication remains restricted to the committed research folder.
