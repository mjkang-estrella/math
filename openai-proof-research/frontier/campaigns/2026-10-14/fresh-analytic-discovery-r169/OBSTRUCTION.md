# Prefreeze exact-rate construction and the unpaid operation

No exact theorem was frozen. The statements in this file are feasibility targets or deductions explicitly marked as such, not a weakened substitute for an old scope.

## Target tested after the complete compatible reduction

For each fixed \(0<\kappa<8\), with the exact diameter-gauge measure and whole disk variable \(X_1\) of CALCULATIONS.md, test whether a finite strictly positive limit exists:
\[
I_\kappa=\lim_{u\to\infty}u^{-q}[-\log\mathbb P(X_1>u)],\qquad q=2/(2-d).
\]
This quantifies the same untruncated whole-trace variable, including boundary visits. It is not the already-paid stretched-exponential exponent, a conditional collar theorem, a finite-mesh substitute, or an assertion of a known famous gap. Nothing here establishes that this exact-rate problem is open in all literature. It is the specific operation this construction did not close.

The closed reduction gives only
\[
0<c\le\liminf u^{-q}[-\log\mathbb P(X_1>u)]
\le\limsup u^{-q}[-\log\mathbb P(X_1>u)]\le C<\infty.
\]
The positive and finite constants survive the natural/Hausdorff normalization, but their numerical values do not.

## A concrete mesh-scale attempt

Set \(\ell=m^{-1}\) and use \(N\asymp m^2\) cells. In an admissible source ribbon, step \(j\) generates mass \(\ell^d A_j\), with \(A_j\ge a_0>0\) on its stopped success event. The source gives conditional success probability at least \(q_0>0\), uniformly in the already generated admissible past. Consequently
\[
\sum_{j=1}^{N}\ell^d A_j\ge c m^p,
\qquad -\log\mathbb P(\hbox{all successes})\le C m^2.
\]
The finite-mesh to actual-mass passage is legitimate by Section 4 of CALCULATIONS.md; that passage is not the missing operation.

To determine a rate, keep the full stopped state \(s\): mapped remaining domain, access corridor, front location, marked point/target data, and already visited regions. At step \(j\), let \(K_{j,m}(s,ds'\,da)\) be the subprobability kernel of the successful passage and rescaled mass \(A_j\). The exact generating functional for this restricted layout would be
\[
(K^{\lambda}_{1,m}K^{\lambda}_{2,m}\cdots K^{\lambda}_{N,m}{\bf1})(s_0),\qquad
K^{\lambda}_{j,m}F(s)=\int e^{\lambda a}F(s')K_{j,m}(s,ds'\,da).
\]
This formula is a finite iterated conditional expectation. The known estimate says \(K_{j,m}{\bf1}\ge q_0\) and the retained mass is bounded below. It does not replace these kernels by one stationary kernel, nor bound the error in their normalized log product by \(o(N)\). The old trace is part of the state. After flattening the current tip, locations and distortions of future cells change with the whole old hull.

Even a rate for one fixed ribbon layout would only give a lower probability bound for \(X_1>u\). To match it from above one needs an exponentially accurate decomposition of *all* high-mass configurations, including repeated visits, branches, swallowed regions for \(\kappa>4\), and near-boundary concentration. The source's slab/window argument controls their total probability up to unspecified constants in \(e^{-cN}\); it does not identify a minimizing configuration or its entropy.

One proposed repair is block gluing. Divide an \(m\)-array into blocks of width \(L\) cells, concatenate nearly optimal blocks, then let \(L\to\infty\). To preserve the rate one needs both:

1. mass lost in the connectors is \(o(m^p)\), and the logarithmic probability cost of matching entrance/exit states is \(o(m^2)\);
2. the upper decomposition into those block states costs only \(e^{o(m^2)}\) and retains every configuration contributing at the proposed rate.

The source's positive-probability local reset can be used once per step at cost \(O(m^2)\), exactly the leading scale, rather than the required lower-order error. It does allow finitely many prescribed reset operations, so merely citing dependence or a failed naive independence argument would not justify stopping. The actual missing estimate is a *uniform many-block comparison at subleading logarithmic cost*, with boundary-state control and an upper counterpart. The existing rough-state compactness produces deterministic positive constants, not closeness of log transition weights between different histories.

## Strong primary operations tested against that repair

Rezaei–Zhan 1607.03840v3, Section 6, does provide a stronger mechanism than naive independence. It selects a thin L-shaped approach, retains a favorable tip angle, separates point clusters conformally, and inducts through three cases. The lower bound keeps all target visits before a controlled outer radius. The full proof, including its final recursive choice of \(\rho_1,\ldots,\rho_n\), was read. However the constants and outer radius depend on the number of points. At page 44, the next separation depends on previous \(V_j\) and \(C_{\rho_k}\); page 46 chooses successive \(\rho_{k+1}\) sufficiently small. No \(o(m^2)\) comparison across the growing number of states follows from those operations. They should not be discarded, but their quantitative dependence would itself have to be controlled.

The multipoint hierarchy is another exact expression: the ordered \(n\)-point Green function is the first Green weight times a two-sided radial expectation of the remaining \((n-1)\)-point Green function, summed over orders. Its constants \(C_n,B_n,\beta_n,\delta_n\) in Theorems 4.1–4.2 are fixed-\(n\) quantities. The mesh separation restriction involves \(Q^{B_n}r_j/R_j\). In the relevant saddle regime, \(n\) grows and many configurations have spacings of order \(n^{-1/2}\) or smaller. One cannot interchange this limit with \(n\to\infty\) using the theorem's fixed-\(n\) error bound. The full convergence induction was not read, and no assertion is made that its constants cannot be improved; the stated and read operations do not furnish that improvement.

Holden–Yuan's reverse-flow comparison is compatible even at the boundary. CALCULATIONS.md carries it through to a Gaussian variation upper bound. It preserves enough geometry to transfer moments, but is an averaged lower distortion comparison on an event of positive probability. It does not produce the two-sided, nearly cost-free transfer of a whole exponentially rare high-mass ensemble that an exact rate would require. Their fast-crossing tail concerns *small* traversal content, with exponent \(1/(d-1)\); it cannot simply be substituted for a *large* amount of total content in a bounded disk.

## Moment and free-energy formulations of the same missing precision

If the proposed tail limit exists, elementary survival integration and Stirling asymptotics force
\[
\log\mathbb E X_1^n={n\over q}\log n-{n\over q}[1+\log(qI_\kappa)]+o(n).
\]
The actual estimates give only
\(\log\mathbb E X_1^n=(n/q)\log n+O(n)\).
Thus determining the coefficient of \(n\), not merely the leading \(n\log n\), is necessary. Multipoint constants whose logarithms are uncontrolled on that scale do not pay it.

Likewise the proposed rate would imply
\[
\log\mathbb E e^{\lambda X_1}\sim A\lambda^{q/(q-1)},\qquad
A=(q-1)q^{-q/(q-1)}I_\kappa^{-1/(q-1)}.
\]
This is the maximum of \(\lambda u-I_\kappa u^q\). Our upper and lower bounds locate the exponent \(2/d\) but leave two different constants. No converse Tauberian theorem is invoked here.

## Why convexity and scaling alone do not fill the gap

This is a diagnostic example, not a model for SLE. For \(u\ge1\), set a survival function
\[
S(u)=\exp\{-u^q[2+\tfrac12\sin(\log u)]\}.
\]
Its negative logarithm has derivative
\[
u^{q-1}\{2q+\tfrac q2\sin(\log u)+\tfrac12\cos(\log u)\}>0
\]
for \(q>2\), so it extends to a legitimate nonnegative random-variable law below 1. It obeys two-sided \(e^{-c u^q}\) estimates, has all exponential moments, an entire Laplace transform of order \(q/(q-1)\), a convex log-Laplace transform, and moment determinacy. Nevertheless \(-\log S(u)/u^q\) has no limit. Define scaled variables \(Y_R=R^dY_1\) if desired; this also satisfies the one-variable scale law. These are precisely the coarse conclusions available above. Therefore none of those abstract properties, singly or together, logically supplies the desired rate.

## Disposition

PREFREEZE/no nominee. The exact-rate bridge remains unproved. The full whole-disk stretched-exponential reduction and compatible variation improvement are retained as calculations, with their source payment made explicit. No correctness grade, substantial-contribution grade, acceptance, or campaign count is assigned. No neighboring impossibility or exhaustive-literature claim is made.
