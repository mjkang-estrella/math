Provider: codex / gpt-6.1-sol.
TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h019-relation-detectors-sol-20261008-r1
Status: completed, no pending children. Unendorsed report; independent review follows.

Best supported complexity remains the classical square-root reference, with applicable automorphisms and all costs charged. **Verified gain: NONE.** I examined four concrete detector constructions; none currently merits an experiment. Two admit useful paper falsifiers, and two expose narrower missing operations.

I read RESEARCH_LOOP.md, RESEARCH_TEAM.md, authoritative STATE, and the relevant H017/H018 detector and disposition records. Where STATE’s BM status lagged your brief, I used your update: four fixed features, L64, one \(p=8191,q=8053\) fixture, saved-data audit pending. I drew no asymptotic inference from it. No experiments, edits, child tasks, commits, or consultation with live proposers occurred.

Throughout, a recovered signed relation between labelled points gives
\[
A G+B Q=O,\qquad k=-A/B\bmod q
\]
when \(B\ne0\). Rejecting zero coefficients, recovering signs, and verifying \(kG=Q\) remain paid.

**1. Exact witness-count contraction: a substantial rank obstruction for this specific ansatz**

**Operation.** Replace the dense SP3 zero tensor by separated features:
\[
K(P,R,S)=\mathbf1[\text{some signed relation}],
\qquad
K(P,R,S)=\sum_{t=1}^{r}u_t(P)v_t(R)w_t(S).
\]
Then count witnesses without emitting triples:
\[
Z=\sum_t
  \Big(\sum_{P\in A}u_t(P)\Big)
  \Big(\sum_{R\in B}v_t(R)\Big)
  \Big(\sum_{S\in C}w_t(S)\Big).
\]
A positive integer count permits recursive list restriction to locate a witness. Thus this specifies detection and extraction, rather than assuming a useful signal.

**Hoped-for gain.** With cheaply evaluated features, \(r=o(\sqrt n)\) would make the initial contraction \(o(n^{3/2})\), apart from charged localization and setup.

**Paper falsifier.** The exact kernel cannot have such a uniform separated rank.

For the unsigned kernel, fixing \(S\) gives the \(q\times q\) permutation matrix
\[
K_S(a,b)=\mathbf1[a+b+s=0],
\]
which has rank \(q\).

There is also a coordinate-aware signed version. On the full group, fix nonzero \(c\) and define
\[
H_c(a,b)=
\mathbf1[a+b+c=0]+\mathbf1[a+b-c=0]
+\mathbf1[a-b+c=0]+\mathbf1[a-b-c=0].
\]
On even functions, its action is
\[
(H_cf)(a)=2\big(f(a+c)+f(a-c)\big).
\]
Over \(\mathbb C\), the cosine Fourier basis has eigenvalues
\(4\cos(2\pi tc/q)\), all nonzero for odd prime \(q\). Hence its rank on the even subspace is \((q+1)/2\). Removing the infinity orbit’s row and column lowers rank by at most two.

For affine, nonzero inputs, the four events are mutually exclusive; consequently the remaining matrix is precisely the Boolean signed-relation kernel on abscissae, up to invertible orbit-weight scaling. Its rank is therefore at least
\[
(q-3)/2.
\]

**Complete-work verdict.** The specified exact feature contraction needs \(\Omega(q)\) separated terms over characteristic zero. Explicitly evaluating and aggregating them already exceeds square-root work, before recovery. This also applies over splitting fields of odd characteristic different from \(q\), by the corresponding root-of-unity argument.

**Scope.** This rejects a uniformly exact low-rank count decomposition. It does **not** reject input-adaptive decompositions, randomized existence-only detectors, or every implicit tensor method. I found no new applicable prior-art theorem to import; the displayed rank calculation is an independent paper derivation requiring review.

A concrete randomized variant also fails its advertised precision. Even granting free scalar characters, estimate an unsigned count using sampled Fourier modes. For three iid length-\(n\) lists, let
\[
Y_t=\Big(\sum_i\omega^{ta_i}\Big)
    \Big(\sum_j\omega^{tb_j}\Big)
    \Big(\sum_k\omega^{tc_k}\Big).
\]
Include the zero mode exactly and sample \(r\) nonzero modes independently. The count estimator’s mean-square error, averaged over lists and sampling, is
\[
\frac{n^3(q-2)}{qr}.
\]
At \(n^3\asymp q\), constant absolute RMS accuracy requires \(r=\Omega(n^3)\). This falsifies that estimator’s cheap accurate-count claim; variance alone is not a lower bound for every possible decision rule. Moreover, evaluating characters of target-dependent points is itself an unsupported, paid operation.

**2. Elliptic divisor products: genuine detection, but translation-grid evaluation remains quadratic**

**Operation.** For signed known-label points \(A_1,\ldots,A_n\), set \(S_A=\sum_iA_i\). Construct a Miller-style rational function with divisor
\[
\operatorname{div}(f_A)=
\sum_i[A_i]-[S_A]-(n-1)[O].
\]
Now form, implicitly,
\[
F_{A,B}(T)=\prod_{j=1}^{n}f_A(T-B_j).
\]
Away from its poles,
\[
F_{A,B}(-C_k)=0
\]
exactly detects an unsigned triple \(A_i+B_j+C_k=O\). Signs can be covered by signed lists.

Pole locations are \(B_j\) and \(S_A+B_j\), only \(O(n)\) indexed points. Check the queried \(C_k\) against this support and handle or reject exceptions explicitly. Once a zero \(C_k\) is found, scanning \(B_j\) and testing \(-C_k-B_j\) in an \(A\)-dictionary recovers the labels in \(O(n)\) additional group work.

**Hoped-for gain.** Miller functions can have compact straight-line representations. Perhaps a product of translated functions could be evaluated on all \(C_k\) without producing the \(n^2\) translated arguments or pair sums.

**Unsupported assumption.** A compact divisor description or circuit must support that aggregate evaluation in \(o(n^{3/2})\) complete work. Compact representation alone does not supply it. Miller explicitly distinguishes straight-line representation from expanded rational-function representation. [Miller’s primary source page](https://crypto.stanford.edu/miller/)

**Complete-work screen.** A concrete streamed implementation processes one \(B_j\) at a time, forms the \(n\) points \(-C_k-B_j\), evaluates \(f_A\), and updates the products. It performs \(n^2\) translated-point operations even if function evaluation is granted free. Memory can remain near-linear; work cannot.

Expansion instead creates a function with up to \(n^2\) indexed zeros. Charging that expansion also misses the gate. These are implementation screens, not a degree-based runtime impossibility.

**Cheapest decisive next analysis.** Require an explicit translation-product circuit and count its operations when evaluated jointly on the \(n\) query points. If it makes one call per \((B_j,C_k)\), it is rejected on paper. I found no sourced aggregate evaluator that avoids this. This is a different representation from H017’s polynomial product/gcd, but presently offers no better detector.

**3. Structured norm modulo the third-list polynomial: output truncation does not yet remove the pair dimension**

**Operation.** Let \(A(X),B(Y),C(Z)\) be the square-free list polynomials and \(S_3\) the summation polynomial. Compute
\[
N(Z)=
\operatorname{Norm}_{\mathbb F_p[X,Y]/(A,B)}
       \big(S_3(X,Y,Z)\big)\pmod {C(Z)}.
\]
Then \(\gcd(N,C)\) identifies third-list coordinates participating in a relation. For an identified \(z\), scanning one list and solving the constant-degree equation \(S_3(x,Y,z)=0\), followed by dictionary lookup, recovers a pair in \(\widetilde O(n)\) work.

**Hoped-for gain.** Only a degree-\(<n\) residue is requested. A structured determinant or norm algorithm might compute it directly, avoiding the degree-\(O(n^2)\) full norm and the dense triple algebra.

**Concrete attempted implementation.** First eliminate \(Y\):
\[
R(X,Z)=\operatorname{Res}_Y(B(Y),S_3(X,Y,Z)).
\]
Since \(S_3\) has degree at most two separately in \(X,Z\), \(R\) has degree at most \(2n\) in each. Reduce modulo \(A(X),C(Z)\), then take the remaining norm in \(X\).

A literal dense intermediate allocates \(n^2\) coefficients. Likewise, a conventional multiplication operator for the first quotient has dimension \(n^2\). Either implementation exceeds the \(o(n^{3/2})\) gate before extraction.

**Prior-art check.** Fast multivariate multipoint evaluation takes a coefficient vector and explicit evaluation points; it does not directly promise existential zero detection over an implicit Cartesian product. [Bhargava–Ghosh–Guo–Kumar–Umans, Theorem 1.1](https://arxiv.org/pdf/2205.00342)

Quasi-linear generic bivariate-resultant algorithms are relevant background, but their size parameter and generic-position requirements must be mapped to the actual elimination problem. I found no theorem yielding the requested truncated norm below the pair dimension. [van der Hoeven–Lecerf](https://www.texmacs.org/joris/resultant/resultant.pdf)

**Verdict and falsifier.** The two-stage dense implementation is rejected. The changed operator—computing the norm *directly modulo \(C\)*—remains an explicit unresolved computational problem, not an algorithm. The cheapest source-level falsifier is to instantiate an alleged theorem with the precise intermediate dimensions, input format, genericity conditions, and recovery cost. Merely citing near-linear modular composition is insufficient.

This deliberately reopens only a specified truncated operation within the already screened norm/product family; it is not a new positive candidate.

**4. Shared pair tables across targets: real amortization, already matched by fixed-base BSGS**

**Operation.** Precompute
\[
A_i=a_iG,\quad B_j=b_jG,\quad
D_{ij}=A_i+B_j,
\]
retaining \(a_i+b_j\). For target \(Q_t\), query points \(Q_t+c_kG\). A table match gives
\[
k_t=a_i+b_j-c_k\bmod q.
\]
This has a nonzero target coefficient and explicit verification.

If the table contains \(m\le n^2\) distinct points, independent uniform queries hit with probability \(m/q\). Constant-success recovery needs \(\Theta(q/m)\) expected queries per target.

**Hoped-for gain.** At \(n\asymp q^{1/3}\), charge \(q^{2/3}\) setup once and roughly \(q^{1/3}\) queries per target:
\[
W_{\rm pair}(T)=\widetilde O(q^{2/3}+Tq^{1/3}),
\]
with \(q^{2/3}\) stored labelled entries. Per-target cost can beat square root after sufficient reuse.

**Paper falsifier against the matched baseline.** Standard fixed-base BSGS with \(m\) baby steps already gives
\[
W_{\rm BSGS}(T;m)=\widetilde O(m+Tq/m),
\qquad M=\widetilde O(m).
\]
Choosing \(m=n^2\) matches the pair-table expression, while arithmetic-progression giant steps provide full-range coverage. Optimizing \(m\), where feasible, gives the familiar \(\widetilde O(\sqrt{Tq})\) tradeoff. The pair table has supplied no superior exponent, storage tradeoff, or established constant saving. The underlying BSGS construction is documented in [Galbraith’s primary lecture](https://www.math.auckland.ac.nz/~sgal018/ecc2015.pdf).

Random scalar generation, scalar multiplications, duplicate pair sums, failed queries, lookup, and verification further burden the pair-table implementation. This comparison already charges BSGS setup; it does not compare amortized work against a fresh single-target rho run.

If the first two lists contain target-dependent coefficients, their reuse across different targets needs a new construction. Rebuilding them cannot be credited as shared setup.

**Recommendation to root.** Retain the exact signed-kernel rank screen and the batching comparison as paper-only negative findings, subject to independent review. Do not admit an experiment for these four constructions. The unresolved operations worth a future source-level check are aggregate elliptic translation-product evaluation and direct truncated norm computation; neither currently has a credible sub-\(n^{3/2}\) implementation.

The current SP3 hypothesis still has constant-probability iid witnesses near \(n=q^{1/3}\), but no sufficiently cheap detector. These calculations narrow particular detector designs without establishing coordinate-aware impossibility or changing the square-root reference.
