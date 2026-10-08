Root caution: unverified proposer report. No experiment ran. Several geometric,
inversion-cost, pole-support and universal-exclusion statements are incorrect or
unsupported; do not adopt its proposed falsifiers or negative claims wholesale.

The hybrid lens does not produce a full-work improvement. Two procedures are worth writing down because their gain, if any, sits in a gap the older cards do not already name; everything else in this pass rebalances at the negation-rho baseline or repeats a registered object.

Baseline, unchanged: one full scalar on an ordinary prime-field curve of prime order \(q\neq p\), only the negation automorphism. Negation-rho is about \(\sqrt{\pi q/2}/\sqrt{2}\) group operations. Shoup’s generic bound does not apply to coordinate algorithms. Verified improvement: **NONE**. No experiment was run.

## Card 1 — Parallel-chord witness, solved as a degree-4 residual

**Procedure.** Fix the public curve \(y^2=x^3+Ax+B\) and base \(G\). A walk point is stored as usual: \(R_i=[a_i]G+[b_i]Q\) with known coefficients. The first mathematical object is not the point set; it is the affine slope
\[
\lambda(R,S)=\frac{y(S)-y(R)}{x(S)-x(R)}\in\mathbb F_p
\]
together with the intercept \(\mu=y(R)-\lambda x(R)\). A collision is a pair of chords with the same \(\lambda\) and different intercepts. Each chord meets \(E\) in a third point because
\[
f(x)-(\lambda x+\mu)^2=0
\]
is a cubic; the third root is \(-\,x(R)-x(S)+\lambda^2\), and the three points sum to \(\mathcal O\). Given two parallel chords on four walk points, form the two cubic residuals, solve each cubic (degree 4 after clearing the shared \(\lambda\), one resultant in the intercept difference), and read candidate scalars from the known coefficient vectors of any triple that sums to \(\mathcal O\). Verify by one scalar multiplication.

**Where a gain could come from.** Slope image size is \(\Theta(p)\), so a slope birthday is the same order as a point birthday. The only saving is if one slope collision yields a constant-size list of scalars before any point collision, and if checking the residual cubic is cheaper than storing full points. That would improve the leading constant of negation-rho, not the exponent, and only if false parallel chords are rarer than \(\pm\)-collisions by a fixed factor.

**Predicted cost.** Same exponent as negation-rho. At \(T\) samples the number of parallel chord pairs is \(\asymp T^2/p\asymp T^2/q\). Each pair produces \(O(1)\) candidate triples. This matches the point-collision count up to a small constant and does not beat \(\sqrt{\pi q/2}/\sqrt{2}\).

**Setup, memory, restarts.** No curve preprocessing. Memory is the walk table of coefficients plus one field element \(\lambda\) (the intercept is recomputed). Restarts are the usual rho restarts when the walk cycles without a verified scalar. Failed residual cubics are charged: each collision, true or false, costs a constant number of field operations and one verification scalar multiplication when the cubic splits.

**Unsupported assumption.** That a shared affine slope on two chords imposes a scalar relation tighter than “each triple sums to \(\mathcal O\)”. On the Weierstrass model every non-vertical line already meets infinity at \(\mathcal O\), so parallelism is not an extra group relation.

**Prior art.** The chord-residual cubic is the group law. Equal-slope detection is a coarser filter than the negation quotient of Bernstein–Lange–Schwabe (ePrint 2011/003). It is not signed BSGS and not a Semaev factor base.

**Falsifier, not run.** On one prime-order curve with \(q\approx 2^{16}\), sample \(T=2^{10}\) walk points and count pairs with equal \(\lambda\) but \(\{R,S\}\neq\{\pm R',\pm S'\}\). If that count is already \(\ge c\,T^2/q\) for a small \(c\) (parallel chords as common as point collisions), the constant cannot improve. If the count is \(o(T^2/q)\), the constant question stays open and still has no exponent claim.

## Card 2 — Order-2 state meet-in-the-middle, jumped by the translation matrix on a fixed window

**Procedure.** Let \(u_n=x([n]G)\). Differential addition gives an explicit rational map
\[
\Phi\colon (u_n,u_{n+1})\mapsto (u_{n+1},u_{n+2})
\]
depending only on \(A,B,x(G),y(G)\), not on \(n\). The state space is the orbit of \((x(G),x([2]G))\) under \(\Phi\), length \(q\) up to the sign \(u_n=u_{q-n}\). The algorithm is baby-step/giant-step on this state: babies are \(\Phi^j(x(G),x([2]G))\) for \(j<m\); giants walk backward from \((x(Q),x(Q+G))\) by the inverse branch of \(\Phi\) that stays on \(\langle G\rangle\). A match \(j+im\equiv \pm k\pmod q\) is the scalar. The inverse branch is the unique rational root of the degree-4 preimage of doubling along the chord, selected by lying in \(\langle G\rangle\), which is free once the point is known because \([2]\) is bijective on a prime-order group.

**Where a gain could come from.** Only from making one application of \(\Phi\) or \(\Phi^{-1}\) asymptotically cheaper than one elliptic addition, or from jumping \(\Phi^{q^{\theta}}\) faster than repeated addition. The forward group law is already \(O(\log q)\) doublings per long jump. A holonomic or matrix closed form for \(\prod_{i<N}\mathrm D\Phi(i)\) does not invert the index; Bostan–Gaudry–Schost evaluates a polynomial-coefficient recurrence’s \(N\)th term in \(\tilde O(\sqrt N)\), which ties square-root and does not beat it.

**Predicted cost.** \(m=q/m\) gives \(2\sqrt q\) state steps, each one addition or one rational evaluation of the same degree as addition, times two for the sign. Exponent \(1/2\), leading constant no better than negation-aware BSGS, and worse than negation-rho on memory.

**Setup, memory, restarts.** No preprocessing beyond \(x(G),x([2]G),x(Q),x(Q+G))\). Memory \(m\) states if the baby list is stored; rho-style distinguished states on the same orbit use \(O(1)\) memory and return to Card-free negation-rho. No restarts beyond the usual collision failure. The degree-4 preimage contributes \(O(1)\) field operations per backward step, not a new search tree: over \(\mathbb F_p\) the subgroup half is unique.

**Unsupported assumption.** That the state \((u_n,u_{n+1})\) has a computable quotient, of size \(q^{1-\varepsilon}\), on which \(\Phi\) still acts and from which the index lifts by a polynomial equation. Prime order forbids a group quotient. A non-homomorphic quotient (a rational function of the pair) has fibers of size \(O(1)\) if it separates indices, which returns the birthday to \(\sqrt q\), or large fibers whose membership equation is another DLP.

**Prior art.** Differential addition is Montgomery’s ladder identity. Orbit BSGS on \((x(nG),x((n+1)G))\) is ordinary BSGS in a redundant encoding. Hess–Shparlinski and Mérai–Winterhof (Des. Codes Cryptogr. 81, 2016; arXiv:1509.06909) give large linear complexity for \(f(nG)\) when \(f\) is rational; the zero-count below extends that to every fixed \(f\in\mathbb F_p(E)\). This card is the nonlinear order-2 recurrence those theorems do not literally quote, and it still does not move the exponent.

**Falsifier, not run.** Symbolic, not numeric. Write \(\Phi\) from the curve equation and the chord through \(G\). Confirm the backward step is a degree-4 polynomial with exactly one root in the subgroup for a generic state (the root is \(x([n]G)\) when the state is \((x([n+1]G),x([n+2]G))\)). If that identity holds, there is no branching to search and the cost is BSGS. A second root in \(\langle G\rangle\) on a positive-density set of states would be the only opening, and it would contradict bijectivity of \([2]\).

## Rejected in this pass

These were costed and dropped. They are not open cards.

**Fixed rational statistics along the orbit.** For any non-constant \(f\in\mathbb F_p(E)\), the translates \(f\circ\tau_G^i\) have poles at distinct points \(-iG\). A constant-coefficient relation \(\sum_{i\le L}c_i f([n+i]G)=0\) on a long window produces a function with more zeros than its pole degree unless every \(c_i=0\). Hence the linear complexity profile of \(n\mapsto f([n]G)\) is \(\Omega(N/\deg f)\) on windows of length \(N\le q\). Berlekamp–Massey, Prony, and matrix pencils on slopes, Miller ratios, or \(x+x\circ[2]\) cannot beat square-root. Polynomial-in-\(n\) coefficients escape that pole argument, but a recurrence of order \(L\) and coefficient degree \(d\) with \(L(d+1)<\sqrt q\), run backward by baby-step/giant-step, is again one \(O(1)\) state update per index step. The group law is already an \(O(\log q)\) forward map. A hidden forward recurrence does not invert faster than BSGS.

**Complete-intersection witnesses.** Six points of \(E\) on a conic sum to \(\mathcal O\), so their coefficient vectors give \(k\) from one linear equation, checked by a \(6\times 6\) determinant on \((1,x,y,x^2,xy,y^2)\). Listing triples to collide \(R_1+R_2+R_3=-(R_4+R_5+R_6)\) costs \(T^3\) additions and needs \(T^3\asymp\sqrt q\). The same balance holds for a degree-\(d\) plane curve through \(3d\) walk points: half-sum listing is \(\sqrt q\). Reuse does not help, because one such relation already determines \(k\); the cost is finding the first one. This is why factor-base methods need point reuse across many relations, which is the registered index-calculus ledger, not a new witness.

**Prime-order quotients, halvings, and intertwining maps.** A group homomorphism cannot shrink \(\langle G\rangle\). The x-duplication map is degree 4, but \([2]\) is bijective on the subgroup, so the rational preimage tree does not branch. Geometric BSGS (babies \([r^j]G\), giants multiplication by \(r^{-m}\)) replaces an \(O(1)\) giant addition by an \(O(\log q)\) scalar multiplication. An intertwiner \(\varphi(P+Q)=\varphi(P)+G\) is multiplication by \(k^{-1}\) up to translation, hence has degree \(k^2\), not a bounded degree. Ritt commutation of Lattès maps was already closed in the constraint pool; this is the translation form of the same degree count.

**Information-theoretic sketch collisions.** A computable sketch \(\psi\) with image smaller than \(\Theta(q)\) has fibers larger than \(O(1)\). On a prime-order group those fibers are not cosets. A collision of \(\psi\) on stored walk points does not yield a polynomial equation in \(k\) of degree \(o(q)\); the points themselves are already known. Upgrading the collision requires the fiber equation, which is another discrete log unless the fiber is the negation pair.

**Formal logarithms in either characteristic.** In characteristic \(p\) the formal logarithm is inseparable (\(p\) kills the invariant differential’s integral), so equal-characteristic Laurent series at a rational point do not recover the scalar. Mixed-characteristic sections are the registered p-adic lane and were not reopened. Full-group power sums of \(x([j]Q)\) are independent of \(k\) because multiplication by \(k\) merely permutes \(\langle G\rangle\). Partial orbit power sums are the already-registered vanishing-circuit request.

**Index-calculus ledger, restated so it is not reopened by accident.** A free 2-sum decomposition oracle still costs \(q/X+X^2\), minimized at \(q^{2/3}\). A free 3-sum oracle ties \(\sqrt q\). The \(m=4\) cell \(q^{2/5}\) needs a real existence tester of cost \(X^{\tau}\) with \(\tau<1/2\) at \(X=q^{1/5}\), which is the registered open cell (naive Semaev, PKM, the length-\(\le 5\) univariate grammar, Gröbner bounds of Yokoyama–Yasuda–Takahashi–Kogure). Evaluating \(S_5\) on one explicit tuple is \(O(1)\) and does not decide existence. Pair-sum hash tables cost \(X^2=q^{2/5}\) to build and \(X^2\) per target scan. No new tester is supplied here.

**Covers, pairings, class groups, and Kani-type extraction.** A double cover \(C\to E\) embeds the subgroup in a genus-2 Jacobian whose index calculus costs \(\tilde O(p)\) for the full group, worse than \(\sqrt q\) on the subgroup. Weil pairing on \(E(\mathbb F_p)\) is alternating and hence trivial on a cyclic group; the embedding degree of a prime \(q\approx p\) is not a feasible MOV field. Imaginary-quadratic units are finite and already in the automorphism baseline. Walking the \(\ell\)-isogeny volcano stays inside an isogeny class of equally hard curves; hitting a weak curve is special-curve transfer. Castryck–Decru / Kani needs images of an auxiliary torsion basis under a secret smooth-degree isogeny; multiplication-by-\(k\) publishes neither. The graph of \([k]\) in \(E\times E\) is the marked-surface card, and no compact extraction is given here. Square-root Vélu on \(\langle G\rangle\) quotients by a subgroup that does not depend on \(k\).

**Also dropped as already closed or immediately losing.** Signed and grumpy-giant BSGS, batch inversion, Edwards/Hessian models (no rational 2-torsion or 3-torsion), Xedni lifts, integer EDS reduction modulo \(\ell\neq p\) (the lifted point does not lie on the reduced curve), Wagner prefix merges (no local digit law in a prime field), low-weight and double-base subset sums (they rebalance at \(\sqrt q\) once the necessary number of summands is included), walk-trace decoding of slope characters (fixed-degree characters fall under the Kohel–Shparlinski bound already used on interval predicates), and Freiman/FFT 3-sum speedups (an explicit isomorphism to \((\mathbb Z,+)\) preserving elliptic addition is the discrete log).

## Wave note

Best supported full work remains negation-rho as above. Verified improvement: **NONE**. No hypothesis in this pass is under test as a claimed improvement. The two cards are conditional constant or encoding variants; both are predicted to tie the square-root exponent once the stated assumption is granted in its likely form. Evidence against a gain is the symbolic ledger above, not a measurement. The conclusion-changing check, if either card is kept, is the Card 1 slope-collision count or the Card 2 degree-4 branch count, each on one synthetic prime-order curve, with group operations charged against negation-rho. Neither check is an asymptotic proof.
