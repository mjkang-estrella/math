# H017 hybrid mechanisms: raw Grok report

Unverified initial output. Mathematical lower bounds, probability assumptions, operation constants and source claims below require independent review; none is accepted as a measured complete-work result.

No complete-work improvement over negation-aware rho. Four mechanisms in the hybrid, collision-geometry, and reusable-preprocessing lane were specified and costed. Each ledger lands on the classical square-root reference. Verified improvement remains **NONE**.

Working reference: one full scalar on an ordinary prime-field prime-order curve, about \(\sqrt{\pi q/4}\) group additions, with preprocessing, memory, failures, and verification charged separately. Single-target time is not an amortized multi-target time.

## 1. Algebraic orbit folding beyond negation

**Paid operation.** Fix a rational function \(f\) on \(E\) of bounded degree (slope to \(G\), tangent slope, \(x(P)+x(P+G)\), and the same constructions with a short translate). For each walk point, compute the other rational roots of \(f(R)=f(P)\), pick a canonical representative, and continue a negation-style walk on representatives.

**Recovery.** A collision of representatives solves \(k\) only when every rational fiber mate used in the label update is an affine map \(R=[n]P+[m]G\) with \(n,m\) known from the branch, and the resulting coefficient of \(k\) is nonzero.

**Expected gain.** None. Negation (and the conjugate involutions \(P\mapsto -P+T\)) already gives the factor \(\sqrt{2}\). Any two distinct involutions of that form compose to a translation, and the translation orbit is the whole prime-order group, so they cannot be used together. A mate that is not a morphism does not update \((a,b)\). A mate that agrees with one fixed \([n]P+[m]G\) on a positive-density set would be that morphism. A nonzero function of degree \(O(n^2)\) has \(O(n^2)\) rational zeroes, so each bounded pair \((n,m)\) accounts for \(O(n^2)\) points. Pairs with \(|n|,|m|\le N\) cover \(O(N^4)\) points. Covering the group forces \(N=\Omega(q^{1/4})\) and \(\Omega(q^{1/2})\) candidate branches.

**Prior art.** This is the label obstruction in the equal-tangent and opposite-slope correspondences, made quantitative. It is not an automorphism speedup (Wiener–Zuccherato, Gallant–Lambert–Vanstone, Bernstein–Lange–Schwabe). Those stop at \(\mathrm{Aut}=\{\pm1\}\).

**Assumption that would reopen it.** A branch rule of cost \(o(N)\) whose successful \((n,m)\) are not a positive-density set of zeroes of one fixed morphism, and whose label update is still affine with nonzero coefficient of \(k\).

**Setup, memory, full work.** No table. Each step pays the fiber (a constant number of field operations and a square root) plus a rho step. Square roots already exceed the \(\sqrt{2}\) step budget before the branch count is included.

**Cheapest falsifier.** Already closed for fixed branches by the degree count. A proposed explicit branch is killed by one counterexample on the recorded \(p=59\), \(q=67\) curve, or by showing it is not affine.

## 2. Implicit pair-sum dictionary

**Paid operation.** Build a base \(F\) of \(B\) known-log points and the list (or polynomial \(H_2\)) of abscissae of pairwise sums. Size \(U\le B^2\). A translate \(R=Q+[u]G\) is kept when it is \(\pm(A+C)\) for two entries of that list. Parenthesized, that is a four-point decomposition. Test a translate by the degree-2 summation slice in one variable and a half-gcd against \(H_2\).

**Recovery.** Labels on the four base points are known. One relation \(\sum\varepsilon_i(a_i+b_i k)=t\) with nonzero \(\sum b_i\) gives \(k\). Verify \(kG=Q\). Constructed pairs are discarded.

**Success probability and work.** About \(\min(1,U^2/q)\) of translates decompose if sums behave uniformly. Empty translates dominate while \(U^2\ll q\). Writing \(H_2\) costs \(\Theta(U)\) group additions. An exact query that is correct for every dictionary must touch \(\Theta(U)\) coefficients; half-gcd is soft-\(O(U)\) field work, not \(o(U)\). Ledger:
\[
U+\frac{q}{U}.
\]
The minimum is \(2\sqrt{q}\) at \(U=\sqrt{q}\). That ties signed meet-in-the-middle and loses the rho constant. Log factors in the half-gcd sit on the wrong side of the ledger.

**Prior art.** Semaev summation polynomials, Petit–Kosters–Messeng, and the Yokoyama–Yasuda–Takahashi–Kogure bounds already put naive prime-field index calculus at or above generic square-root cost. Bernstein–Lange preprocessing has the same \(M+q/M\) shape. This is the natural implicit resultant left open after the explicit-expansion rejection, restricted to this parenthesis and this query. It is not a claim about every unexpanded circuit.

**Assumption that would reopen it.** An exact query whose field cost is \(U^\alpha\) for a uniform \(\alpha<1\), after setup \(U\), on empty translates. Then any \(\beta\) strictly between \(1/(2(2-\alpha))\) and \(1/2\), with \(U=q^\beta\), has total exponent \(\max(\beta,\,1-2\beta+\alpha\beta)<1/2\). Generic Euclidean degree drop is 1, so \(\alpha=1\) and the interval for \(\beta\) is empty.

**Setup and memory.** \(\Theta(U)\) sums stored. Failed translates and the final scalar check are paid. Single-target: setup is not amortized away.

**Cheapest falsifier.** On one synthetic curve with \(B\le 2^8\), the subresultant sequence for random empty translates must have mean length \(o(\deg H_2)\). Length \(\sim\deg\) kills the only exponent opening. No large run is required to reject the soft-\(O(U)\) exact query.

## 3. Growing-anchor fiber search

**Paid operation.** Choose \(L\) generic known-log anchors \([r_j]G\), not a short interval. Seed a line through one anchor, take the residual quadratic fiber, and continue through frontier points exactly as in a two-color fiber walk. A closure that leaves only anchor columns, with nonzero denominator, solves \(k\). Lines through two anchors are discarded: their third point is \(-(A+B)\) and the coefficient of \(k\) is 0.

**Expected gain.** None for this selector. A new row run through one frontier point meets the anchor set with probability \(\Theta(L/q)\). The frontier identity needs at least one such accidental anchor incidence before \(F\) can fall, so the row count is \(\Omega(q/L)\). Anchor setup is \(O(L\log q)\) scalar multiplications. If one row costs \(\kappa\) rho-steps (\(\kappa\ge 1\): a slope, a quadratic, and a square root),
\[
\kappa\frac{q}{L}+L\log q\ge 2\sqrt{\kappa\, q\log q}.
\]
The \(3^L N\) secret-count does not become an algorithm once \(L=O(\log q)\). An arithmetic-progression anchor set collapses further: \(\sum\varepsilon_j j\) with \(\varepsilon_j\in\{-1,0,1\}\) takes only \(O(L^2)\) values, not \(3^L\).

**Prior art.** Same relation and frontier identities as the few-anchor fiber screen. The new piece is the uniform hit-time of a growing generic anchor pool, which that screen deliberately left open. It is not Semaev index calculus and not labelled restart seeding.

**Assumption that would reopen it.** A paid rule that forces a non-constructed anchor incidence with probability \(\omega(L/q)\) per row, without spending \(\Omega(q/L)\) rows, and whose kept relations still have a nonzero coefficient of \(k\).

**Setup, memory, full work.** Memory \(O(L)\) anchors plus the live frontier. Failed components are paid. Retrying slopes on the same anchor set does not enlarge the recoverable set.

**Cheapest falsifier.** The \(\Omega(q/L)\) bound is combinatorial given uniform accidental hits. A proposed selector must state a hit probability and a row cost; if their product is at least \(\sqrt{q}\), stop. A finite check is only needed if the selector claims a biased hit rate.

## 4. Second channel by duplication, and collinear triples

**Paid operation.** Run a competent negation-aware \(r\)-adding walk. On every step, also evaluate the duplication map on the canonical \(x\)-coordinate and look it up in the stored walk abscissae. A hit \([2]P_i=\pm P_j\) gives
\[
(2b_i\mp b_j)k=\pm a_j-2a_i,
\]
nonzero with probability \(1-O(1/q)\). Separately, the classical collinear-triple collector: \(t\) labelled walk points, hash \(P_i+P_j\), and test the third point. One triple \(P_i+P_j+P_k=O\) with \(b_i+b_j+b_k\ne 0\) solves \(k\).

**Expected gain.** None on either schedule.

- Duplication is a second useful relation type, so the step count falls by about \(\sqrt{2}\). It is not free: the third point of the chord is \(-P_{\mathrm{next}}\), already identified by negation. A separate duplication costs about one full step (amortized batched affine addition is \(5M+1S\) per step in the large-batch limit; duplication is another slope and a division of the same order). Work multiplier about \(\sqrt{2}>1\). A net win needs the extra map to cost at most \(\sqrt{2}-1\approx 0.414\) of a batched step.
- Collinear triples among \(s\) uniform points occur at rate \(\sim s^3/q\). One expected triple at \(s\sim q^{1/3}\). The uniform reporter (hash every pair, or sort slopes from each origin) is \(\Theta(s^2)=q^{2/3}\) group operations. Subsampling origins does not help: \(m\) origins at cost \(ms\), hit probability \(\Theta(m/s)\), repetitions \(s/m\), product \(\Theta(s^2)\).

**Prior art.** Negation channels are Bernstein–Lange–Schwabe, not a new automorphism. Pair hashing of labelled points is the ordinary 3-sum reporter already compared with rho. Aronov–Ezra–Sharir, about \(s^{24/13}\) orientation tests when all three sets lie on a fixed curve, gives exponent \(8/13\approx 0.615\) if those tests were free field operations. They are not, and \(8/13>1/2\). Alman–et al. (arXiv:2610.06783, 2026) make integer 3SUM truly subquadratic and state explicitly that collinearity detection does not follow: the reductions run the wrong way. Importing that 3SUM algorithm as an ECDLP algorithm is incorrect.

**Assumption that would reopen it.** Either a division-free duplication whose complete batched cost is \(\le 0.414\) of one BLS step, with the new hits not concentrated on the negation class, or a uniform collinear reporter of exponent \(\alpha<3/2\) on \(s\) points (so \(s\sim q^{1/3}\) costs \(q^{\alpha/3}<q^{1/2}\)).

**Setup and memory.** Duplication channel: the ordinary distinguished-point store, plus one extra lookup per step. Triples: \(O(s)\) points and a hash table. Both are single-target.

**Cheapest falsifier.** For duplication, a multiplication/squaring/inversion count of the proposed map against \(5M+1S\); no curve search. For triples, the exponent of the proposed uniform reporter; if it is \(\ge 3/2\), the \(q^{2/3}\) ledger stands. A decision-tree sign-test bound is not that exponent.

## What was not reopened

Repaired H015 modules were not resubmitted. The compensated arithmetic-progression divisor exists, and evaluating it on an interval of length \(B\) costs \(\Theta(B)\), which does not beat an explicit baby list. The degree-4 summation polynomial, once the missing \(X^2Y^2\) term is restored, still does not put a positive-yield factor base below the meet-in-the-middle size inside the Coppersmith range. Signed slopes, sliding-window report minima, labelled restart bursts, and mixed-modulus character features stay closed.

| Mechanism | Derived complete work | Against \(\sqrt{\pi q/4}\) |
|---|---|---|
| Bounded algebraic fiber canonicalization | At least negation rho, and only with an affine branch that covers \(O(N^4)\) points | No gain |
| Implicit four-point dictionary | \(U+q/U\ge 2\sqrt{q}\) while queries read \(U\) | No gain |
| Generic-anchor fiber BFS | \(\ge 2\sqrt{\kappa q\log q}\), \(\kappa\ge 1\) | No gain |
| Duplication side lookup | About \(\sqrt{2}\) times a rho step | No gain |
| Uniform collinear triples | \(q^{2/3}\) | No gain |
