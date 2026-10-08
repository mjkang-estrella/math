# H013 hybrid operations — raw Grok report, unaccepted claims

2026-10-08. Original Grok4.7 task completed. Contains heuristic costs and
overbroad mathematical/rejection assertions; independent root disposition pending.
No numerical run, validated improvement or accepted universal exclusion.

Verified gain remains **none**. Negation-aware rho, about \(\sqrt{\pi q/4}\) group additions, is still the reference. The three mechanisms below are speculative, labeled by construction, and aimed at that baseline. None repeats equal-tangent associates, an unspecified Hensel selector, or iid bin-plus-short-progression testing.

Scope for every card: ordinary \(E/\mathbb{F}_p: y^2=x^3+Ax+C\), \(\#E(\mathbb{F}_p)=q\) prime, \(q\neq p\), \(q\approx p\), \(\gcd(q,p-1)=1\), \(\mathrm{Aut}=\{\pm1\}\), full unknown \(k\) with public \(T=[k]G\). Preprocessing, memory, abandoned walks, verification, and rank are charged. No secret interval, no hidden oracle, no special-curve transfer.

A constraint these cards are built around: any single-valued step that emits \(s\) group elements at \(\ge 1\) addition each, then picks one, has image at least \(q/s\) and costs at least \(\sqrt{s}\) more than it saves against a random map. Extra images beat negation-rho only if they are cheaper than about \(0.414\) additions (the \(\sqrt{2}\) budget) or the dynamics are not a random map on a domain of size \(\ge q/2\). Rational maps \(E\to E\) are only \([n]+\)translation. Invertible \(n\) is a relabeling of the same discrete log. That is why an affine branch law is not, by itself, an exponent improvement.

## Card 1 — Running-sum shepherd

**Operation.** Fix a public jump table of size \(r=16\), with \(J_h=u_h G+v_h T\) and \((u_h,v_h)\in\{\pm1,\pm2\}^2\setminus\{(0,0)\}\), computed once by additions. Labels of the \(J_h\) are the coefficient pairs themselves.

State is a pair of labeled points \((P,\Sigma)\), keys negation-canonical (lexicographically smaller of \(y\) and \(-y\)).

- Start: \(\Sigma\leftarrow G\) with label \((1,0)\), \(P\leftarrow T\) with label \((0,1)\). Insert both.
- Each step, with current labels \((a,b)\) and \((a_\Sigma,b_\Sigma)\):
  1. \(U\leftarrow\mathrm{canon}(P+J_{H(x(P))})\). One addition. Label \((\pm(a+u),\pm(b+v))\).
  2. \(W\leftarrow\Sigma-P\), then \(V\leftarrow\mathrm{canon}(\Sigma+W)\). Two additions. Label of \(V\) is \(\pm(2a_\Sigma-a,\ 2b_\Sigma-b)\).
  3. Replace \(P\) by whichever of \(U,V\) has the smaller canonical key.
  4. \(\Sigma\leftarrow\mathrm{canon}(\Sigma+P)\). One addition. Add the labels, then apply the canon sign.
  5. Look up \(P\). On a hit with label \((a',b')\) and \(b'\neq b\),
     \[
     k\equiv (a-a')(b'-b)^{-1}\pmod q.
     \]
     Verify \([k]G=T\). Equal-\(b\) hits are paid failures. A repeated state \((P,\Sigma)\) with the same labels is a fruitless cycle: abandon the walk and restart from \(P\leftarrow T+[\rho]G\), \(\Sigma\leftarrow G+[\rho']G\) with fresh public \(\rho,\rho'\). Every abandoned addition is charged.

**Why this is not the killed H010 pattern.** Every stored point is produced by the group law from \(G\) and \(T\), so the label is an explicit affine pair. There is no quartic fiber, no \(p^2\) digit, and no bin test of a short progression. The second candidate \(V=2\Sigma-P\) is a reflection in the running sum, not an unidentified associate.

**Gain against negation-rho.** Four additions per step, against one addition and domain \(q/2\) for competent negation-rho (\(t_0=\sqrt{\pi q/4}\)). A random map on a domain of size \(q/2\) would need about \(t_0\) steps and therefore about \(4t_0\) additions here: a loss by about \(4\). An exponent or a material constant appears only if the running-sum coupling makes the first useful collision arrive in \(t<t_0/4\) steps. Memory is one record per step until collision, or the usual distinguished-point thinning if a later variant stores only a fraction \(\theta\); thinning does not reduce the addition count below the number of points actually computed. No rank or training. Verification is one scalar multiplication, negligible beside a long walk. Restarts are inside the ledger, not a separate free budget.

**Prior art.** Negation-rho and fruitless-cycle handling are Bernstein–Lange, ePrint 2011/003, and Wiener–Zuccherato. The \(r\)-adding skeleton is Teske. Local greedy descent to a stored endpoint was the H012 LD8 schedule, which kept \(B\) fixed and was bounded by \(\Omega(\sqrt{q\log q})\) for that frozen neighborhood. This walk never stops at a basin minimum: \(\Sigma\) is an accumulating labeled point, the alternative step is reflection in \(\Sigma\), and \(b\) changes because the jump table contains \(T\).

**Unsupported assumption.** For every ordinary curve in scope, the mean addition count to a \(b\)-changing collision, including restarts, is \(<t_0\).

**Cheapest falsifier.** One ordinary curve with \(q\approx 2^{16}\), thirty random targets, cap \(8t_0\) additions, count only group additions. Kill the uniform saving if the median shepherd count is \(\ge t_0\). One curve kills a uniform factor. It does not by itself prove an asymptotic loss on every larger curve. Do not read a small-curve ratio as an asymptotic constant.

## Card 2 — Anchor-slope residual, admitted only through a morphism gate

**Operation.** Fix the public anchor \(A=G=(x_0,y_0)\). For a labeled walk point \(P=(x,y)=aG+bT\), \(y\neq 0\), set
\[
\mu=\frac{3x^2+A}{2y}.
\]
The line through \(A\) of slope \(\mu\) is \(Y=y_0+\mu(X-x_0)\). It always meets \(E\) at \(A\). The other two intersection abscissae are the roots of
\[
X^2-\sigma X+\pi,\qquad \sigma=\mu^2-x_0,\qquad \pi=x_0^2+A+\mu^2 x_0-2\mu y_0.
\]
Discriminant \(\Delta=\sigma^2-4\pi\). If \(\Delta\) is not a square in \(\mathbb{F}_p\), this step emits nothing. If \(\Delta=\delta^2\), the two points \(Q_\pm\) have
\[
x_\pm=\frac{\sigma\pm\delta}{2},\qquad y_\pm=y_0+\mu(x_\pm-x_0),
\]
and the chord theorem gives the proved relation
\[
Q_++Q_-=-A=[-1]G,
\]
so the discrete logs sum to \(-1\). That identity alone does not determine \(k\): it is one linear constraint on two unknown logs.

**Label gate, which is the whole claim.** The residual may be used as an extra walk image only if a single pair \((\alpha,\beta)\), independent of \(P\), satisfies
\[
Q_+=[\alpha]P+[\beta]G
\]
on a positive-density set of \(P\), with \((\alpha,\beta)\neq(\pm1,0)\). Then a cross-collision \(Q_+(P_1)=P_2\) of two walk states is
\[
(\alpha b_1-b_2)k\equiv a_2-\alpha a_1-\beta\pmod q,
\]
provided the coefficient of \(k\) is nonzero, then one verification \([k]G=T\). If no such stable pair exists, the branch is discarded. Summing \(Q_++Q_-\) is not accepted as a substitute.

**Gain.** A stable invertible \(\alpha\) is a morphism \(E\to E\), hence only a relabeling of one discrete log, not a smaller domain. The only remaining saving is a cross-collision constant: at most \(\sqrt{2}\) fewer steps if \(Q_+\) is a second, nearly disjoint, image of every step. Each image must then cost \(<0.414\) group additions, including the discriminant test and the square root. A generic \(\mathbb{F}_p\) square root is an exponentiation, \(\Theta(\log p)\) multiplications, which already exceeds \(0.414\) additions for cryptographic \(p\) and for \(q\approx 2^{16}\). So the card beats negation-rho only in the thinner case where \(\Delta\) is a square in the function field \(\mathbb{F}_p(E)\) and the resulting map equals some \([\alpha]+\)translation that evaluates in \(<0.414\) additions. Setup is one anchor. No table, no rank, no training. Failed non-squares are charged field operations. If the image is computed only on a distinguished fraction \(\theta\), the step-count factor is only \(\sqrt{1+\theta}\), and the inequality becomes \(\theta/2>\theta\tau\) with \(\tau\) the extra cost in additions, i.e. \(\tau<1/2\), which a generic square root also fails.

**Prior art.** This is not the H010 equal-tangent fiber. Those four points are the zeros of \(3x^2+A-2\mu y\), and they were never given individual affine labels. Here the line is the anchor chord of slope \(\mu(P)\), the sum relation is \(-A\) rather than \(O\), and the label is admitted only after the morphism gate. It is also not a parallel-chord birthday: the third point of a chord through two labeled points is tautological. Bernstein–Lange already spend the only free involution, \(P\mapsto -P\). A second reflection \(P\mapsto A-P\) gives the same \(\sqrt{2}\) and does not stack, because the two involutions generate a translation of order \(q\).

**Unsupported assumption.** \(\Delta\) is a square in \(\mathbb{F}_p(E)\), and the resulting rational map is \([\alpha]+[\beta]\) with evaluation cost \(<0.414\) additions and \((\alpha,\beta)\) not the negation already in the baseline.

**Cheapest falsifier.** Symbolic, on the function field of one ordinary curve: compute \(\Delta\) from the formulas above and test whether it is a square (valuation parity at \(O\) and at the three geometric 2-torsion places, then a square test in \(\mathbb{F}_p(x)[y]/(y^2-x^3-Ax-C)\)). If it is not a square, kill the asymptotic claim; rational points may still split \(\Delta\) sometimes, but then every image pays a generic square root and loses to negation-rho. If it is a square, identify \((\alpha,\beta)\) from three public multiples \([n]G\) and stop if \(|\alpha|\ge 2\) or the map is \(\pm1\). No full-group sweep and no secret \(k\).

## Card 3 — Coordinate HNP bridge, fixed generator, no walk selector

**Operation.** This is not a rho variant. For public multipliers \(t_i\in\mathbb{F}_q^\times\), compute
\[
P_i=[t_i]T=[t_i k]G
\]
by an ordinary scalar multiplication, and read a coordinate leak
\[
L_\mu(P_i)=\text{the top }\mu\text{ bits of the integer representative of }x(P_i)\in\{0,\ldots,p-1\}.
\]
Hidden-number recovery asks for \(k\) from samples \((t_i, L_\mu(P_i))\) under the hypothesis that \(L_\mu(P_i)\) equals the top \(\mu\) bits of the integer \(t_i k\bmod q\). Use the Boneh–Venkatesan / Howgrave-Graham–Smart lattice: dimension \(d=\Theta(\mu^{-1}\log q)\) if the leaks are exact top bits, one LLL call, then one verification \([k]G=T\). Concrete starting parameters to freeze before any test: \(\mu=\lceil\sqrt{\log_2 q}\rceil\) and \(S=2\lceil\sqrt{\log_2 q}\rceil\) samples, the classical regime in which exact top-bit leaks of \(t_i k\bmod q\) determine \(k\).

**Ledger.** Each sample costs \(\ell\le 1.5\log_2 q\) group additions (double-and-add, no window precomputation credited unless it is counted here too). Total sample cost \(S\ell\). Lattice cost is polynomial in \(d\) and \(\log q\) bit operations; charge it, but it is negligible beside \(S\ell\) only when the bit-leak hypothesis is already true. No walk, no abandoned trail, no factor-base rank, no training set beyond the \(S\) samples. Memory is \(S\) field elements. Failed lattices (no verified \(k\)) are paid in full and the method does not fall back to a hidden rho.

**Gain.** If the leaks were exact top bits, \(S\ell=O(\sqrt{\log q}\cdot\log q)\) additions would beat \(t_0\) by an exponential margin. If each sample agrees with the true top bits of \(t_i k\bmod q\) only with probability \(2^{-\mu}\), the samples are independent of \(k\) and the lattice does not recover it; expected cost is then a full failure plus a return to negation-rho, i.e. a loss of the whole sample budget. A bias \(\delta\) above \(2^{-\mu}\) needs a fresh sample-size calculation; it is a win only if the resulting \(S(\delta)\) still satisfies \(S(\delta)\ell<t_0\).

**Prior art.** Boneh–Venkatesan, CRYPTO 1996, is HNP for most-significant bits of hidden linear forms. Nguyen–Shparlinski recover an ECDSA key from partial nonce bits, which are already bits of a scalar in a linear equation. They do not supply a map from \(x([n]G)\) to those bits. The H010 reversal law is not this attack: that law says a generator-independent point bit cannot have positive parity agreement for every generator at once, because \(q\) odd flips the scalar parity of \(-G\). Card 3 fixes \(G\), uses top bits rather than parity, and never uses the bits as a halving selector. It is also not an iid bin of a Hensel digit.

**Unsupported assumption.** For the fixed public \(G\), and for a positive-density set of \(t\), the top \(\mu=\lceil\sqrt{\log_2 q}\rceil\) bits of \(x([t]T)\) equal the top \(\mu\) bits of \(tk\bmod q\) often enough that the HNP lattice’s verified success probability is bounded away from \(0\) at the sample size above.

**Cheapest falsifier.** One ordinary curve, \(q\approx 2^{20}\), known \(k\) used only inside the test, \(2000\) random \(t\). Compare top \(\mu\) bits of \(x([t]T)\) with top \(\mu\) bits of \(tk\bmod q\), \(\mu=\lceil\sqrt{20}\rceil=5\). Kill the card if the agreement rate is \(<2^{-\mu}+q^{-1/4}\). That threshold is far below what HNP needs and already makes \(S\ell>t_0\) under a standard bias-to-sample conversion \(S\gtrsim \delta^{-2}\log q\). One curve kills a uniform leak. It does not prove that some thinner family of traces is linearly related to \(k\).

## What was withheld

Free stacks of two reflections, x-only doubling (a bijection on negation classes), Fibonacci coefficient chains (image is a one-parameter subgroup of the label lattice and misses a random \(k\)), and “lookup \(-A-U\)” (the same \(\sqrt{2}\) as negation, not a second factor). Neighbor-min folds with \(s\) additions lose by \(\sqrt{s}\) under the image bound above. Coarse bins of a rational function were not reopened.

No experiment was run, and no asymptotic improvement is claimed.
