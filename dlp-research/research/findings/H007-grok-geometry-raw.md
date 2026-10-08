# H007 Grok collision geometry: raw completed report

Unaccepted proposer report; see H008-operation-disposition.md for corrections.
Provider grok, model grok-4.7. Request ecdloop-h007-collision-geometry-grok-20261008-r1.

The working reference is unchanged: for one full scalar on an ordinary prime-field prime-order curve, negation-aware Pollard rho costs about \(\sqrt{\pi q/4}\) group operations. Verified improvement is **NONE**. Three collision mechanisms are below. Only the first has a conditional path under that reference, and only by a factor \(\sqrt{w}\) with \(w=\Theta(\log q)\).

## 1. Hankel-window collision

**Operation.** Fix a window \(w=\Theta(\log q)\) and a rho iteration whose step is \(+G\) or \(+Q\) from the current coordinates, with coefficients \((a_n,b_n)\) tracked. Let \(u_n=x(W_n)\). Form the Hankel matrix \(H_n=(u_{n+i+j})_{0\le i,j<w}\) and its displacement generator: the \(O(w)\) entries of the first row, last row, and the Somos-style bracket
\[
\Delta_n=u_n u_{n+3}-A\,u_{n+1}u_{n+2}-B\,u_{n+2}^2
\]
coming from the degree-4 addition relation (the same bilinear identity that makes a pure elliptic sequence Somos-4). Advance by one group addition; update the window in \(O(w)\) field operations. Store the generator, keyed by a canonical normalization (leading nonzero entry \(1\), signs fixed by the negation rule on \(W_n\)).

A collision \(H_n\sim H_m\) means the two length-\(w\) x-windows have the same Padé data. The map \(P\mapsto H(P,P+G,\ldots,P+(w-1)G)\) is rational of degree \(O(w)\) on \(E\). A useful fiber point is one with
\[
R=\varepsilon P+[t]G,\qquad \varepsilon\in\{\pm1\},\quad t\in\mathbb Z,\ |t|<w.
\]
Then the stored labels give
\[
(b_n-\varepsilon b_m)k\equiv \varepsilon a_m-a_n-t\pmod q.
\]
The coefficient of \(k\) is nonzero whenever the two windows are not the same rho segment read twice. Invert it and check the point.

**Gain and barrier.** Image size at least \(q/O(w)\) if fibers are no larger than the degree. Birthday cost is then \(O(w)\sqrt{q/w}\) field operations plus \(\sqrt{q/w}\) group additions, memory \(\sqrt{q/w}\) generators. That is \(o(\sqrt q)\) only when a useful-translation fraction \(f\) of collisions satisfies \(f\sqrt{w}\gg 1\). If \(f\le 1/w\), filtering eats the gain and the cost is \(\Omega(\sqrt{qw})\), a loss. Degree \(O(w)\) caps the geometric fiber; it does not by itself force those fibers to be the translations \(\varepsilon P+[t]G\).

**Prior art.** Negation rho and the fruitless-cycle analysis are the baseline, not this window: Bernstein–Lange–Schwabe, [eprint 2011/003](https://eprint.iacr.org/2011/003) and the matching slides [cr.yp.to/talks/2011.03.07](https://cr.yp.to/talks/2011.03.07/slides.pdf) (search space \(\ell/2\), factor \(\sqrt 2\)). Somos/QRT iteration is forward scalar multiplication by a fixed point, \(n\) cheap steps rather than a collision search: Hone, [arXiv:2001.09076](https://ar5iv.labs.arxiv.org/html/2001.09076). Lauter–Stange already equate EDS index recovery with ECDLP; this card does not invert an EDS term, it collides two windows of a labeled walk. It is not the orbit-segment power-sum circuit (one long product \(\prod_{j<T}(Z-x([j]G))\)), not the adjacent pair \((x(P),x(P+G))\) (degree \(O(1)\), rational inverse translation), and not a fixed-window character sum.

**Assumption.** Rational fibers of this Hankel generator on the prime-order subgroup have useful-translation fraction \(f\gg w^{-1/2}\).

**Falsifier.** On one ordinary curve with \(q\approx 2^{16}\), for \(w=4,6,8\), build the generator for every subgroup point and partition equal keys. If the fraction of pairs with \(R=\pm P+[t]G\) and \(|t|<w\) is below \(w^{-1/2}\), the asymptotic claim is dead. No rho has to be run.

## 2. Independent-label incidence \(U+V=2S\)

**Operation.** Three labeled walks, or one walk read at three independent times. At stored points \(U,V,S\), test
\[
U+V=2S
\]
by hashing \(x(2S)\) (doubling is bijective, \(q\) odd) and probing \(x(-(U+V))\). A hit expands to
\[
(b_U+b_V-2b_S)k\equiv 2a_S-a_U-a_V\pmod q.
\]
The coefficient of \(k\) is a random element of \(\mathbb F_q\) for independent rho labels, hence nonzero with probability \(1-1/q\). This is the missing independent label on the third point: the chord through \(U\) and \(V\) has third point \(-(U+V)\), and equality with \(2S\) is not the chord law applied to a pair whose third point was built from those same two labels.

**Gain and barrier.** With \(L\) stored points, hashing doubles costs \(L\) additions. Probing all pairs costs \(\Theta(L^2)\) additions. Expected hits are \(L^3/q\). One hit at \(L=q^{1/3}\) therefore costs \(\Theta(q^{2/3})\) group operations and \(\Theta(q^{1/3})\) memory. That is worse than \(\sqrt{\pi q/4}\). Restricting to an arithmetic progression replaces the test by BSGS and returns to \(\Theta(\sqrt q)\), not below it. Pair-sum set-size is the barrier; the slope of \(UV\) is not a second channel (equal slopes alone do not give this relation).

**Prior art.** Distinguished from the parallel-chord identity, where the third point is defined as \(-(U+V)\) and the three labels sum to \((0,0)\). Grumpy-giants improves only the generic BSGS constant: Bernstein–Lange, [eprint 2012/294](https://eprint.iacr.org/2012/294). Prime-field summation search, including the one-relation variant, remains above rho: McGuire–Mueller, [eprint 2017/1262](https://eprint.iacr.org/2017/1262.pdf); Amadori–Pintore–Sala, [Finite Fields Appl. 51 (2018)](https://doi.org/10.1016/j.ffa.2018.01.009).

**Assumption.** None that rescues the exponent. An \(L^{3/2-\varepsilon}\) detector for this incidence would, and I do not have one; generic 3-sum structure supplies no such detector.

**Falsifier.** Accounting is already decisive: \(\Theta(q^{2/3})\) versus \(\Theta(q^{1/2})\). A 20-bit check is unnecessary for the exponent. The only experiment that could reopen it is a detector whose measured pair-probe count on an AP-free point list of size \(2^{10}\) and \(2^{12}\) is \(o(L^{3/2})\).

## 3. Mixed doubling-translation orbit, collided as itself

**Operation.** Single walk on the subgroup, label \((a_n,b_n)\), rule
\[
W_{n+1}=2W_n+[s_n]G,\qquad s_n\in\{0,1\}
\]
with \(s_n\) the Legendre bit of \(x(W_n)\). Coefficient update, all public:
\[
a_{n+1}=2a_n+s_n,\qquad b_{n+1}=2b_n.
\]
Start one copy at \(Q\) (\(a_0=0,b_0=1\)) and one at \(O\) (\(b\equiv 0\)). Hash negation-canonical \(x(W_n)\). A hit between the two copies is
\[
a+2^{n}k\equiv a'\pmod q,
\]
so \(k\equiv (a'-a)\,2^{-n}\), coefficient \(2^n\not\equiv 0\). Self-collisions inside the \(Q\)-copy give the same shape with two different exponents of \(2\).

**Gain and barrier.** Each step is one doubling and at most one addition, \(O(1)\) group operations, same order as a rho step. The state space is the negation quotient, size \((q-1)/2\). A random-function collision therefore still takes \(\Theta(\sqrt q)\) steps. Expansion makes \(b_n=2^n\) public and invertible; it does not shrink the set of occupied x-coordinates. The walk is a bijection on the subgroup only if the branch rule is bijective, which this Legendre rule is not, so the functional graph can have short cycles. Short cycles help only if a collision still has nonzero \(b\)-difference. A cycle that closes by pure doubling, \(s_n=0\) throughout, forces \(2^n(a+bk)=a+bk\), hence \((2^n-1)(a+bk)=0\), so either the point was \(O\) or \(2^n=1\) in \(\mathbb F_q\). That is a special order, not a generic discrete log.

**Prior art.** Not the direct-halving walk: the step is forward multiplication by \(2\), with a public branch, and recovery is a collision of two labeled orbits, not rational reconstruction of a halving norm. Iteration functions with a fixed partition of the group are Teske-type rho; constants from the iteration rule sit inside the classical reference once negation is included (same Bernstein–Lange source as card 1). QRT/Lyness iteration (Hone, same URL as card 1) is repeated addition of one fixed point and takes \(\Theta(n)\) steps for the scalar \(n\), which is the wrong direction for a search.

**Assumption.** The functional graph of this specific branch rule on the negation quotient has rho length \(o(\sqrt q)\) while a positive-density set of collisions has \(b\not\equiv b'\). I do not see a structural reason for the \(o(\sqrt q)\); the honest prediction without that assumption is a constant-factor rho variant, not a new exponent.

**Falsifier.** On one ordinary curve with \(q\approx 2^{20}\), run the labeled map from \(Q\) and from \(O\), negation-canonical x-keys, cap at \(4\sqrt q\) steps, over a few seeds. If the first useful collision (nonzero \(b\)-difference, verified point) lands in the same \(\Theta(\sqrt q)\) band as negation rho on the same curve, the exponent claim is dead. A shorter cap does not distinguish constants from exponents.

## Wave note

Best supported full-solver cost remains negation rho, about \(\sqrt{\pi q/4}\) group operations, memory negligible for distinguished points or \(\Theta(\sqrt q)\) for BSGS. Verified improvement: **NONE**. No experiment was run. The only hypothesis here with a possible \(o(\sqrt q)\) cost is the Hankel-window collision, and only if the fiber count on a 16-bit ordinary curve beats \(w^{-1/2}\). The incidence repair of the chord gap costs \(\Theta(q^{2/3})\) and should not be reopened without a new detector.
