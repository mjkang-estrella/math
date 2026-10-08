# Raw H010 Grok hybrid proposal — unverified claims

Task: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h010-hybrid-geometry-grok-20261008-r1
Provider/model: grok/grok-4.7. Terminal completed.
Root does not adopt this report wholesale. Proposed large all-point tests are NOT authorized; missing selector/cost assumptions and finite-to-asymptotic claims need correction.

No verified improvement. Three mechanisms are worth writing down. None is claimed to beat negation-aware rho.

Baseline remains the ordinary prime-field, prime-order, full-range discrete log: negation-aware Pollard rho at about \(\sqrt{\pi q/4}\) group operations, with the known automorphism factor, and with preprocessing, memory, failed attempts, verification, and extraction charged. Shoup's generic bound does not forbid a coordinate method. These cards do not use adaptive factor-base sampling, algebraic gcd compression, or a quantum algorithm.

## Card 1 — Equal-tangent associates as extra walk images

**Operation.** Fix the usual negation-aware walk \(P=[a]G+[b]Q\), with \((a,b)\) tracked. At the current point, if the tangent slope \(\mu=(3x^2+A)/(2y)\) is finite, solve the degree-4 condition for other points with the same tangent slope:
\[
(3x^2+A)^2-4\mu^2(x^3+Ax+B)=0,
\]
and set \(y=(3x^2+A)/(2\mu)\). Each rational root other than \(P\) is an associate \(\varphi_j(P)\). Store the ordinary rho key of \(P\) and, when present, the keys of the associates. A collision between an associate of one walk point and another walk point is the event
\[
\varphi(P_1)=P_2.
\]
Under the affinity assumption below this is
\[
\alpha(a_1+b_1 k)+\beta=a_2+b_2 k,
\]
so
\[
(\alpha b_1-b_2)k=a_2-\alpha a_1-\beta,
\]
provided the coefficient is nonzero, then one point-equality check. The four geometric points with slope \(\mu\) sum to \(O\) because \(3x^2+A-2\mu y\) has pole order 4 at \(O\). That principal-divisor relation is not the recovery equation. Summing all four labels cancels the coefficient of \(k\). Recovery uses only the cross-walk collision, whose two labels are independent.

**Structural source of gain.** Negation is the degree-2 map \(x\). Equal tangent slope is a different degree-4 condition. Each extra rational associate is another image of the same walk label. If a positive-density set of points has an associate \(\varphi(P)=[\alpha]P+[\beta]G\) with \((\alpha,\beta)\neq(\pm1,0)\) fixed, the collision probability rises by that density while the step adds only a constant number of field operations (one degree-4 solve).

**Full-work threshold.** Let \(\varepsilon\) be the density of points that have at least one such nontrivial affine associate, and let \(\gamma\ge 1\) be the step cost in group-operation equivalents, including the degree-4 solve and extra storage. Against negation-aware rho this is a gain only if \(\sqrt{1+\varepsilon}/\gamma>1\). Bounded geometric fiber size (\(\le 3\) extra roots) cannot change the exponent. It can change only the leading constant, and only if that inequality holds after memory and failed associate solves are charged. If the rational associates are not affine, a key collision does not produce the displayed linear equation.

**Applicability.** Ordinary \(E/\mathbb{F}_p\), \(\#E(\mathbb{F}_p)=q\) prime, \(q\neq p\), \(q\approx p\), \(\gcd(q,p-1)=1\), no extra endomorphism defined over \(\mathbb{F}_p\), full unknown \(k\in\{1,\ldots,q-1\}\). Vertical tangents and \(\mu=0\) are exceptional branches and must be charged, not dropped.

**Prior art.** This is not the H005 parallel-chord birthday. There the third intersection of a secant was \(T=-(U+V)\), so the three labels summed to \((0,0)\). Here the solved equation is a collision of one associate with an independently labeled walk point. It is also not negation-rho, not a raw consecutive \(x\)-window, and not an endomorphism collision: multiplication by a fixed integer is bijective on a prime-order group, so it does not add rational images.

**Unsupported assumption.** On a positive-density set, each extra rational equal-slope point satisfies \(\log\varphi(P)=\alpha\log P+\beta\) with \((\alpha,\beta)\neq(\pm1,0)\) independent of \(P\).

**Cheapest falsifier.** On one ordinary curve with \(q\approx 2^{16}\), for every rational point compute the rational equal-slope associates by the degree-4 equation and their discrete logs by ordinary rho or BSGS. Kill the card if either the density of points with an extra rational associate is \(0\), or the map \(n\mapsto \log\varphi([n]G)\) is not affine with a stable \((\alpha,\beta)\neq(\pm1,0)\) on a positive-density component. One curve kills a claimed uniform affine law. It does not by itself prove an asymptotic density.

## Card 2 — Torsion-lift Hensel digit as the backward-walk selector

**Operation.** Silverman's local torsion lift is the unique point \(\widehat R\in E(\mathbb{Z}/p^2\mathbb{Z})\) with order \(q\) and \(\widehat R\equiv R\pmod p\). It is computed by taking the one-parameter Hensel lift of \(R\) and solving the linear condition \([q]\widehat R=\mathcal O\bmod p^2\), in \(O(\log q)\) operations on linear polynomials modulo \(p^2\). Write \(u(R)\in\mathbb{F}_p\) for that correction digit. Walk backward from \(Q+[r]G\) for a known random restart \(r\):
\[
U=[2^{-1}]R,\qquad V=U-H,\qquad H=[2^{-1}]G,
\]
and choose \(U\) or \(V\) according to the parity of \(u(R)\), not according to a coordinate lattice score. Update \((a,b)\) by the corresponding halving rule. A collision of underlying points with \(a_i\neq a_j\) gives
\[
k=(b_j-b_i)(a_i-a_j)^{-1},
\]
checked by one scalar multiplication. Charge every restart, every \(O(\log q)\) lift, and the cycle detector.

**Structural source of gain.** The selector is not a rational function of \(R\) and not a multiplicative character. The torsion lift is a homomorphism for the prime-to-\(p\) torsion, so \(u\) is a coboundary of the naive coordinate section against that homomorphism. The hope is that the parity of this coboundary agrees with the halving bit often enough that the useful trajectory is \(o(\sqrt q/\log q)\), rather than a random preimage guess.

**Full-work threshold.** Each step already costs \(\Theta(\log q)\) group-operation equivalents modulo \(p^2\). The walk therefore beats \(\sqrt{\pi q/4}\) only if the expected number of steps until a useful collision is \(o(\sqrt q/\log q)\). A selector that is merely unbiased costs \(\Theta(\sqrt q\log q)\) and loses to negation-aware rho. There is no exponent gain from the lift itself: \([q]\widehat R=\mathcal O\) exactly, so the formal logarithm of the lifted torsion is \(0\) and the Smart ratio is \(0/0\).

**Applicability.** Same ordinary prime-order scope, \(p\nmid q\), precision exactly \(p^2\). This does not extend to a claim about deeper Witt digits. Restarts are part of the cost. No secret interval is used.

**Prior art.** Silverman, *Four Faces of Lifting* (ECC 2007): the torsion lift preserves \(\widehat Q=[k]\widehat G\) and is computable, but multiplication by \(q\) lands on \(\mathcal O\), so the formal group does not see \(k\). That talk does not test \(u(R)\bmod 2\) as a halving selector. H005's inverse walk used the different selector \(s(R)=(h(x),x,y)\) from two-dimensional lattice reduction on the integer representatives; that card is not reused here. H003's section predictors, which try to read \(k\) off a section value, are a different operation.

**Unsupported assumption.** Parity of \(u([n]G)\) agrees with the canonical halving bit of \(n\) on a fraction \(1/2+\delta\) with \(\delta\) bounded away from \(0\), uniformly in the ordinary family, strongly enough to force the trajectory bound above.

**Cheapest falsifier.** On one ordinary curve with \(q\approx 2^{12}\), compute \(u([n]G)\bmod 2\) for every \(n\) and compare with the LSB of \(n\) in \(\{0,\ldots,q-1\}\). Kill the card if the agreement is \(1/2+o(1)\). A single curve kills a uniform bias claim. It does not prove that some thinner arithmetic progression of scalars remains biased.

## Card 3 — Arithmetic-progression compression of the same Hensel digit

**Operation.** Compute the same digit \(u([n]G)\in\mathbb{F}_p\), but do not walk backward. Partition \(\mathbb{F}_p\) into \(m\) public bins, \(m\) fixed (start with \(m=2\) and \(m=16\)). Run negation-aware rho. Store a point only by its bin of \(u(P)\), together with \((a,b)\). On a bin collision between \(P_1\) and \(P_2\), test the \(O(s)\) candidate translations
\[
P_1-P_2=[t]G,\qquad |t|\le s,
\]
by \(O(s)\) differential additions, and accept the first \(t\) that also matches the points. A hit with \(b_1\neq b_2\) is
\[
(a_1-a_2-t)+(b_1-b_2)k=0.
\]
The bin is not a window of \(x\)-coordinates and not a Legendre symbol.

**Structural source of gain.** A random function to \(m\) bins does not beat rho: false collisions cancel the birthday gain. A gain appears only if bin level sets of \(u(n)\) contain arithmetic progressions of indices of length \(s\), so that a bin hit shortens the translation test to a known interval of length \(s\) and the stored key is shorter than the full negation class by that factor.

**Full-work threshold.** A Hensel digit costs \(\Theta(\log q)\) group-operation equivalents modulo \(p^2\) each time it is computed. Charging it on every step, the walk beats \(\sqrt{\pi q/4}\) only if the useful-progression factor satisfies \(s/(\log q)^2\to\infty\) and almost every bin collision has its true translation inside the tested interval. Computing the digit only on distinguished points removes the overhead only on the unstored steps; every stored or tested point still pays \(\Theta(\log q)\). If the longest progression in a bin is \(O(1)\), the card is ordinary rho plus a wasted lift.

**Applicability.** Same ordinary scope. The binning is the standard integer representative of the Hensel digit, not a multiplicative character and not an oracle. No claim is made that \(u([k]G)\) itself equals \(k\) or a linear form in \(k\). In fact the second difference of \(n\mapsto u([n]G)\) equals a non-constant rational defect of naive addition, so \(u([n]G)\) is not a polynomial in \(n\) of degree less than \(q-1\). The card uses only the geometry of its level sets.

**Prior art.** Not a raw Hankel window: the key is one non-rational digit, and the tested fiber is an arithmetic progression in the scalar, not a shift of consecutive \(x\)-coordinates. Not fixed character averaging: there is no character sum. Not Silverman's or H003's use of the lift: those compare formal logarithms or section values with \(k\). The formal logarithm of this lift is identically zero and is not consulted. Not the H005 lattice-score walk: the digit is a storage key, not a halving choice.

**Unsupported assumption.** For \(m\in\{2,16\}\), a positive-density subset of each used bin is a union of arithmetic progressions of scalar length \(s\gg(\log q)^2\), and the walk's bin collisions land in that subset with probability bounded away from \(0\).

**Cheapest falsifier.** On one ordinary curve with \(q\approx 2^{16}\), compute \(u([n]G)\) for all \(n\) and, for \(m=2\) and \(m=16\), measure the longest arithmetic progression inside each bin. Kill the card if that length is \(O((\log q)^2)\) or smaller. One curve kills a uniform long-progression claim. It does not prove the absence of a thin family of curves with long progressions.

## What was not carded

A nodal pencil through \(G\) and \(Q\) does not yield a multiplicative discrete log: a collinearity among labeled points either holds for every \(k\), with coefficient sum zero, or is the ordinary group law. Bijective re-encodings (\([c]\), unique halving, \(x\circ[c]\)) do not shrink the prime-order set. Small-\(\ell\) pairings of rational points are trivial because \(\gcd(\ell,q)=1\) makes \(G\) an \(\ell\)-multiple; that is an identity, not a degree lower bound. Shipsey–Swart (ePrint 2008/444) reduces to a finite-field discrete log only for \(\#E(\mathbb{F}_q)=q-1\), which is outside this scope.
