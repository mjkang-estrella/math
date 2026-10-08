# H015 Grok composed-mechanism proposal — raw, unverified

2026-10-08. grok/grok-4.7. Task
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h015-composed-mechanisms-grok-20261008-r1`.
Terminal COMPLETED, no pending child runs. Retained verbatim as a proposal;
its algebra, counts, baseline constants and experiment requests are NOT accepted.
Independent preflight is required. Root did not run any proposed experiment.

Verified improvement remains **NONE**. The baseline is unchanged: negation-aware Pollard rho, about \(\sqrt{\pi q/4}\) group additions, on an ordinary curve \(E/\mathbb{F}_p:y^2=x^3+Ax+C\) with \(\#E(\mathbb{F}_p)=q\) prime, \(q\neq p\), \(q\approx p\), \(\gcd(q,p-1)=1\), \(\mathrm{Aut}=\{\pm1\}\), and a full unknown scalar \(T=[k]G\).

Three compositions are below. Each is a different paid recovery from the openings left by the anchor-pole, H011, and H012 reviews. None treats a rational self-map as \([n]\), reads \(k\) off three samples, feeds \(x\)-bits to HNP, or reruns the running-sum shepherd. Nearby compositions that die by a zero coefficient of \(k\), by \(k\mapsto q-k\) with the same \(x\), or by a \(\Theta(q^{2/3})\) pair scan are withheld at the end.

## Card 1 — Special \(S_3\) box module

**Obstruction removed.** The killed H012 module is a fixed 28-row integer lattice for \(S_6\) at box exponent \(1/5\). The algebra review left general \(m=3\) small-root recovery undecided: missing a proved bound is not a proof that no module works. This card supplies a different, group-law module for a quadratic, not that \(S_6\) matrix.

**Procedure.** Freeze \(B=\lfloor p^{1/3}\rfloor\). Factor base \(\mathcal{B}\) is the rational points whose integer abscissa lies in \(\{0,\ldots,B-1\}\) (both \(y\)-signs). Build it by scanning those \(B\) field elements and taking square roots of the cubic; logs of base points are unknown nuisance variables. Walk labeled points \(R=aG+bT\) by adding a fixed public jump with \(b\not\equiv 0\). For each \(R\), let \(f(X,Y)\) be the degree-2-in-each Semaev eliminant \(S_3(X,Y,x(R))\), normalized monic in \(X\), so \(f=0\) iff abscissae \(X,Y,x(R)\) are collinear for some signs.

Lattice, dimension 10, monomials \(\{X^i Y^j:i,j\le 3,\,i+j\le 3\}\). Rows are the coefficient vectors of \(p\,X^i Y^j\) and of \(f\,X^i Y^j\), scaled by \(B^{3-i-j}\) on the \((i,j)\) column, exactly the Jochemsz–May shape for two variables. LLL, then keep vectors whose scaled length is below the Howgrave-Graham threshold \(p\,B^{3/2}\). From each survivor \(g\in\mathbb{Z}[X,Y]\), compute \(\mathrm{Res}_Y(f,g)\) and test rational roots inside the box. A hit \((x_1,x_2)\) plus a sign pair with \(\varepsilon_1 P+\varepsilon_2 Q+\varepsilon_3 R=O\) and \(P,Q\in\mathcal{B}\) is one sparse row
\[
\varepsilon_1\lambda(P)+\varepsilon_2\lambda(Q)=-a-bk\pmod q.
\]
Collect \(B\) independent rows, solve the sparse system in the \(\lambda\)'s and in \(k\) by Wiedemann, and verify \([k]G=T\). Failed lattices and singular matrices are paid in full. No rho fallback is hidden inside the ledger.

**Baseline and gain.** Generation of \(R\) is one group addition each. At \(B\sim q^{1/3}\), a uniform model gives \(\Theta(1)\) triples in \(\mathcal{B}^3\) summing to a fixed \(R\). If the lattice returns one such triple in \((\log p)^{O(1)}\) bit operations, \(B\) successes cost \(q^{1/3+o(1)}\) group additions plus one sparse solve. Wiedemann on \(B\) sparse rows is \(B^{2+o(1)}=q^{2/3+o(1)}\) field operations, which is worse than \(\sqrt{q}\) additions. The exponent win appears only in the unbalanced cutoff \(B=q^{1/4-\varepsilon}\) if, contrary to the generic triple count, this walk produces \(\gg B\) relations before \(q^{1/2}\) additions. That is the whole gain claim. Setup is the base scan \(O(B\log p)\). Memory is the \(B\times B\) sparse matrix. I do not claim the proved Jochemsz–May region reaches this box; the card is that this chordal quadratic may factor inside LLL beyond the generic bivariate bound.

**Prior art.** Semaev summation polynomials, Jochemsz–May (Asiacrypt 2006), and the prime-field index-calculus surveys (Galbraith–Gaudry 2015/1022; Petit–Kosters–Messeng). Distinct from the frozen H012 \(S_6\) module and from Diem’s extension-field balance.

**Assumption.** For this \(f\), LLL returns the planted box root whenever one exists, at \(B=\lfloor p^{1/3}\rfloor\), with probability bounded away from 0, at dimension 10.

**Falsifier.** One ordinary curve, \(q\approx 2^{24}\). Plant 30 decompositions: choose \(P,Q\) in the box, set \(R=-(P+Q)\), build \(f\), run the dimension-10 LLL. Kill the card if fewer than 3 plants return \((x(P),x(Q))\). No discrete log is required. A kill here does not forbid a larger module.

## Card 2 — One Miller probe for a whole baby progression

**Obstruction removed.** H011’s degree-2 fibers collapse to a paid query “two known logs sum to \(2C\)”, envelope \(L+q/L\). The same review says a higher-degree anchored divisor is unpriced, not impossible, if the generator has a nonzero coefficient of \(k\) and does not enumerate the support. The generator here is one function, built by double-and-add, whose zero divisor is an arithmetic progression of babies.

**Procedure.** Choose \(B\) a power of 2, \(B<q\). Let \(D=[B]G\), computed by \(O(\log B)\) doublings, label \((B,0)\). Claimed identity, to be killed or kept before any walk: in \(\mathbb{F}_p(E)\),
\[
\prod_{j=0}^{B-1}\bigl(x-x([j]G)\bigr)
=\eta\cdot\frac{\psi_{B}(x-x(S))}{\psi_{B-1}(x)^{c}}
\]
is false as written for a general AP, so the card does **not** use that shape. The procedure that is actually specified is:

Build the Miller function \(f_B\) with divisor \(B(G)-([B]G)-(B-1)(O)\) by the double-and-add loop on the public scalar \(B\), \(O(\log B)\) line and vertical steps, all charged. This \(f_B\) vanishes only at \(G\), not on the baby progression. The **new** function is the translate product defined recursively, not by listing zeros. Write \(g_1=\ell_{O,G}\), the vertical line, and
\[
g_{2m}=g_m\cdot(g_m\circ\tau_{-mD})\cdot v_m,
\]
where \(\tau_Q(P)=P-Q\) and \(v_m\) is the unique line-vertical correction of degree \(O(1)\) that cancels the extra zeros and poles of the translated factor and restores pole only at \(O\). Each correction is solved from a \(3\times 3\) slope system. The recurrence runs \(\log B\) levels. If a level’s correction stays degree \(\le 4\) and can be written down from the current \(g_m\) in \((\deg g_m)^{1+o(1)}\) field operations, then \(g_B\) is available as an arithmetic circuit of size \(B^{1+o(1)}\).

Evaluate by reducing that circuit modulo the baby polynomial \(\Pi(X)=\prod_{j<B}(X-x([j]G))\), which is built once in soft-\(O(B)\) by a product tree. A giant \(R_t=T-[t]D\) with label \((-tB,\,1)\) hits a baby iff the remainder of \(g_B\) at \(x(R_t)\) is zero and the \(y\)-sign matches a stored bit. A hit \([t]\)-free:
\[
k-tB\equiv j\pmod q
\]
for the baby index \(j\) recovered from the root, because \(b=1\). Verify \([k]G=T\).

**Baseline and gain.** Ordinary BSGS spends \(\Theta(q/B)\) giant additions. Here the giants are still walked one addition at a time unless the circuit evaluation of \(g_B\) at an entire giant AP can be advanced by the differential recurrence of \(x([n]D)\) in \(O(1)\) field operations per giant. That does not beat BSGS. The gain is only the following cutoff: if the translated product at the top level is itself a Miller function of a **single** public point of order dividing \(B\), then one gcd of two degree-\(B\) polynomials replaces the giant loop. Cost soft-\(O(B)\). Set \(B=q^{1/3}\). That is below \(\sqrt{q}\) only when that collapse is true. Setup and memory: the product tree, \(O(B)\) field elements. Failed gcd (no common root) is a paid miss; there is no second walk inside the ledger.

**Prior art.** Miller’s algorithm and Shanks BSGS. Not the H011 reflection query, which tests one center at a time, and not a rational self-map of \(E\).

**Assumption.** The correction \(v_m\) has degree \(\le 4\) at every level, and \(g_B\) equals a function with zero divisor exactly \(\sum_{j<B}([j]G)\) rather than \(B(G)\).

**Falsifier.** Symbolic, one ordinary curve, \(B=8\). Expand \(g_8\) by the recurrence and compare its zero divisor with \(\sum_{j<8}([j]G)\). Any extra zero, a degree-\(>4\) correction, or a pole away from \(O\) kills the collapse. Do not walk giants unless this passes.

## Card 3 — Bit readout from signed slopes against the public doubling chain

**Obstruction removed.** An \(x\)-only predicate cannot separate \(k\) from \(q-k\). The anchor card’s global square-root branch is impossible. This card never builds that branch. It uses \(y\), so \(T\) and \(-T\) differ, and it asks for an exact base-2 digit, not a biased sample and not an HNP lattice.

**Procedure.** Public chain \(D_i=[2^i]G\) for \(0\le i<n\), \(n=\lceil\log_2 q\rceil\), cost \(n\) doublings, labels \((2^i,0)\). For the target \(T=(x,y)\), \(y\neq 0\), and each \(i\) with \(D_i\neq\pm T\), set
\[
\lambda_i=\frac{y-y(D_i)}{x-x(D_i)}\in\mathbb{F}_p.
\]
Proposed digit map, frozen before any check: write the integer representative of \(\lambda_i\) in \(\{0,\ldots,p-1\}\) and set
\[
\beta_i=\Bigl\lfloor\frac{2\lambda_i}{p}\Bigr\rfloor\in\{0,1\}.
\]
Interpret \(\beta_0+\beta_1 2+\cdots+\beta_{n-1}2^{n-1}\bmod q\) as a candidate \(k\), and verify \([k]G=T\). If the verify fails, the method stops. It does not start a rho search charged to a success. Field cost is \(n\) inversions, batchable to one inversion plus \(O(n)\) multiplications, plus the \(n\) doublings. Memory is \(n\) points. No samples, no modulus \(q\) hidden-number lattice, no agreement probability.

**Baseline and gain.** If \(\beta_i\) is the \(i\)-th binary digit of the representative of \(k\) in \(\{0,\ldots,q-1\}\), the cost is \(O(\log q)\) group operations and beats \(\sqrt{\pi q/4}\) by an exponential margin. If the map is only a function of \(x(D_i)\) and \(x(T)\), it cannot separate \(k\) from \(q-k\) and the verify fails on one of \(T,-T\). The use of \(y-y(D_i)\) is what makes separation possible; it is not proved.

**Prior art.** Binary doubling chain and Miller slope accumulation compute these slopes for a **known** scalar. They do not read an unknown scalar off the slopes. Not Boneh–Venkatesan HNP and not the H014 order-6 character sums: there is no estimation step, only one verify.

**Assumption.** For every ordinary curve in scope and every \(k\), \(\beta_i\) equals the \(i\)-th bit of \(k\).

**Falsifier.** One ordinary curve, \(q\approx 2^{12}\), five known scalars including \(1\), \(2\), and \(q-1\). Compute \(\beta_i\) from the slopes and compare with the bits. One mismatch kills the exact readout. A mismatch does not forbid some other function of the same \(\lambda_i\) of description length \(O(n)\); that other function is not supplied here.

## Withheld

- Tangent-parallel residual admitted by a baby gcd: both recovered points are pure babies, so the coefficient of \(k\) is identically 0.
- Two involutions: they generate a translation of order \(q\) and do not stack a second \(\sqrt{2}\).
- Legendre symbol or halving-polynomial splitting type as a bit of \(k\): the same \(x\) occurs for \(k\) and \(q-k\), and \(q\) odd flips parity.
- EDS ratio \(\psi_2(T)/\psi_1(T)^4=\psi_{2k}(G)/\psi_k(G)^4\): true by the composition formula, and inverting it is the discrete log again.
- Unbalanced 3-sum reporter and Coppersmith at the proved bivariate box: both rebalance at \(\Theta(\sqrt{q})\) or at \(q^{2/3}\) once sparse linear algebra is counted.
