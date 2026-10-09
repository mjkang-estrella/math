# H044 raw Grok full-solver report — UNACCEPTED

2026-10-09 UTC. Provider grok / grok-4.7. Terminal task:
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h044-fullsolver-compositions-grok-20261009-r1`.
Root retrieved through task_status. Claims below require independent review;
no improvement accepted. In particular the translation-degree, within-block
null-event and cost-minimization arguments have unresolved objections.

No surviving labelled search schedule. Verified complete-work improvement stays **NONE**, and the working exponent stays **1/2**. Three schedules are fully specified below. Each one changes the eligible event, the fiber, or the block law relative to batched negation rho and x-only negation BSGS. None beats an equally informed baseline once labels, eligible pairs, memory, and nulls are charged. No experiment is justified. The H034 cap was not touched. Nothing was run, imported, edited, or delegated.

The low-memory comparator is Bernstein–Lange–Schwabe negation rho: heuristic \((1+o(1))\sqrt{\pi q/4}\approx 0.886\sqrt{q}\) iterations on the negation quotient \(N=q/2\), each a batched affine addition of \(5M{+}S\), fruitless-cycle overhead \(\Theta(1/\sqrt{r})\). The high-memory comparator is average-case x-only negation BSGS, \((b+q/(4b))(2.5M{+}S)\), which is \(\sqrt{q}\,(2.5M{+}S)\) at the best \(b\). Negation, batch inversion, lazy replay, rotated cycle checks, and fixed multi-giant layouts are baseline. Conjugate outputs are not treated as independent samples. Feature equality is not treated as a labelled collision.

## 1. Side-abscissa probe, eligible pairs only

**Successor.** Negation-canonical \(r\)-adding walk. The inserted state is the main canonical point \(\psi(W)=\lvert W+J_{h(W)}\rvert\). The same denominator also yields the side abscissa \(x(W-J_{h(W)})\). From the corrected affine invoice, one full sum plus that side abscissa costs \(6M{+}2S+\varepsilon_K\). Sides are not inserted.

**Labels.** \(W=\varepsilon([a]G+[b]Q)\) and \(J=[u]G+[v]Q\) give
\[
W-J=[\varepsilon a-u]G+[\varepsilon b-v]Q.
\]
A hit against a stored main point with coefficient \(b'\) is useful only when \((\varepsilon b-v)-\varepsilon'b'\not\equiv 0\pmod q\). A zero coefficient is a null, not a success. Recovery is that linear equation, then one scalar check.

**Detector and eligible pairs.** Store every main canonical abscissa and its label. At step \(t\) test only \(\{\psi(W),\,x(W-J)\}\) against those \(t\) stored mains. Side–side pairs are not events. This is not the all-pairs model on \(2t\) samples, and it is not the parked fixed-table/rho hybrid: the table is the walk’s own history.

**Optimistic law, already enough to lose.** If both probes were uniform on the quotient, independent, and always useful, the hazard would be \(\lambda(t)=2t/N\). Then \(\mathbb{E}[T]=\sqrt{\pi q/8}\approx 0.627\sqrt{q}\), and the field bill would be about \(0.627(6{+}2s)\sqrt{q}\). At \(s=1\) that is \(5.01\sqrt{q}\) against \(\sqrt{q}\,(2.5{+}s)=3.5\sqrt{q}\). At the same stored-abscissa count \(b\approx 0.627\sqrt{q}\), BSGS costs \((b+q/(4b))(2.5{+}s)\approx 1.026(2.5{+}s)\sqrt{q}\), about \(3.59\sqrt{q}\) at \(s=1\). The probe is worse by a factor of about \(1.4\) before nulls, fruitless cycles, and replay.

The invalid all-pairs reading loses as well. Two independent samples per round, every unordered pair kept, would cost \(\sqrt{\pi q/4}\,(3{+}s)\) because the \(6M{+}2S\) round is split over two samples. For every \(s\in[0,1]\),
\[
0.886(3{+}s)>(2.5{+}s).
\]
At \(s=1\) the left side is \(3.54\) and the right side is \(3.5\). Correlation and zero-coefficient hits only move the side probe upward. A free independent second class would beat BSGS; this side abscissa is neither free nor independent. Prior art is the same affine sum already priced in the H043 disposition, plus ordinary history detection. It is not Wang–Zhang cycle escape and not a new quotient.

**Unsupported assumption.** That \(x(W-J)\) is an independent uniform quotient sample and that every abscissa hit has a nonzero coefficient of \(k\).

**Cheapest falsifier.** None is needed to reject a gain: the optimistic invoice already sits above matched-memory x-only BSGS. A fixture check would only measure how far below the optimistic hazard the real walk falls.

## 2. Degree-2 sum feature, with the fiber inverse written down

**Operation.** Fix the public anchor \(G=(a,y_G)\), \(f(a)=y_G^2\neq 0\). For \(t=x(W)\),
\[
\varphi(t)=x(W{+}G)+x(W{-}G)=\frac{2\bigl(at^2+(a^2+a_E)t+aa_E+2b_E\bigr)}{(t-a)^2}.
\]
The cubic terms cancel, so \(\varphi\) is degree 2, as already corrected. Hash \(\varphi(t)\) along the walk.

**Recovery map.** \(\varphi(t)=\varphi(s)\) if and only if \(s=t\) or \(s=\pi(t)\). In the coordinate \(u=t-a\), the nontrivial partner is the Möbius involution
\[
v=\frac{-2f(a)\,u}{(3a^2+a_E)u+2f(a)},\qquad \pi(t)=a+v.
\]
Applying the map twice returns \(u\). The denominator is not identically zero: \(f(a)=0\) would be rational 2-torsion, absent for odd prime \(q\). The branch \(s=t\) is ordinary abscissa collision and is cheaper to detect by hashing \(x\).

**Why this is not a labelled collision.** A translation \(P\mapsto P+T\) acts on abscissae by a degree-2 rational map. The partner \(\pi\) is degree 1, so it is not \(x(P+T)\) for any fixed \(T\). It is also not \(x\circ[n]\) for any fixed \(n\) with \(\lvert n\rvert>1\), because that degree is \(n^2\). A hash hit \(\varphi(W)=\varphi(V)\) between two labelled walk points therefore gives \(x(V)=\pi(x(W))\) and no group equation \(V=\varepsilon W+[m]G\). Both points already carry labels by the walk; the Möbius relation does not produce a nonzero coefficient of \(k\). Solving the abscissa equation for candidate \(x\)-values returns a fiber of abscissae, not a scalar. That is the same gap as treating a feature collision as a point collision.

**Cost.** Each evaluation is a small rational function of an abscissa the walk already paid for, plus a hash. The nontrivial hits do not decode, so the extra detector cannot reduce the number of group operations. Prior art is the chord-sum identity already in the H043 disposition. The new step is the explicit inverse, which closes the missing recovery map in the direction that does not yield \(k\).

**Unsupported assumption.** That the nontrivial \(\varphi\)-fiber is induced by a group translation or by \([n]\) for a known small \(n\).

**Cheapest falsifier.** The degree comparison above is already decisive. A fixture is optional: on any ordinary prime-order curve, evaluate \(\pi(x(G)),\pi(x([2]G)),\pi(x([3]G))\) and test equality with \(x([m]G\pm[n]G)\) for small fixed \(m,n\). A single miss refutes a universal translation rule. No such run was performed.

## 3. Remixed short arithmetic-progression herd

**Successor.** A herd of \(k\) walks. A block starts with a full mix that refreshes the centre \(C_i=[a_i]G+[b_i]Q\), charged at \(C_f=5M{+}S\). The next \(\ell-1\) steps add one fixed public jump \(D\), at the x-only price \(C_x=2.5M{+}S\), but only if a real batched x-only chain is maintained. Points of block \(i\) are \(P_{i,j}=C_i+[j]D\) for \(0\le j<\ell\).

**Eligible events.** Inside one block the coefficient of \(k\) does not change, so those pairs are null. Between blocks \(i\) and \(m\),
\[
C_i-C_m=[\delta]D \quad\text{or}\quad C_i+C_m=-[\sigma]D
\]
for an offset \(\delta\in\{-(\ell-1),\ldots,\ell-1\}\) or a sum-index \(\sigma\in\{0,\ldots,2\ell-2\}\). One offset is one event: the \(\ell-\lvert\delta\rvert\) index pairs that sit on that offset are the same equation, not \(\ell^2\) samples. There are \(4\ell-2\) such atoms. If the centre difference is uniform, the union probability is \((4\ell-2)/q\), and only those atoms with \(b_i\not\equiv\varepsilon b_m\) are useful.

**Invoice.** Expected useful block collisions are at most \(\binom{k}{2}(4\ell-2)/q\). Setting that to 1 gives \(k^2\ell=q/2\) for large \(\ell\). With \(t=k\ell\) keys,
\[
\text{field cost}=k\,C_f+t\,C_x
\]
is minimized at \(\sqrt{2}\,\sqrt{C_f C_x}\,\sqrt{q}\). At \(s=1\), \(\sqrt{(6)(3.5)}=\sqrt{21}\) and the product is about \(6.5\sqrt{q}\), against \(3.5\sqrt{q}\) for balanced x-only BSGS. If every step, including the mix, were priced at \(C_x\), the same offset count would still cost about \(1.41\,C_x\sqrt{q}\). Memory is \(\Theta(t)=\Theta(\sqrt{q})\) stored abscissae if every cross offset is hashed, so the comparator is BSGS, not low-memory rho. This is not a fixed GWZ or grumpy-giant layout: those keep entire families on a few public strides and never pay a remixed centre. It is also not the H024 fixed-progression ceiling; that ceiling does not apply to hash-chosen centres, and this is the direct count for those centres.

**Low memory.** Replacing the full table by distinguished points multiplies the waiting time by a positive power of \(1/\theta\) and does not turn the offset count into a random-mapping collision. The BLS constant is not claimed for this clocked leg.

**Unsupported assumption.** That \(\ell\) points on one progression behave as \(\ell\) independent quotient samples, which would replace \(k^2\ell/q\) by \((k\ell)^2/q\) and falsely suggest a win.

**Cheapest falsifier.** Integer, not experimental: from \(C_i-C_m=[\delta]D\) deduce \(P_{i,j+\delta}=P_{m,j}\) for every in-range index. Count offsets, then compare \(\sqrt{2}\sqrt{C_f C_x}\) with \(2.5{+}s\). The inequality already rejects the schedule.

## Wave report

Best supported estimate: exponent \(1/2\), with negation rho at about \(0.886\sqrt{q}\) batched additions of \(5M{+}S\) below roughly \(0.19\sqrt{q}\) stored abscissae, and \((b+q/(4b))(2.5M{+}S)\) above that. These are conditional field-arithmetic comparators, not measured runtimes.

Verified improvement: **NONE**.

Hypothesis under test: none retained. The three schedules fail on eligible-pair price, fiber recovery, and AP offset dependence respectively.

Evidence for a gain: none. Evidence against: the invoices above. A second independent negation class per round would need an effective field cost strictly below \((2.5{+}s)/\sqrt{\pi/4}\) per class to undercut balanced x-only BSGS before nulls and detection. At \(s=1\) that gate is about \(3.95M\). The conjugate split costs \(3{+}s\) per class in the most generous reading and \(6{+}2s\) per main step in the probe reading. Both sit above the gate. The gate is an admission test for this sample type, not a lower bound on other coordinate methods.

Next conclusion-changing object: one public successor on canonical states of size at most the negation quotient, with an affine label update, a nonzero coefficient of \(k\), and either an independent eligible sample cheaper than that gate or a block whose useful events are not the \(O(\ell)\) offsets of a repeated jump. Only that object warrants a bounded synthetic check.

No source or model failure occurred. Prior-art distinction uses the accepted H043, H040, and H024 records plus search copies of Wang–Zhang (ePrint 2011/008), the Bos–Kleinjung–Lenstra negation slides, and Galbraith–Ruprai (ePrint 2010/615, an interval method, not a full-group improvement). No new full PDF was opened in this pass. The Möbius partner is derived from the degree-2 formula already recorded in the H043 full-work disposition.
