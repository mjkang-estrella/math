# H046 raw Grok noncanonical walk report — UNACCEPTED

2026-10-09 UTC. Provider grok / grok-4.7.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h046-noncanonical-geometry-grok-20261009-r1`.
Terminal completed, no pending children. This is raw proposal evidence, not
an accepted experiment or verified gain. Independent mathematical and full-cost
reviews are required; root identified signed-label, stopping-statistic and
low-memory-detection problems on initial reading. H034 cap remains untouched.

The working full-secret cost is still exponent \(1/2\), with verified gain **NONE**: Bernstein–Lange–Schwabe negation rho at low memory, and x-only interleaved negation BSGS at square-root memory. Pair counts are not stopping times. The three schedules below are low-memory functional walks whose win condition is measured useful-stopping work.

Baselines used as comparators, not as discoveries: negation rho, heuristic \((1+o(1))\sqrt{\pi q/4}\approx 0.886\sqrt{q}\) iterations on the negation quotient at one batched affine add \(5M{+}S\) per step (cryptojedi `negation-20110102.pdf` §§1–3; fruitless-cycle overhead separate); high-memory comparator, if a schedule stores \(\Theta(\sqrt{q})\) keys, Galbraith–Wang–Zhang interleaved negation BSGS at about \(0.943\sqrt{q}\) keys and limiting \(2.5M{+}S\) per abscissa. Canonical representative \(\kappa\) includes the sign \(\varepsilon\in\{\pm1\}\) in the label. A repeated canonical abscissa of two labelled visits is the equation \((b_t-b_s)k=a_s-a_t\). It is useful only when \(b_t\neq b_s\).

Affine doubling and addition are the EFD short-Weierstrass formulas
\[
x(2P)=\frac{(3x^2+a)^2}{(2y)^2}-2x,\qquad
x(P{+}Q)=\Bigl(\frac{y_Q-y_P}{x_Q-x_P}\Bigr)^2-x_P-x_Q.
\]
A doubling is counted separately from an add. Provisional price \(C_{\mathrm{dbl}}=5M{+}2S\) is only for the break-even arithmetic below; an EFD batch audit can replace it. Jump table: \(r=16\) fixed multiples of \(G\). Setup \(O(r)\) adds. No training and no \(k\)-dependent advice.

---

### Card 1 — Lazy low-\(x\) gate, translate or double

**Operation.** State is one canonical point \(W=aG+bQ\). Start at \(W=\kappa(Q)\), \((a,b)=(0,1)\).

1. Always compute \(A=\kappa(W+J_{h(x(W))})\) and the translated label \(\varepsilon(a+j,b)\).
2. If the integer representative of \(x(A)\) is \(<p/2\), set \(W\leftarrow A\).
3. Otherwise compute \(D=\kappa([2]W)\) from the old \(W\), with label \(\varepsilon'(2a,2b)\), and keep whichever of \(A,D\) has the smaller integer \(x\).

The fallback replaces the state. This is a different map from thinning a finished walk. The scalar maps are \(m\mapsto m+j\) or \(m\mapsto 2m\), not a hash choice of one pre-selected branch and not an always-on evaluation of both branches.

**Nulls.** After signs, \(|b|=2^v\). A repeat is null when the doubling counts match, and useful when they differ:
\[
(2^{v_t}-2^{v_s})k=a_s-a_t.
\]
Any nonzero coefficient is invertible because \(q\) is prime. Verify \(kG=Q\) once.

**Why a gain is possible.** Let \(\alpha\) be the fraction of steps that double, and let \(\lambda\) be the collision intensity of the canonical abscissa relative to the uniform negation quotient (\(\lambda=1\) for a random map; uniform-on-a-half has \(\lambda=2\)). Mean step price \(C_{\mathrm{add}}+\alpha C_{\mathrm{dbl}}\). Against rho this needs
\[
\lambda>\bigl(1+\alpha C_{\mathrm{dbl}}/C_{\mathrm{add}}\bigr)^2.
\]
At \(\alpha=1/2\) and \(C_{\mathrm{dbl}}\approx C_{\mathrm{add}}\) the threshold is \(\lambda>2.25\). A uniform half only reaches \(2\), so a win requires the doubling branch to concentrate harder than that cap. Iid min-of-two intensity \(4/3\) is the wrong law for this gate and is not used.

**Memory and stopping.** Same distinguished-point budget as the rho baseline, memory \(o(\sqrt{q})\), overhead charged on both sides. Ring buffer of the last \(8\) abscissae: a null repeat triggers one escape \(W\leftarrow\kappa(W+G^\star)\) with \(G^\star\) outside the jump table, and the escape is counted. Stop at the first useful repeat or at cap \(4\times 0.886\sqrt{q}\) steps. Failures cost the cap. Do not turn the hit count into a Rayleigh time.

**Prior art.** Pollard’s iterator is one branch among \(+g\), \(+h\), and squaring (Miller–Venkatesan, `math/0603727`, (1.1)). Teske \(r\)-adding and BLS negation walks are the baseline. H031 always paid for two translates. The conditional double, the weight null, and the \(\lambda>2.25\) contract are the new pieces.

**Assumption.** Elliptic dependence of \(x(W+J)\) and \(x([2]W)\) pushes \(\lambda\) past \(2.25\), and the useful-weight fraction stays bounded away from \(0\), at the same ratio on larger \(q\).

**Falsifier.** One ordinary prime-order curve, \(q\approx 2^{16}\), \(8\) seeds. Median verified-success work, capped trials at the cap, priced with adds and doubles separate. Kill if that median is \(\ge 0.886\sqrt{q}\,(5{+}s)\) at \(s=1\). A pass only clears the cheap kill.

---

### Card 2 — Lazy low-\(x\) gate, \(+G\) or \(+Q\)

**Operation.** Same skeleton as Card 1, with the second branch \(W+Q\) instead of \([2]W\). Start \((a,b)=(0,1)\).

1. Always compute \(A=\kappa(W+G)\), label \(\varepsilon(a+1,b)\).
2. If \(x(A)<p/2\) as an integer, keep \(A\).
3. Otherwise compute \(B=\kappa(W+Q)\), label \(\varepsilon'(a,b+1)\), and keep the smaller integer \(x\).

Scalar bookkeeping is \((a,b)\mapsto\varepsilon(a+1,b)\) or \(\varepsilon'(a,b+1)\). Both steps are ordinary adds. Mean cost \((1+\alpha)C_{\mathrm{add}}\) with \(\alpha=P(\text{second add})\).

**Nulls.** Signs included, \(b_t-b_s=0\) is null (same net \(Q\)-count). A canonical repeat with \(b_t\neq b_s\) is
\[
(b_t-b_s)k=a_s-a_t.
\]
A pure \(G\)-translate walk would have \(b\equiv 1\) and every self-repeat would be \(0=0\). The \(+Q\) branch is what makes \(b\) move.

**Prediction.** Same shape as Card 1 with \(C_{\mathrm{dbl}}\) removed: need \(\lambda>(1+\alpha)^2\). At \(\alpha=1/2\) that is again \(\lambda>2.25\), above the uniform-half value \(2\). Win condition is measured stopping work, not \(\binom{T}{2}/q\).

**Memory and stopping.** Identical DP contract, cap, escape, and verification as Card 1. Escapes that add an extra \(G\) increment \(a\) and must be logged or they corrupt \(b_t-b_s\).

**Prior art.** Two always-evaluated \(G\)-translates are the H031 schedule and would be null from a \(Q\)-start. Pollard’s \(+G\) / \(+Q\) split is one branch per step, chosen by a partition of the current point, at one add. Here the second add is conditional on the abscissa of the first result, and both images are compared only when that happens.

**Assumption.** The joint law of \(x(W+G)\) and \(x(W+Q)\) concentrates past \(\lambda=2.25\), and unequal \(Q\)-counts are a positive fraction of repeats.

**Falsifier.** Same \(2^{16}\) median-work kill as Card 1, with the null class defined by \(b_t=b_s\). Surplus repeats at equal \(Q\)-count are not a win.

---

### Card 3 — Translate, then a parity fold

**Operation.** One branch per step, chosen after the translate, with no second parent.

1. Always set \(W\leftarrow\kappa(W+J_{h(x(W))})\), label \(\varepsilon(a+j,b)\).
2. If the new integer \(x\) is odd, replace \(W\leftarrow\kappa([2]W)\), label \(\varepsilon'(2a,2b)\).

Scalar maps: \(m\mapsto m+j\), or \(m\mapsto 2(m+j)\). The doubling edge is the one Miller–Venkatesan isolate as the source of expansion in the Pollard digraph (`math/0603727`, Proposition 2: without squaring, mixing is exponential in \(\log n\)). Here it is applied to the translated point on a parity predicate, on about half the steps if \(x\) is balanced, at extra cost \(\alpha C_{\mathrm{dbl}}\).

**Nulls.** \(|b|=2^v\) after signs. Useful iff the two visits have different fold counts:
\[
\bigl(2^{v_t}(a\text{-prefix}_t)-2^{v_s}(a\text{-prefix}_s)\bigr)
\]
is the ordinary rearranged form of \(b_t\neq b_s\). Same-weight repeats are surplus even when the abscissae match.

**Prediction.** Mean price \(C_{\mathrm{add}}+\alpha C_{\mathrm{dbl}}\). A random-map iteration count \(0.886\sqrt{q}\) loses at \(\alpha\approx 1/2\). A win requires the useful walk length
\[
E[T_{\mathrm{useful}}]\le 0.886\sqrt{q}\cdot\frac{C_{\mathrm{add}}}{C_{\mathrm{add}}+\alpha C_{\mathrm{dbl}}},
\]
about \(0.59\sqrt{q}\) iterations if \(\alpha=1/2\) and \(C_{\mathrm{dbl}}\approx C_{\mathrm{add}}\). That is a real shrinkage of the image relative to a random function, not a rescaling of pair counts.

**Memory and stopping.** Same low-memory DP contract and cap as Card 1. Parity folds can create short cycles; the length-\(8\) escape applies and is charged. Each escape is a \(+G^\star\) and does not silently double.

**Prior art.** Pollard squares on a partition of the current group element and does not translate first. BLS records the negation \(2\)-cycle for a negating additive step; that \(\Theta(1/r)\) formula is for their hash increment, and this parity fold needs its own escape count. Conjugate chord images are a second output of one denominator; this fold is a later doubling of an already accepted translate.

**Assumption.** The parity fold shortens useful return enough to clear the \(0.59\sqrt{q}\) line, and same-weight repeats do not absorb the early collisions.

**Falsifier.** Same median-work census. Kill immediately if the median number of useful stops with distinct \(v\) is \(0\) while raw abscissa repeats are plentiful: that is surplus, not a solve.

---

### Strongest potential test

Run Card 1 on one ordinary prime-order curve at \(q\approx 2^{16}\), eight seeds, cap \(4\times 0.886\sqrt{q}\) steps. Instrument every canonical repeat into three buckets: distinct doubling weight, equal weight, and escape. Decision statistic: median verified-success work at \(s=1\), failures at the cap, doubles priced \(5M{+}2S\). Compare with \(0.886\sqrt{q}\,(5{+}s)\).

Equal-weight repeats with a small median do not count as a gain. A median below the baseline only clears this kill; the same census at \(2^{20}\) and \(2^{24}\) is required before any large-\(q\) claim. Cards 2 and 3 use the same harness with their own null predicate. No Rayleigh fit.

### Wave report

- Best supported estimate: exponent \(1/2\), negation rho below about \(0.19\sqrt{q}\) stored abscissae, x-only interleaved negation BSGS at square-root memory. No tighter bound.
- Verified improvement: **NONE**.
- Hypothesis under test: none retained. The three gates are unrun; each wins only if measured useful-stopping work beats \(0.886\sqrt{q}\,(5{+}s)\).
- Evidence for a gain: the lazy gate can in principle pass the half-uniform cap \(\lambda=2\) if the fallback concentrates. Evidence against: iid overlap stops at \(4/3\) or at \(\lambda=2\), both short of \(2.25\), and a parity fold at \(\alpha\approx 1/2\) needs a map shorter than a random function.
- Next conclusion-changing check: the \(2^{16}\) median-work census for Card 1, with the weight split above.
