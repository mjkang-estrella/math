Provider: acpRegistry_factory_droid / claude-fable-5.1
TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h019-learned-operators-fable-20261008-r1
Status: completed; no pending children. Raw unendorsed report; independent review pending. Root identified counterexamples to its universal information-floor and autocorrelation claims.

# H019 information-lens report (Factory Fable 5.1, read-only)

**Verdict: no new candidate observable.** Verified improvement remains NONE. Instead of padding to 3–5 cards, I deliver (A) a sharpened admissibility map that states exactly which cheap observables are closed by theorem and which are merely unexplored, (B) an inventory of the "Weil-silent" families with their actual status, and (C) two concrete paper tools with exact cost accounting. Nothing here is a numerical result, authorizes a run, or treats the completed one-fixture BM diagnostic (p 8191, q 8053, four features, L 64) as asymptotic.

Scope respected: no runs, edits, children, commits, wallet targeting. I did not read other live proposers' outputs. Read: RESEARCH_LOOP, RESEARCH_TEAM, STATE, H017 information/SP3/coordinate dispositions, H018 operators/raw/BM v1–v2/admissions, H013 MCL/group-action/coordinate/algebra, H014 screen, H016 mixed-modulus, H011 fiber screen, H005, H003 EDS/lift/noisy, H002 learning and arithmetic cards.

## A. Admissibility map for a cheap public observable

Setting: $E/\mathbb F_p$, $\#E = q$ prime, $q \approx p$, $Q = kG$. A "cheap observable" is $h(r(P_1,\dots,P_t))$ with $P_i = [c_i]P + [t_i]G$ for $O(1)$ public $c_i, t_i$, $r$ a rational function on $E^t$ of degree $d$, and $h:\mathbb F_p \to \mathbb C$, $|h| \le 1$, with additive Fourier $\ell_1$ norm $L_1(h)$ over $\mathbb Z_p$. The target is a scalar predicate $\tau(k)$ with $\ell_1$ norm $L_1(\tau)$ over $\mathbb Z_q$ (MSB/interval predicates have $L_1 = O(\log q)$).

**A1. Required-signal floor (decoder-independent for binary predicates).** A binary predictor with advantage $\varepsilon$ carries at most $\approx 3\varepsilon^2$ bits about $\tau(k)$ per query (mutual information of a biased bit), so any decoder needs $\ge \log_2 q/(3\varepsilon^2)$ queries. With per-query cost $c_f \ge 1$ group operation, beating $q^{1/2}$ requires
$$\varepsilon \;\gtrsim\; q^{-1/4}\,(c_f \log q)^{1/2}.$$
This floor does not depend on which decoder is used. The loop's accepted decoder (H003 Fourier recovery) needs $\varepsilon^{-6}$, i.e. $\beta<1/12$; the Håstad–Näslund chosen-multiplier HNP result states a polynomial-time reduction for *any* single bit of $ax \bmod N$ in general cyclic groups (ACM abstract fetched; the PDF is binary and I did not read the exponent). If its dependence is $\varepsilon^{-2}\,\mathrm{polylog}$ as in the ACGS lineage, the usable region widens to $\beta<1/4$, matching the floor. Either way $\beta<1/4$ is necessary; nothing below the floor can help, whatever the decoder. Combining $m$ predicates of advantage $\varepsilon$ each only acts like one of advantage $\varepsilon\sqrt m$; with $m \le \log q$ this never changes an exponent.

**A2. Weil-class ceiling with explicit $\ell_1$ factors.** Expanding $h$ and $\tau$ in characters and applying the Kohel–Shparlinski-type bound $|\sum_{P} \chi(P)\,\psi(r(P))| \le 2d\sqrt p$ for group characters $\chi$ of $E(\mathbb F_p)$ (cited from memory; the loop's H013 MCL record and H018 raw N3 used the same family of bounds) gives
$$\bigl|\mathbb E_k\, h(r(kG))\,\overline{\tau(k)}\bigr| \;\le\; 2d\, L_1(h)\, L_1(\tau)\,\sqrt p/q .$$
New lemma (paper, checkable in ten lines): **every individual bit of the integer representative has small $\ell_1$.** For $B_j(\tilde x) = (-1)^{\lfloor \tilde x/2^j\rfloor}$ on $[0,p)$: it is a period-$T=2^{j+1}$ square wave, whose $\mathbb Z_T$ expansion has $\ell_1 = \Theta(\log T)$ (coefficients $2/(T|\sin(\pi r/T)|)$ at odd $r$); transferring to $\mathbb Z_p$ through the Dirichlet kernel $|D_p(\theta)| \le \min(1, 1/(2p\|\theta\|))$ at the $p$ points $r/T - a/p$ costs a factor $\le 4 + 2\ln p$. Hence $L_1(B_j) = O((j+1)\log p) = O(\log^2 p)$, and $L_1$ of any product of $s$ bits is $O(\log^{2s} p)$.

Consequences, all closed by theorem for **additive** scalar targets (bits/intervals of $k$):

| Observable class | $L_1(h)$ | Ceiling $\varepsilon$ | vs floor $q^{-1/4}$ |
|---|---|---|---|
| sign($y$), intervals, MSB of $\tilde x$ | $O(\log p)$ | $\tilde O(d\,q^{-1/2})$ | closed |
| any single bit $j$ of $\tilde x$ or $\tilde y$ | $O(\log^2 p)$ | $\tilde O(d\,q^{-1/2})$ | closed |
| products of $O(1)$ bits, residues mod small $m$ | polylog | $\tilde O(d\,q^{-1/2})$ | closed |
| multiplicative characters $\chi_p(r(P))$ (Chen / Shparlinski–Stange mixed bound, H003) | n/a | $O(d\sqrt p/q)$ | closed |
| any of the above on $O(1)$ affine-combination points | polylog | $\tilde O(d\,q^{-1/2})$ | closed |

Nonconstancy of the composite (not Artin–Schreier) must be checked per feature; degree grows with $c_i^2$ but stays polynomial for bounded multipliers.

**A3. Spectral concentration is forbidden.** By Parseval $\sum_a |\hat h'(a)|^2 \le 1$ for $h'(k) = h(r(kG))$, while A2 caps each $|\hat h'(a)| \le \tilde O(d q^{-1/2})$. A spectral decoder (phase estimation, HNP on heavy frequencies) that needs energy $E_S = \sum_{a\in S}|\hat h'(a)|^2 \ge q^{-1/2}\log q$ (from A1 applied per frequency) must therefore use $|S| \ge \tilde\Omega(q^{1/2})$ frequencies, i.e. square-root work. The information is present (full energy 1) but flat; flat-spectrum extraction is a dictionary/BSGS. This excludes spectral decoders on Weil-class features; it does not exclude non-spectral cheap extraction, which no theorem addresses.

**A4. The one proof gap inside the Weil class: multiplicative scalar targets.** Characters $\chi(k)$ of $\mathbb Z_q^*$ are not group characters of $E(\mathbb F_p)$; the proven ceiling (Ahmadi–Shparlinski, read by root in H013) is only $O(q^{-1/12}\log^{1/3} q)$, and the Bhakta twists cited in H008 keep exponent $1/12$. With the MCL route's accepted cost $m^2/\rho^2 + \sqrt{q/m}$ (H016), a gain needs $\rho > q^{\delta - 1/4}$ at $m = q^\delta$, so the formally open window is $\delta < 1/6$, $1/12 < \beta < 1/4$. This is a gap in bounds, not evidence: the generic expectation is $\rho \sim q^{-1/2}$, H014's tiny data are consistent with that, and no mechanism makes any algebraic $f$ dilation-covariant with a $\mathbb Z_q^*$ phase. The cheapest closure is analytic: an improved bilinear bound for $\sum_n \chi(n)\psi(r(nG))$ with exponent $\ge 1/4$. I could not find one in the sources accessible to me.

**Net statement.** Within the Weil class, additive targets are closed by a factor $q^{1/4}$ (ceiling $q^{-1/2}$ vs floor $q^{-1/4}$); only the multiplicative-target window above remains formally open, with no positive reason. Any cheap useful observable must therefore be *non-algebraic in the integer representation* or sit in that window.

## B. Weil-silent inventory (what A2 does not cover)

| Family | Why it escapes A2 | Reason to expect structure | Status / cheapest paper screen |
|---|---|---|---|
| **F1. $p$-adic second coordinate** (torsion-lift digit $T(P) = [q^{-1}][q]\tilde P$, $\kappa$ of H016, Hensel digit of H010) | In Witt coordinates the $\mathbb Z/p^2$ group law is polynomial over $\mathbb F_p$ but the second Witt component has **degree $p$** (Witt addition polynomial $S_1$); Weil is vacuous | Genuine group-theoretic meaning: $T$ is a quasi-homomorphism, $T(nG) = nT(G) + D(n)$ with $D$ the cumulative lift defect (this is exactly H002 A2's $g([k]P) = k\,g(P) - C_k$) | Registered lane (H002 A2, H003 lift-section, H010 cards); I do not reopen it. New framing only: *all* scalar information in $T$ sits in $D(k)$; a predictor of $D$ with advantage above the A1 floor is itself an ECDLP solver, and H003's small-image dictionary bound is the right screen for "concentrated $D$". No changed paid operator from me. |
| **F2. Digit functions of many bits of $\tilde x$** (digit-sum parity / Thue–Morse $t(\tilde x)$) | $L_1(t) \approx p^{0.79}$ (Gelfond-type bound), so A2 is vacuous | None. Carries in the mod-$p$ group law scramble binary digits; no mechanism | **Primary source read:** Dartyge–Sárközy 2013 (HAL full text) defines digits as coordinates in an $\mathbb F_p$-basis of $\mathbb F_{p^r}$, so their digit sum is an $\mathbb F_p$-linear functional and their Theorem 1.2 is Weil; it does **not** cover binary digits of residues in a prime field. Mauduit–Rivat/Drmota–Mauduit–Rivat are integer-polynomial results, inapplicable. So F2 is genuinely open, but a tiny-fixture null would be uninformative and a positive only a candidate; no run recommended. |
| **F3. Multiplicative-order / Fermat-quotient statistics of $\tilde x$** | non-algebraic over $\mathbb F_p$; $q_p(ab) = q_p(a)+q_p(b)$ only before reduction | None for EC sequences | Shparlinski 2011 abstract (fetched): Heath-Brown's bound for consecutive Fermat quotients is nontrivial only for $N \ge p^{1/2+\epsilon}$ and concerns integers $n$, not $x(nG)$. No transfer, no mechanism. Not carded. |
| **F4. Learned Boolean circuits on bits of $(\tilde x,\tilde y)$** | $L_1$ of a depth-2 circuit on $m$ bits can reach $2^{m/2}$ | Only the hypothesis that MSB$(k)$ has a small circuit as a function of coordinates | See card C2: this *is* the small-circuit-ECDLP hypothesis via A1; training is a search over it with no prior. |

## C. Concrete paper tools

### C1. Label-free autocorrelation necessary condition (screen, not a solver)

*Operation.* For a proposed feature $h$ with $h'(n) = h(nG)$, define $A(\ell) = \mathbb E_n\, h'(n)\overline{h'(n+\ell)}$ and the Fejér sum $F_L = \sum_{|\ell|<L}(1-|\ell|/L)A(\ell) = \sum_a |\hat h'(a)|^2 K_L(a)$.
*Inequality.* If $h$ has correlation $\varepsilon$ with MSB$(k)$ (or any target supported on frequencies $|a| \le q/L$), then $|\hat h'(a_0)| \ge c\,\varepsilon$ at some such $a_0$ and $F_L \ge c^2\varepsilon^2 L/2$. So $\varepsilon \le \sqrt{2F_L/(c^2 L)}$.
*Why it matters.* $F_L$ needs **no labels and no secret**: sample $N$ random points, walk $L$ additions each, average. It is the exact necessary condition behind the H017 pair-predictor remark, stated with a constant.
*Cost and power.* $N L$ group additions. Standard error of $F_L$ is $\approx\sqrt{L/N}$, so detecting the threshold level $\varepsilon^2 L$ with $\varepsilon = q^{-1/4}$ needs $N \gtrsim 1/(\varepsilon^4 L)$, total work $\approx q$. Hence it is **not** cheaper than the problem at the threshold; it is cheap only for gross signals ($\varepsilon \ge q^{-1/8}$) on finite fixtures, where it halves the per-sample cost versus labelled sampling (additions instead of scalar multiplications). For algebraic $h$ it reproduces $\varepsilon \le \tilde O(\sqrt d\, q^{-1/4})$, weaker than A2.
*Unsupported assumption.* None; it is a theorem-level necessary condition. Its limitation is that passing it proves nothing.
*Decision.* Keep as a free pre-screen for any future non-algebraic feature (F2-type) before any labelled run; it does not itself justify a run.

### C2. Training as circuit search: the exact accounting

*Representation.* Input bits of $(\tilde x,\tilde y)$ of $P$ and of $O(1)$ affine-combination points; hypothesis class $\mathcal H$ of circuits/networks with $W$ parameters.
*Objective.* Advantage $\varepsilon$ on a fixed predicate $\tau(k)$ (MSB, a bit, or $\chi(k)$).
*Generalization.* Uniform convergence needs $N \gtrsim (W\log W + \log(1/\delta))/\varepsilon^2$ labelled samples; each label costs a scalar multiplication ($\approx\log q$ group ops). Validation alone of a threshold-level predictor ($\varepsilon = q^{-1/4}$) costs $N \ge q^{1/2}$ samples, i.e. square-root work before any use.
*Existence.* By A1 plus a polynomial bit decoder, a circuit of size $W$ with $\varepsilon \ge q^{-1/4+\delta}$ implies an ECDLP circuit of size $\tilde O(W q^{1/2-2\delta})$. So the hypothesis "training finds a useful feature" is equivalent, up to the decoder polynomial, to "ECDLP has a sub-square-root circuit on coordinate bits", searched over without a structural prior. Gradient methods are statistical-query learners; the loop already recorded Takhanov et al. as prior art on parity-type SQ hardness (H002), which is a limit on *generic learners*, not a coordinate impossibility.
*Unsupported assumption.* That such a circuit exists and is reachable by local search. No mathematical reason is known; all Weil-class members of $\mathcal H$ are excluded by A2.
*Cheapest falsifier.* None exists on paper beyond A2; a finite training failure rejects only that architecture/size. *Decision:* no training run is justified; the loop's earlier refusals (H002 L1/L2, H013 Stage B) stand with this sharper reason.

## D. Rejected without a card (one line each)

- Fourier-phase + HNP decoder on heavy coefficients: a decoder contingent on a missing signal; excluded by A3 for Weil-class features.
- Formal-group linearization ($z([u]P) \approx u z(P)$): only formal; over $\mathbb F_p$ it is a degree-$u^2$ rational map, N2-affine on logs.
- Window synchronization / sliding-window sketches of $x(Q+jG)$: distinct windows are Weil-independent; any index is the landmark dictionary $L + q/L$ (H013).
- Low-entropy or learned iteration functions that "concentrate" the walk: image shrinkage by factor $r$ requires $r$ distinct computable step counts, which is the distinguished-point walk at cost $r$ per landing; no gain.
- Twist/Kummer-line permutation $x \mapsto x([n]\cdot)$ on $E \cup E'$: unobservable without $n$; twist order supplies nothing about $k$.
- Genus-2 point counts of $y^2 = f(x)(x - x_Q)$, Schoof-type auxiliary families: Deligne-type $p^{-1/2}$ correlation, inside A2's ceiling.
- Partial-CDH operations on a cheaply recognizable subset: random self-reducibility makes any $q^{-\delta}$-fraction CDH an ECDLP solver via Maurer–Wolf; no such cheap operation is known (H018 N2 already states the dichotomy).

## E. Five-item summary

1. **Best supported work:** classical square-root reference with known automorphisms and all setup/memory/failure/verification charged; unchanged.
2. **Verified improvement:** NONE.
3. **Hypothesis offered:** none positive. Offered instead: the admissibility map (A1–A4) with the new bit-$\ell_1$ lemma, the Weil-silent inventory, and the label-free necessary condition C1.
4. **Evidence:** paper derivations only. A2 closes all polylog-$\ell_1$ coordinate features for additive scalar targets by a factor $q^{1/4}$ below the decoder-independent floor; A3 closes spectral decoders on Weil-class features; A4 identifies the sole formal gap (multiplicative targets, exponent 1/12 vs 1/4) with no mechanism. F2 is confirmed open by reading Dartyge–Sárközy (their digits are $\mathbb F_p$-linear). Nothing here is Lean-proved; the bit-$\ell_1$ lemma and the A2 composition should get an independent check before being cited in a disposition.
5. **Next conclusion-changing step:** (i) independent check of the bit-$\ell_1$ lemma and A2/A3 constants (cheap, paper); (ii) if any proposer later names a non-algebraic feature (F1/F2 type), apply C1 before any labelled fixture; (iii) the only theorem-level opening worth analytic effort is improving the multiplicative-twist exponent in A4 toward 1/4, which would close the last Weil-class window. No feature sweep, training engine, or further BM fixture is justified by this report.

**Source access:** Dartyge–Sárközy 2013 full text read (HAL); Håstad–Näslund JACM 2004 abstract read, PDF not parsed (binary); Shparlinski 2011 Fermat-quotient abstract read; Kohel–Shparlinski 2000 and Gelfond's Thue–Morse bound cited from memory and flagged; Ahmadi–Shparlinski and Chen/Shparlinski–Stange relied on through the loop's existing root-read records.
