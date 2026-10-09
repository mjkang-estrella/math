# H044 raw Factory Fable information report — UNACCEPTED

2026-10-09 UTC. Provider acpRegistry_factory_droid / claude-fable-5.1.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h044-information-constructions-fable-20261009-r1`.
Terminal result retrieved via task_status. All proposed closures and decoder
claims await independent review. Usage footer is unverified provider metadata,
not research evidence or a measured cost of an ECDLP algorithm.

# H044 independent information-lens pass: no surviving algorithm; two decoder-class closures and one named open operation

**Role and conduct.** Factory `claude-fable-5.1`, read-only in `/home/mj-kang/Documents/Dev/math/dlp-research`. Read RESEARCH_LOOP.md, RESEARCH_TEAM.md, STATE.md, and the accepted dispositions H042-nonlinear, H043-trace-scalar, H043-briefs, H041/H040-information, H013-MCL, H004-compact-algebra, H026-eds-reconciliation, H003-orbit-invariant, plus the H042 Fable raw. I did **not** open `H044-independent-briefs.md` (it holds other proposers' lenses). No runs, imports, edits, children, commits; H034 cap untouched; H006/H038 Farey and H039 hybrid untouched. One fresh primary read this pass: Shparlinski–Stange, *Character sums with division polynomials*, arXiv:0912.5246v4 (HTML, read in full; Lemmas 1, 2, 4, 5, Theorem 6, Section 6). No source or model failures.

**Verdict.** Verified improvement remains **NONE**; best supported exponent 1/2. I examined four genuinely different constructions. None survives its own invoice. The pass yields two decoder-class closure lemmas that are not in the record and that consolidate three recorded "openings" into one, plus one precisely named public operation that remains outside every proved bound (with no positive rationale). I am not submitting a card.

## Deduplication: what I did not resubmit

The record already holds the EDS perfectly-periodic normalization and multiplicative-lift circularity (Lauter–Stange; H002/H022/H024/H026), the Kummer collapse of Miller/EDS values to two-point odd support (H004 L0, H042 lemma), power-residue characters of φ (H024 Card A), H-invariant orbit labels and elliptic periods (H003 D1–D3), dilation-product characters (H004 M1), the MCL coset decoder (H013), the autocorrelation-lag decoder (H041), and the Prym trace operator (H042/H043). I checked each of my initial ideas against these before writing; the EDS/Miller multiplicative-lift route I derived independently reproduces H024/H026 exactly and is not repeated below.

## L1. Second-order (pair-correlation) decoders are dominated by first-order Fourier gates

*Setting.* $F(n)=f([n]G)$, $|F|\le 1$. Additive coefficients $c_a=q^{-1}\sum_n F(n)e(-an/q)$; centered autocorrelation $\tilde R(\tau)=q^{-1}\sum_n F(n)\overline{F(n+\tau)}-|c_0|^2=\sum_{a\ne0}|c_a|^2e(a\tau/q)$.

*Lemma.* Parseval over $\tau$ gives
$$\sum_\tau|\tilde R(\tau)|^2=q\sum_{a\ne0}|c_a|^4\le q\cdot\max_{a\ne0}|c_a|^2\cdot\sum_{a\ne0}|c_a|^2\le q\max_{a\ne0}|c_a|^2 .$$
Hence any public peak list of $t$ nonzero lags with $|\tilde R|\ge\varepsilon$ satisfies $t\varepsilon^2\le q\max_{a\ne0}|c_a|^2$. The H041 decoder's own idealized gain criterion $t\varepsilon^2>\sqrt q$ therefore forces $\max_{a\ne0}|c_a|>q^{-1/4}$, which is exactly the H040 phase-decoder gate $b<1/4$. The converse fails (a single coefficient $\varepsilon$ gives lag peaks of only $\varepsilon^2$), so the lag route is strictly weaker.

*Multiplicative version.* With $\hat c_\chi=(q-1)^{-1}\sum_{n\ne0}F(n)\overline{\chi(n)}$ and $R^\times(u)=\sum_\chi|\hat c_\chi|^2\chi(u)$, the same argument gives $t\varepsilon^2\le(q-1)\max_{\chi\ne1}|\hat c_\chi|^2$. The mixed dilation query $\mathbb E_a f([a]Q)\overline{f([ac]G)}=R^\times(k/c)$ (substitute $n=ac$) with random $c$ hitting a public peak list costs $q/(t\varepsilon^2)$ trials-times-samples, so a gain again needs a single multiplicative coefficient above $q^{-1/4}$: the recorded H013 MCL opening, where the only proved ceiling is Ahmadi–Shparlinski's $q^{-1/12}$.

*Consequence.* H041 (additive lags), H004 M1/H042 mixed dilations, and H040/H013 single-coefficient phase/coset decoders are one opening, not three. Future second-order proposals need not be separately reviewed; they need a first-order coefficient $\ge q^{-1/4}$ plus its discovery cost. This does not touch third-order statistics (see L2) or non-algebraic features.

## L2. Quadratic-phase ("chirp") decoder: a genuinely new decoder shape, closed for bounded degree, open for cheap high-degree features

*Public operations.* Suppose public $(\alpha,\beta)$, $\alpha\ne0$, with $S(\alpha,\beta)=q^{-1}\sum_nF(n)e(-(\alpha n^2+\beta n)/q)$, $|S|=\varepsilon$. For $d=0,\dots,N-1$ compute $F(k+d)=f(Q+[d]G)$ (one addition each) and $y_d=F(k+d)e(-(\alpha d^2+\beta d)/q)$. Expanding $\alpha(k+d)^2$, $y_d$ equals the $S$-summand at $n=k+d$ times a fixed unit phase times $e(2\alpha kd/q)$. So a length-$N$ DFT of $(y_d)$ shows a tone at frequency $\omega=2\alpha k$ of amplitude about $\varepsilon N$ against noise $\sqrt N$, resolving $\omega$ to width $q/N$, i.e. $k$ to an arithmetic progression of length $q/N$ with public difference $(2\alpha)^{-1}$. BSGS on that progression costs $\sqrt{q/N}$.

*Conditional full work.* $N+\sqrt{q/N}+\text{verify}$, minimized at $N=q^{1/3}$: $\tilde O(q^{1/3})$ **if** (i) $\varepsilon\gg q^{-1/6}\sqrt{\log q}$, (ii) the mass of $S$ is spread over length-$N$ windows (local flatness, unproved, same gap as H004), (iii) $(\alpha,\beta)$ is public. Memory $N+\sqrt{q/N}$. Failures: DFT false peaks each cost one $\sqrt{q/N}$ BSGS, so the true tone must be among $O(1)$ top peaks. Discovery of $(\alpha,\beta)$ by sampling costs about $q^2\varepsilon^{-2}$ and is single-target prohibitive; only an analytic rule or many-target amortization on fixed $(E,G)$ could pay it. This is not range narrowing: the progression comes from a measured public phase, not from an assumed secret range.

*Closure for bounded degree (new).* Weyl differencing: $|qS|^2=\sum_\tau e(\cdot)\sum_nF(n)\overline{F(n+\tau)}e(2\alpha\tau n/q)$. For $\tau\ne0$ the inner sum is a Kohel–Shparlinski mixed sum (group character times additive or multiplicative character of $g\mp g\circ\tau_T$, degree $\le2d$, nonconstant under the H041 pole conditions; for Kummer use Shparlinski–Stange Lemma 4/5, bound $2\deg\sqrt p$ when not a square). Thus $|qS|^2\le q+(q-1)\cdot4d\sqrt p$ and
$$\varepsilon\le q^{-1/2}+2\sqrt d\,p^{1/4}q^{-1/2}\approx 2\sqrt d\;q^{-1/4}\quad(q\approx p).$$
Since $q^{-1/4}<q^{-1/6}$, condition (i) fails for every bounded-degree (or bounded Fourier-$L^1$) coordinate feature. Dilations do not escape: $F\circ[u]$ has $S'(\alpha,\beta)=S(\alpha u^{-2},\beta u^{-1})$, so $x\circ[n]$ for any $n$ has the same quadratic-spectrum magnitude multiset as $x$ (extends the H004 remark from linear to quadratic spectra). Homomorphic transport (H026) likewise.

*What stays open, named precisely.* Cheap features whose degree is not a dilation of a small one: $\psi_p(\Psi_n(Q))$ with $n>q^{1/12}$ (degree $(n^2-1)/2$, $O(\log n)$ evaluation), additive characters of Miller values $f_{n,G}(Q)$ or $f_{n,Q}(G)$ with $n>q^{1/6}$, and net values. For these the Weyl bound exceeds $q^{-1/6}$ and no other bound exists; Shparlinski–Stange Section 6 states explicitly that for additive characters of $\Psi_n$ "there is no natural analogue of (5) and thus our approach does not apply at all." Note $\Psi_n(Q)=\Psi_{nk}(G)\,\Psi_k(G)^{-n^2}$ (their Lemma 2), so these features are EDS terms at the dilated secret index under a quadratic-exponent mask, which is where a quadratic phase could in principle originate. I have no positive rationale; square-root cancellation is the generic expectation.

*Cheapest falsifiers.* Paper: a bound for $\sum_{P}\omega(P)\psi_p(\Psi_n(P))$ with $n>q^{1/12}$ below $q^{3/4}$ would close the slot (none known). Numerical (not run; for a future wave only): on one curve with $q\approx2^{16}$, compute the full quadratic spectrum $\max_{\alpha,\beta}|S|$ of $\psi_p(\Psi_n(Q))$ for a few $n\approx q^{1/4}$ against the random baseline $q^{-1/2}\sqrt{2\log q^2}$. A null kills only those $n$ and that size.

## M3. Learned relational operator: pairwise log comparator (examined, not carded)

*Construction.* Train $h(P_1,P_2)\in\{0,1\}$ to predict whether the canonical integer log of $P_1$ is smaller than that of $P_2$. Train distribution: independent uniform known scalars in $[0,q)$, points by scalar multiplication (paid, no fixed-base table unless charged). Test: disjoint uniform pairs, permutation-label control, advantage $\varepsilon$ with $\pm N_v^{-1/2}$ confidence. *Extraction:* binary search on $[0,q)$ with pivots $[j]G$; each comparison re-randomized by translating both points by $[d]G$, which preserves order except on wraparound (probability $|n_1-n_2|/q$, small at fine scales, large at the first few coarse pivots, where chosen-multiplier rerandomization à la Håstad–Näslund must be used instead); $O(\varepsilon^{-2}\log q\log(\log q/\delta))$ comparisons, one addition each.

*Why it does not survive.* The extraction is itself a reduction: any comparator with noticeable advantage solves ECDLP, so the target is hard-core-equivalent, like the H042 D bit predictor. This is the same "unavailable bias" in a two-point relational form; the only change is the extraction (translation rerandomization instead of chosen multipliers) and an explicit distribution-shift analysis. It supplies no mechanism for advantage, so no invoice can be priced beyond the template. The learned lens therefore yields no changed construction: every learnable target is either a function of $Q$ alone (computable, uninformative) or hard-core-equivalent via its own extraction.

## M4. Dilation self-correlation (examined; absorbed by L1)

$\mathbb E_a f([a]Q)\overline{f([ac]G)}=R^\times(k/c)$ with large minimal-representative lags escapes the degree bounds (H004 M1 regime) but, by L1, any usable peak structure implies a single multiplicative coefficient $\ge q^{-1/4}$, i.e. the H013 opening with its $q^{-1/12}$ ceiling and no construction. Not a new opening.

## Mandatory items

- Best supported complexity: generic square-root with known automorphism constants; no change.
- Verified improvement: NONE.
- Hypothesis examined: that a public nonlinear operator admits a full-range scalar decoder below $\sqrt q$ via second-order, quadratic-phase, or learned-relational extraction.
- Evidence: L1 and L2 close second-order and quadratic-phase decoders for all bounded-degree/bounded-$L^1$ coordinate features and all their dilations and homomorphic transports; the learned-relational target is hard-core-equivalent. The quadratic-phase route remains open only for cheap high-degree non-dilation features (EDS terms, Miller/net values), where the primary source confirms no bound exists and I have no positive rationale.
- Next conclusion-changing analysis: a proved bound on additive-character sums of $\Psi_n(P)$ for $n>q^{1/12}$ (closes the slot), or an analytic rule producing a quadratic index phase from an EDS mask (would make L2's conditional $q^{1/3}$ schedule testable). Neither is a generic infrastructure task; no experiment is requested now.

Items worth retaining for the record, subject to independent review: the L1 domination lemma (additive and multiplicative), the Weyl-differencing bound $\varepsilon\le 2\sqrt d\,q^{-1/4}$ and the dilation-invariance of quadratic spectra, and the Shparlinski–Stange Section 6 citation scoping the open additive case.

---
*Factory usage — local bridge. This turn: 2,213,165 tokens · ≈4,096,864 Factory credits. Saved session total: 2,213,165 tokens · ≈4,096,864 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
