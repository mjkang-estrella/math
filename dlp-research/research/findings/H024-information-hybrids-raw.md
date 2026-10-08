# Raw H024 Factory Opus report — UNREVIEWED

TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h024-information-hybrids-factory-opus-20261008-r1

This retained proposal is not an accepted result. In particular, character-bound,
posterior-cost and multi-family coverage claims require independent review.

# H024 information, learned and hybrid pass: final report

**Outcome:** verified gain is **NONE**. Nothing I found changes the exponent. One search-policy card (C) could plausibly lower the high-memory constant, and it can be tested cheaply. Card A is an accounting rule that should become the gate for any future predictor proposal. Card B shows that a large class of learned and aggregated features cannot help, and names the few classes it does not cover.

**What I did and did not do:**
- I read `README.md`, `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md`, `STATE.md`, and the accepted information, learning and schedule findings from H002 through H023. I did not open any H024 proposal.
- I made no edits, experiments, child tasks or commits.
- I did run shell commands, all read-only: listing and searching the repo, and piping two primary-source PDFs through `curl | pdftotext` to standard output for reading. No files were written.
- Sources read directly this pass:
  - Bernstein–Lange, *Two grumpy giants and a baby*: the ePrint 2012/294 abstract, plus §§5–6 of the PDF.
  - Kohel–Shparlinski (ANTS 2000): the author PDF, Theorem 1.
- Everything else cited below is either an earlier project read or noted as abstract-only or from memory.

---

## A. Posterior-ordered search: what information actually pays (gate plus search policy)

**Mechanism.** A public, paid predictor gives a view Y of the target Q. Rank coarse scalar blocks by posterior probability and run BSGS with giant steps in that order. The baby table is shared. Recovery is exact and the search is complete, so a wrong prediction only raises expected cost and never causes failure.

**Gain source.** This is a correction to H002's rejected "$2^{-I/2}$" claim:
- The relevant quantity is a Rényi (Arimoto) conditional entropy, not Shannon mutual information.
- Baby-then-giant cost for rank R is $m+R/m$. Its optimum, $2\sqrt{E[R]}$, needs memory $\sqrt{E[R]}$. Interleaving improves the constant, as BL show.
- Arikan (1996) gives $E[R]\approx 2^{H_{1/2}(K\mid Y)}$, accurate up to a factor of $1+\ln q$.
- For collision or kangaroo search over ranked prefix sets the analogous quantity is $E[\sqrt{G}]\approx 2^{H_{2/3}/2}$. This holds only if every prefix set can be searched at square-root cost and work is reused across prefixes.

**Exact consequences:**
- **One coarse bit with accuracy $1/2+e$:** $E[R]=\tfrac q2(1-e)$, so cost scales by $\sqrt{1-e}$. Ordered BSGS has no break-even threshold, because the baby table is shared. A 10% gain needs $e\ge0.19$.
- **Restart-style collision search:** under a split-halves model there is a break-even threshold near $e\approx0.085$. This is illustrative only.
- **Mixture (exact with probability α, otherwise nothing):** $E[R]\approx(1-\alpha)q/2$. That is a constant gain only, which agrees with H002 correction 2.
- **Exponent gain:** requires $H_{1/2}(K\mid Y)\le(1-2\varepsilon)\log_2 q$. That means Θ(log q) bits with constant advantage, obtained at sub-$\sqrt q$ cost. This is the noisy-oracle regime of H003, now with an exact recovery method that has no failure case.

**Costs that must be charged:**
- predictor training, if it depends on the curve;
- evaluating the predictor on Q;
- a block-offset table, either $2^b$ entries for b coarse labels or one scalar multiplication per arbitrary jump;
- memory $\sqrt{E[R]}$, compared against a comparator with equal memory;
- if m is tuned for the average case, the worst case worsens.

**Prior art.**
- Arikan, IEEE Trans. IT 42(1), 1996 (abstract only; theorem from memory).
- Galbraith–Holmes, ePrint 2010/616 (located, not read).
- Lange–van Vredendaal–Wakker, *Kangaroos in Side-Channel Attacks*, ePrint 2014/565 (located, not read).
- Ranked side-channel search is known. What would be new is only a public-only source of Y.

**Main unsupported assumption:** that some public feature gives constant advantage on coarse bits. Card B shows that most low-complexity features give at most $O(L/\sqrt q)$ advantage, where L is the feature's additive Fourier L1 norm (sum of absolute Fourier coefficients).

**Cheapest decisive falsifier:** plain arithmetic, no curve work. Take any candidate's held-out confusion matrix, compute E[R], add the evaluation and offset costs, and reject if the cost ratio is at least 1. The saved H014 JSON could be re-scored this way, read-only, after review.

**Verdict:** adopt as an accounting gate after independent review. It is not a mechanism by itself.

## B. Learned linearization and averaging over translated views: a scoped algebraic wall

**Mechanism tested.** Two ideas:
- A learned, Koopman-style embedding $v(P)\in\mathbb C^n$ with $v(P+G)\approx A\,v(P)$, read out through its phase.
- Aggregating features over the rerandomized views $Q+rG$.

This addresses the brief's point that H021 covered only exact, low-dimensional representations.

**Lemma (my derivation, needs review).** Setup:
- $\#E(\mathbb F_p)=q$ prime.
- $h=\psi\circ f$, with ψ a nontrivial additive character of $\mathbb F_p$ and f a nonconstant function on the curve of pole degree $d<p$.
- Kohel–Shparlinski Theorem 1 (read this pass): $|S|\le\sum m_i\deg P_i\,\sqrt p$ with $m_i\le n_i+1$.

So every normalized scalar-Fourier coefficient satisfies $|\hat H(a)|\lesssim 3d/\sqrt q$, for every frequency a.

The function class stays inside this bound under three operations:
- **Translation:** $f\circ\tau_c$ has the same degree.
- **Sums of translates:** their degrees add.
- **Small-height dilations:** for $m\equiv u/v$, substituting $n=vn'$ gives a function of degree at most $d(u^2+v^2)$.

**Consequences:**
1. **Coarse predicates.** Take a statistic of weight W and degree Δ in this class, and a predicate π with Fourier L1 $L_\pi$ (intervals and bits have $O(\log^2 q)$, by H019). Their correlation is at most $3W\Delta L_\pi/\sqrt q$. For averages over independent rerandomizations, beating $\sqrt q$ work therefore needs $W\Delta L_\pi\gtrsim q^{1/4}$.
2. **Koopman readout.** Assume $A$ is diagonalizable with condition number κ. Phase readout needs one coefficient with $|\hat w_j(a)|^2\ge\gamma$, which forces $W\Delta\gtrsim\sqrt{\gamma q/n}/(3\kappa)$. Otherwise the equivariance is diffuse: it amounts to short-range translation invariance, which is H017 card 3 (approximate orbit labels) and is already covered.
3. **The H022 hints fit here.** Constant-squareclass and halving-root features, if they are low-degree multiplicative characters, fall under the same L-function framework (KS Propositions 1–2, not checked line by line). A bounded-defect integer filter on a finite group is bounded in size, so it is useful only as an approximate character, which is case 2 again.

**What remains open (no positive rationale for any of them):**
- **E1:** high-height dilations and other cheap high-degree compositions. This is the H013 multiplicative-character (MCL) territory, where only upper bounds of order $q^{-1/12}$ are known.
- **E2:** bit-level nonlinear or learned networks whose Fourier L1 is at least about $q^{1/4}$.
- **E3:** fine-grained matched filters. These are membership tests that cost about one evaluation per candidate, which is BSGS-like.

**Prior art.** Kohel–Shparlinski 2000 (read). Koopman/EDMD methods and "grokking learns Fourier features" (Nanda et al., 2023) are from memory; there the input is the scalar, so characters are cheap.

**Main unsupported assumption:** none on the closure side. The open risks are bookkeeping in the lemma: pole orders, the multiplicative-character version, and Artin–Schreier degeneracy (excluded when $\Delta<p$).

**Cheapest decisive falsifier:** a prescreen that needs no curve. For any proposed learned or explicit feature, compute its Fourier L1 over $\mathbb F_p$ (or $\mathbb F_p^2$), or its degree. If $W\Delta L\ll q^{1/4}$ at target sizes, reject without any curve experiment.

**Verdict:** a closure for this class, and it says where any future learned work would have to look (E1 and E2).

## C. Many-giant coverage designs with negation (search policy): the one constant-factor survivor

**Mechanism.**
- Use f arithmetic-progression families $\{b_iQ+(c_i+js_i)G\}$ with distinct small $|b_i|$, generated with GWZ paired x-only outputs and stored in one hash table.
- A cross-family x-match solves $(b\mp b')k=\dots$ exactly. Verify the result.
- The shift and stride rule must be a closed form in q, or its search cost is charged.
- For a deterministic design, the uncovered set after a miss does not depend on k, so a fixed schedule loses nothing compared with an adaptive one.

**Gain source.** This targets the "global anti-collisions" that BL name.
- **Counting bound with negation:** cross pairs give at most two scalars each. Same-family pairs inside a progression give only O(t) values. So equal families cover at most $t^2(1-1/f)$ scalars.
- **Average outputs at that bound:** $E\ge\tfrac23\sqrt{q/(1-1/f)}$, which is 0.943 (f=2), 0.816 (f=3), 0.770 (f=4), tending to 0.667 times $\sqrt q$.
- **f=2 matches GWZ Lemma 3.2 exactly.** Interleaved negation BSGS is already optimal for two families.
- **Without negation, BL show the bound is nearly reachable at f=3:** 0.71875 coverage at $1.5\sqrt\ell$ against a bound of 0.75, and a measured average of $1.2055\sqrt\ell$ against $1.155\sqrt\ell$.

**Potential complete-work effect (constant only):** output count and stored keys would scale by c/0.943. With H019's GWZ specialization at about 0.62 of rho field work, c = 0.80 would give about 0.53 of rho, in the high-memory regime only. Memory traffic is not modeled.

**Prior art (BL text read).** BL §6:
- report that a 4-giant variant "outperforms";
- speculate that a growing number of giants reaches the optimal $(0.5+o(1))m^2$ slopes;
- state "it is not clear how to choose the shift distances properly."

This is a known open problem, not a new idea. The GWZ negated-grumpy constant (about 0.9 in Table 5) is still unverified. A bounded search found no later multi-giant design; that is not proof of novelty.

**Main unsupported assumption:** a uniform shift rule for f ≥ 4 negation-aware progression families that keeps the covered sets close to disjoint while coverage grows.

**Cheapest decisive falsifier:** integer combinatorics only, no elliptic-curve arithmetic.
- Compute exact negation-aware coverage curves and the average-case outputs for a declared parametric family.
- Select on one prime of about $5\cdot10^4$ and validate on two fresh primes, with no retuning.
- Pair counting costs about q per design, so roughly 20 designs fit the 1M-event cap. Counting overlaps of progression sumsets in closed form would be cheaper.
- Park the card if nothing beats 0.90√q.

**Verdict:** rank it first for hypothesis review. It is a constant factor only.

## Rejected or deduplicated

- Learned distinguished-point table selection: known (Bernstein–Lange 2012).
- Learned start points: H002 L3.
- Tuning r-adding walks against anti-collisions: BL §4 and BLS2011, with only a small margin left.
- Approximate orbit labels: H017.
- Dilation characters: H013 and H016.
- Sparse powers and implicit relations: H017 and H018. The finite failure there excludes only the specified features on that fixture.
- Shadow walks: H020.
- Multi-target amortization: a different problem.
- A free learned index: excluded by the brief.

## Your composition question

Can modest measured or analytical structure combined with known search change complete work?
- **Exponent:** no supported path. It needs Θ(log q) bits of conditional Rényi-entropy reduction at sub-$\sqrt q$ cost, and the low-complexity translation-view features in card B are bounded far below that.
- **Constant:** yes in principle, through card C. That gain comes from analytical coverage structure, not from information about the scalar.
- **Measured predictors:** ordered BSGS turns any coarse advantage into a gain with no threshold, but every walled feature yields only an $O(W\Delta L/\sqrt q)$ relative gain.

**Suggested next step:**
1. Independent prior-art and math review of card C: GWZ Tables 4–5, any later multi-giant work, and the negation-aware counting bound.
2. Then a frozen integer-only coverage protocol.
3. Separately, a math review of card B's lemma and of card A's formulas.
