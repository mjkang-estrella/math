# H031 Factory memory/recomputation raw proposal

UNREVIEWED claims retained verbatim. Transport summary was only 'Plan is up-to-date.'
Root recovered the substantive untruncated assistant message at timeline position40
through t3_thread_read(messages); r2 is completed, no pending children.
Task: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h031-memory-recomputation-factory-opus-20261008-r2
Provider: acpRegistry_factory_droid; model: claude-opus-5-5.
No reported edits/experiments/children/safety interruption. Source access incomplete.
Numbers, probability laws, novelty, universal closures and proposed tests are NOT accepted.

I've drafted five cards. One survives for independent review, and it applies only to the many-target case. The other four fail paper inequalities under assumptions that favor them. Nothing here changes the single-target estimate: verified improvement is still NONE, and the generic exponent 1/2 reference is unchanged.

**What I did.** I read `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md` and `STATE.md`. I read the H030 storage, prior-art, hierarchy, reconciliation and partitioned-filter findings, both raw H030 storage memos, and the H002, H015, H019, H020, H025 and H029 time-memory dispositions so I wouldn't repeat them. I opened no H031 file. I ran no experiments or code, edited nothing, launched no children, and had no safety interruption. All arithmetic below was done by hand and needs independent recomputation.

**Source access.** A web search found the Kuhn–Struik SAC 2001 PDF (`cr.yp.to/bib/2001/kuhn-rho.pdf` and a Freiburg copy), but I could not open the full text: the fetch tool only accepts URLs the user supplied. So I have not checked whether that paper, or anyone else, already describes the Card 1 idea. Novelty is unverified.

**Units.** $C_x$ is the accepted H019 cost of one x-only progression key, with limit $2.5M+S$. A rho step costs $5M+S$. $s=S/M$.

---

## Card 1 (survives for review; many targets only): shared-baby BSGS that keeps solved targets' giants, with a distinct prime stride per target

**Mechanism.**
1. Blind each target with $Q_t' = Q_t + r_tG$, using a fresh uniform $r_t$. This costs one scalar multiplication per target and makes the $k_t$ independent and uniform, whatever the inputs were.
2. Build signed babies $x(iG)$ for $1 \le i \le b$ with H019 block generation.
3. Solve targets one after another. Target $s$ uses a public stride $D_s$: a distinct prime in $[2b+1-\Delta,\ 2b+1]$. It generates giants $x(Q_s - jD_sG)$ as an H019 progression, which needs $D_sG$ plus about $\ell$ offsets per stride.
4. Probe each giant against one shared table holding the babies plus every retained giant record $(t, j')$ of the targets already solved.
5. Recovery:
   - A baby hit gives $k_s = jD_s \pm i$.
   - A retained hit gives $k_s = jD_s \pm (k_t - j'D_t)$, using the stored $k_t$.
   - Verify with a full point or a scalar multiplication.
6. Once target $s$ is solved, insert its giants as known-log records.

The baby interval guarantees every target is eventually solved within $\lceil q/D_s\rceil$ giants, so there are no retries.

**Where the gain comes from.** Babies give deterministic coverage, which is twice as efficient per record as random coverage, but they must be paid for. Retained giants cost nothing extra to generate and give random coverage. Mixing the two beats either alone.

Under blinding, I checked these model claims:
- Marker density is uniform. Retained logs of target $t$ fill $(b, k_t]$ with spacing $D_t$, and each one also appears as $q - v$ under negation. Across solved targets the combined density is $n/D$ per unit log, constant. So each giant has hazard $2R/q$ from retained records, where $R$ is the retained count, independent of where the baby-coverage frontier is.
- The relations are distinct. Because the strides are distinct primes larger than any per-target giant count, $\Delta j\,D_s = \Delta j'\,D_t$ has no solution over the integers. Wrap-around mod $q$ adds only $O(1)$ coincidences per pair of targets.

**Large-$K$ continuum model.** Put $x = \Gamma/B$ and
$$\psi(y) = \frac{y - (1 - e^{-y})}{2y^2}.$$
Then
$$\frac{W}{\sqrt{qK}} = \frac{1+X}{\sqrt{I(X)}}, \qquad I(X) = \int_0^X \frac{dy}{\psi(y)}.$$

- Hand integration gives a minimum of about $0.906\sqrt{qK}$ keys near $X \approx 1.6$–$1.75$, with $B \approx 0.35$ and $\Gamma \approx 0.56$.
- The competent baseline (shared-table BSGS with no retention, at its optimum $b=\sqrt{qK}/2$) uses $1.0\sqrt{qK}$ keys.
- The simpler rate-sum approximation gives 0.866. That is too optimistic, so don't use it.

**Baselines to compare against.**
- Shared-table BSGS at its optimum.
- Kuhn–Struik rho with negation (about $\sqrt{qK}$ steps at $5M+S$, low memory).
- Bernstein–Lange precomputation at matched memory.
- A per-target interleaved variant (a GWZ-style growing baby table).

**Costs that must be paid.**
- Arithmetic: $C_x$ per key on both sides.
- Per-target setup: blinding, $D_sG$, $\ell$ offsets, final verification, and finding $K$ primes near $2b+1$.
- Tiling waste of at most $\Delta/(2b+1)$.
- One insert per giant, which the baseline doesn't pay. This needs a dynamic table, not a static filter.
- Peak memory of $b + R_{\text{final}}$, about $0.906\sqrt{qK}$ records, against the baseline's $0.5\sqrt{qK}$.
- **Bits per record, which is the main catch.** Retained records cannot use H030's index-free interval recovery, so each needs an explicit $(t, j')$ index plus a fingerprint. At 256-bit sizes that is roughly 10× the bits of a hierarchy-compressed baby, so the scheme needs about 16× the baseline's stored bits.
- False-positive resolution under whatever filter is chosen.

**Scope.**
- Solve-all-$K$, many targets only. With $K=1$ it does nothing.
- It is a constant-factor change. No exponent or single-target claim, and the generic multi-target lower bound only fixes the $\sqrt{Kq}$ order, not the constant.
- Retaining only a $\theta$-fraction of giants is a tunable variant that saves memory at the cost of hazard.

**Prior art.** Kuhn–Struik reuse of earlier walks is the conceptual antecedent; it is already in the repo's mandatory comparator list. Multi-target shared-table BSGS (keyhunt-style) is also known. The combination is probably folklore.

**Main unsupported assumption.** That the model's 9% saving survives finite $K$, the integer effects of the strides, and the bit-level memory cost against a competent many-target baseline.

**Cheapest decisive falsifier.** An exact or integer-model computation, with no curve needed:
1. Independently recompute the continuum optimum.
2. Run a finite integer simulation at $q \approx 2^{20}$ with $K \in \{16, 64, 256\}$ and a fixed blinding seed, including setup.
3. Park the card if the result is not at most 0.95× the shared-table optimum, or if it is dominated at equal stored bits.

## Card 2 (killed on paper): min-of-two class walk

**Mechanism.** From $\pm P$, compute $x(P+R)$ and $x(P-R)$ with one shared inversion. Move to the class with the smaller x. This map is well defined on classes without canonicalizing $y$.

**Hoped-for gain.** The image distribution becomes biased: its density is $2(1-u)$, so $N\sum\pi^2 = 4/3$, and the step count falls by $\sqrt{3/4} = 0.866$.

**Cost.** $3M + 2M + 2S + 1M$ (for the chosen point's $y$) $= 6M+2S$.

**Result.** The ratio against negation rho is $0.866\,(6+2s)/(5+s) \ge 1.039$ for $s \in [0,1]$. That is a loss even granting the ideal random-map law and ignoring its 2-cycles. Using more than two candidates is worse. Choosing by slope instead of x dilutes the bias to $O(1/r)$, and $r=1$ falls into the H025 bounded-stride trap.

## Card 3 (killed on paper): coalescent walk on x-only blocks with a min-hash anchor

**Mechanism.** The state is a center $X$. The block is $\{X + uT : |u| \le \ell\}$, generated x-only. The next center is $\text{anchor} + R_{h(\text{anchor})}$, where the anchor is the block point with the smallest hash.

**Same stride for every block.** The chance that two blocks coalesce is $(2/q)\sum_d \frac{n-|d|}{n+|d|} \approx 0.773\,n \cdot 2/q$, with $n = 2\ell+1$. The cost ratio against rho is
$$\frac{2\ell(2.5+s) + 6 + s}{(5+s)\sqrt{0.773(2\ell+1)}},$$
which is about 1.52 at $\ell=1$ and grows like $\sqrt{\ell}$.

**A different stride per block.** Two blocks intersect with probability $2n^2/q$, but their anchors agree only with probability $1/n^2$. The coalescence rate falls back to $2/q$, at $n$ times the cost.

This confirms the coalescence lock: there is no canonical alignment without the log.

## Card 4 (killed on paper): a filter over every precomputed trail point instead of distinguished points (Bernstein–Lange regime)

A filter hit tells you that you merged into a trail, but not your position or which chain. You still have to walk to the next distinguished point to get the log, so the online cost is unchanged. Recovering the position directly needs about $\log_2(\#\text{points})$ bits per point. That only pays off near a full table, at roughly $S \gtrsim q f^2/\log q$ bits for $f$ filter bits per point.

## Card 5 (killed on paper): x-only bursts around each distinguished point

Each new distinguished point probes its $2\ell+1$ shifts against the stored distinguished points. This raises the rate by a factor of $1 + (2\ell+1)\theta^2$ at a relative cost of $(2\ell+1)\theta c$, where $c = C_x/(5+s) \approx 0.57$. To first order it helps only if $\theta > 2c > 1$, which is impossible.

A related variant, where a new target's x-only burst probes the retained markers, has the same per-key rate as Card 1's giants but no baby coverage, so Card 1 already does better.

---

**What's still missing for a single target.** This lens has no single-target survivor. A real gain would need one of two things:
- a coalescent transition that yields two or more walked states per inversion, or
- a stored structure whose distinct useful relations per record beat signed progression coverage, at no more than the filter hierarchy's bits.

None of Cards 2–5 supplies either.

**Wave report.**
- **Best supported estimate:** unchanged. Generic square root, with H019/GWZ for high memory and negation rho for low memory.
- **Verified improvement:** NONE.
- **Hypothesis offered:** Card 1, a many-target constant factor of about 0.906 against 1.0 in keys, at about 1.8× the records and much higher bit cost.
- **Evidence:** only the model derivations above. Cards 2–5 are paper negatives under assumptions that favor them.
- **Next experiment that could change the conclusion:** recompute Card 1's continuum optimum independently, then run its finite integer-model test with the bits-matched comparison.
