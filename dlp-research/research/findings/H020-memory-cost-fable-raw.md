Provider: acpRegistry_factory_droid / claude-fable-5.1
TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h020-memory-cost-review-fable-20261008-r1
Status: completed; no pending children. Raw review NOT accepted wholesale. Root flags conditional DP accounting, adaptive-label counting, membership-filter versus witness-retrieval memory, and blanket dominance claims for further independent review.

# H020 memory-constrained hybrids: independent read-only review

Scope: baseline/memory ledger and Cards 2–4 of `H020-memory-grok-raw.md`, checked against the accepted H019 disposition and H019 x-only screen. Card 1's shadow mathematics is excluded per brief; I comment only on whether its proposed test has a defined pipeline. No edits, runs, or children. All numbers below are my own recomputation.

## Verdict

Verified complete-work improvement remains **NONE**. Cards 2–4 are correctly closed, but each closes by an elementary counting argument that does not need the GWZ imports the raw uses, and the raw mis-states the scope or the inequality in each. The baseline ledger contains errors in both directions; none of them opens a gain. No numerical test is justified: Cards 2–4 need none, the ledger corrections are arithmetic, and Card 1's "falsifier" has no defined update rule to run.

## Baseline / memory ledger

**B1. "DP storage at any $M \ge 1$ does not change the leading term" is false for bounded $M$.** With a single processor the rho ledger that treats batch inversion as negligible needs $n$ concurrent walks (Montgomery trick, $I/n$ per step). Distinguished points with $M$ records force density $\theta \approx M/T$, $T=\sqrt{\pi q/4}$, and the post-collision overhead is $n/\theta = nT/M$ steps (van Oorschot–Wiener). Total field work is about

$$T\Bigl[(5+s)\bigl(1+\tfrac{n}{M}\bigr)+\tfrac{I}{n}\Bigr],$$

minimised at $n^*=\sqrt{IM/(5+s)}$, giving factor $1+2\sqrt{I/((5+s)M)}$ over $0.886\sqrt q\,(5+s)M$. At $I=8M$, $s=1$: $M=1$ gives $\approx 3.3\times$; $M=64$ gives $1.29\times$; $M=2^{16}$ gives $1.02\times$. So "$(1+o(1))$" requires $M\to\infty$, specifically $M \gg I/(5+s)$. Fruitless-cycle handling (BLS 2011) adds a further few percent not in the ledger. This confirms the root flag: DP storage $\ge 1$ is not automatically the same leading constant once batched inversion and DP overhead are both charged.

**B2. "Best prior art for every budget $o(\sqrt q)$" is unsupported as stated.** It is a two-algorithm comparison (rho vs capped BSGS), not a survey and not a lower bound. Nothing in the raw excludes a third schedule. Record it only as "best of the two schedules compared".

**B3. The finite $(k,\ell)=(8,8)$ cost $2.45M+1S$ omits $\ell+1$ inversions per block (known H019 repair).** The raw's formula $\frac{(\ell+1)(5k-3)}{k(2\ell+1)}M$ is exactly the H019 $C_x(k,\ell)$ with $I$ set to zero. The dropped term is $\frac{\ell+1}{k(2\ell+1)}I \approx I/(2k)$ per key. At $(8,8)$: $0.066\,I$ per key, i.e. $+0.53M$ at $I=8M$ (so $2.98M+S$), $+5.3M$ at $I=80M$, which exceeds rho's $5M+S$ per step. The limiting $2.5M+S$ needs $k\to\infty$; to hold inversion overhead under $0.1M$ per key one needs $k\gtrsim 40$ at $I=8M$ and $k\gtrsim 400$ at $I=80M$. The $0.62$ ratio is therefore an asymptotic arithmetic figure (consistent with H019 screen's $B/0.886\approx0.605$–$0.62$), not a finite-parameter result.

**B4. The crossover $\theta\in(0.19,1.33)$ is a particular schedule, not a memory theorem.** I reproduce the numbers: $(\theta+\tfrac{1}{4\theta})\cdot 3.5=5.317$ gives $\theta\in(0.188,1.331)$ at $s=1$; $0.182$ at $s=0.8$. But (i) it uses the standard capped average $b+q/(4b)$ with $2.5M+S$ per key for both babies and giants (asymptotic per B3); (ii) rho is charged zero DP/batch overhead (B1), which is fine only for $M=\Theta(\sqrt q)$; (iii) the memory unit is "$b$ abscissa+index records" against "$M$ group elements", and in bits an abscissa+index is $\approx1.5\log_2 q$ while a DP record ranges from $\approx\log_2(\#\text{DP})+\log_2(\#\text{walks})$ (seed-replay) to $3\log_2 q$ (full labels). A budget comparison must be in bits including labels, setup tables ($O(k\ell)$ full points, and the $B$-entry table in Card 1), and must apply the same compression to both sides (H007 caveat, repeated by root). None of this moves the $\Theta(1)$ crossover, but the constant $0.19$ is not established at matched bits.

**B5. GWZ constants.** "$0.38$ and $0.36$ multiply by about $0.40$ because of serial $I=8M$", Table 4's $c(0)=6$, and Table 5's $0.9$ are unverified imports here (H019 screen states the grumpy constant is conjectural and unused). They are not needed for any conclusion below; record them as unverified and unused.

**B6. Chord sentence.** "$c\le1/3$" repeats the reversed bound: H019 derived $c=2/(5+s)\in[1/3,2/5]$, so $1/3$ is the optimistic edge. "about $0.95$ after the repeated-jump atom" repeats the ceiling H019 marked unsupported. The conclusion (both $0.77$ and $0.95$ exceed $0.62$) survives because H019 screen already shows $B<C$ throughout $s\in[0,1]$ for $F=3$.

## Card 2: restart vs single dictionary

**Survives, and strengthens.** The raw's $q/(2L)$ is actually a deterministic counting bound and does not need GWZ's $c(0)=6$. A herd of three lists of length $L$ detects $k$ only through cross-list signed pairs: at most $3L^2\cdot2=6L^2$ scalar values (within-list pairs share the $Q$-coefficient and give no $k$). More generally, $N$ listed points with known labels determine at most $2\binom N2<N^2$ candidate $k$. For a uniformly random $k$ and independently randomised restarts, the success probability per herd is $p\le N^2/q$, and the expected cost **including early stop** is at least (expected number of full failing herds)$\times N \ge (1/p-1)N\ge q/N-N$. Overlap between herds only lowers $p$; a deliberately disjoint partition gives the same order $q/(2cN)$. So restart schedules cost $\Theta(q/N)$ and beat rho only when $N\gtrsim 0.65\sqrt q$ (field-work units with $2.5M+S$ vs $5M+S$), where they are a single dictionary anyway.

**Scope correction.** This bound applies to listed-point (non-coalescing) schedules, where detection is pairwise among stored records. It says nothing about iterated walks, which is precisely why the DP method detects collisions among $T\gg M$ points with $M$ records. The raw's "the closed form already kills the restart" is right; "Restarts do not move that threshold" should be read as "no listed-point restart schedule moves it". This is textbook prior art (the standard time/memory reasoning behind BSGS $\Theta(q/b)$ vs rho/DP), not a new result.

## Card 3: anchor fingerprints

**Conclusion survives (no exponent change); the inequality and the constant are wrong.**

- *Direction.* A giant query against $B$ fingerprints produces $B/2^t$ false hits, each costing $\sim m$ x-only steps. Capping verification at $1/(2\lambda)$ of a giant step needs $2^t\ge 2Bm\lambda$, i.e. $t\ge\log_2(Bm\lambda)+O(1)$. The raw's falsifier "any $t\le\log_2(Bm\lambda)$ that keeps verification inside a constant factor" is reversed; the lower bound on $t$ is what forces $\Theta(\log q)$ bits. Root's flag is correct.
- *Constant.* The raw's $2\log_2 B+\log_2(m\lambda)+2\log_2 q/m$ double-counts: in a table bucketed by fingerprint, $\log_2 B$ fingerprint bits are implicit in position, and the index can be coarsened to the anchor ($\log_2(B/m)$ bits). Explicit bits per baby become $\approx\log_2 B+\log_2\lambda+2\log_2 q/m$, which is $\approx0.75\log_2 q$ at $m=8$ and $\approx0.55\log_2 q$ at $m=32$, against $1.5\log_2 q$ for full $x$+index: a $2$–$3\times$ compression, not $20\%$. Moreover the anchors are unnecessary: store $\log_2 B+\log_2\log_2 q+O(1)$ hash bits plus index and verify a hit by one scalar multiplication ($O(\log q)$ group ops); this standard hash-and-verify trick achieves the same $\approx0.5\log_2 q+O(\log\log q)$ bits per baby. So Card 3 is dominated by folklore and is a constant factor in bits only.
- *Why the exponent is robust.* Any membership structure with false-positive rate $\epsilon$ needs $\ge\log_2(1/\epsilon)$ bits per element (standard filter lower bound), and resolving a false hit without a stored index costs $\Omega(m)$ to $\Omega(B)$ group ops. Either route gives $\ge\log_2 B-O(1)\approx0.5\log_2 q$ bits per baby at $B\sim\sqrt q$, so $b=O(W/\log q)$ and the crossover memory stays $\Omega(\sqrt q\log q)$ bits. This is a scoped argument for BSGS-type listing, not a universal bound.
- *"Fails for every realistic $\beta<1/2$"* is undefined ($\beta$ is not introduced in the raw; "realistic" is not a quantity). Replace with: compression shifts the bit-crossover by a constant $\le\sim3$, applied equally to the rho DP store, and changes no exponent and no field-work count.

## Card 4: replay buckets

**Pricing of the literal algorithm is correct; the premise is wrong.** $T/b$ passes over a length-$T$ replayable stream cost $T^2/b$ steps before any matching; with $T\sim0.886\sqrt q$ this exceeds rho iff $T>b$, and exceeds capped block BSGS at the same $b$ throughout. This is the standard external-memory collision tradeoff, and parallel collision search (vOW) is exactly the fix, which requires iteration, i.e. coalescence. The raw correctly scopes it: "prices this detector only".

The opening sentence, "A side image that does not merge walks cannot use distinguished points (H017–H019)", contradicts the accepted H019 disposition: a shared coordinate-based DP predicate CAN capture equal side keys if both record types are stored and compared, with the useful-event rate thinned by $\theta$ (not $\theta^2$) under the uniform-key model. That detector costs $O(1)$ per step and memory $\theta T$, and reduces channel enhancement to $1+(F-1)\theta$; it is a different, cheaper detector than the one Card 4 prices. Card 4 therefore does not close side images categorically; it closes bucketed replay. Non-coalescence remains an obstruction to constant-strength detection at $o(\sqrt q)$ records only within the H019 uniform-key model.

## Does the material complete-work hypothesis survive?

For the memory-constrained hybrids actually proposed (Cards 2–4): no. Each is dominated by known art at every budget, by counting arguments stronger than the raw's. The baseline ledger, after the corrections above, still has rho at $0.886\sqrt q\,(5+s)M\,(1+o(1))$ only for $M\to\infty$, and x-only block BSGS at $\approx0.62\times$ rho field work only asymptotically in $k$ at $\Theta(\sqrt q)$ records; neither correction creates a gap any card exploits. The only H020 item with unresolved status is Card 1, outside this review.

## Is any concrete numerical test justified?

**No.**

- Cards 2–4: closed by counting; a simulation could only confirm arithmetic.
- Ledger items B1, B3: arithmetic; no measurement needed to accept the corrected formulas. A benchmark would only matter if someone later claims a specific finite $(k,\ell,I/M,n,M)$ win, and that claim must come with its own exact ledger.
- Card 1 falsifier $(r,k,w)=(16,4,32)$: the raw specifies no residue update rule (it states the primitive is "missing"), so there is nothing to iterate "in parallel". On the admitted fixture $(p,q)=(8191,8053)$ and on any 16-bit field, $w=32\ge2\log_2 p$, so the test cannot distinguish a short shadow from full arithmetic; it is not a test of width $t+O(k)\ll\log_2 q$. No defined pipeline, no run.

## Items for root to record

1. Replace "any $M\ge1$" with the explicit factor $1+2\sqrt{I/((5+s)M)}$ for single-processor batched rho with $M$ DP records; $(1+o(1))$ needs $M\gg I/(5+s)$.
2. Restore the $(\ell+1)$ inversion term; mark $2.5M+S$ and the $0.62$ ratio as $k\to\infty$ arithmetic.
3. Keep Card 2 closed via the deterministic pairwise bound $\ge q/N-N$ (listed-point schedules only).
4. Keep Card 3 closed as a constant-factor bit compression (up to $\sim3\times$, equally available to rho DPs), fix the $t$ inequality to $t\ge\log_2(Bm\lambda)+O(1)$, strike "realistic $\beta$".
5. Keep Card 4 closed for bucketed replay only; strike "cannot use distinguished points".
6. Fix $c\in[1/3,2/5]$; strike the $0.95$ ceiling; mark GWZ Tables 4/5 figures unverified and unused.
7. "Best for every budget" downgraded to "best of the two schedules compared".
