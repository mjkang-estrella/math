# H047 Factory Fable walk review — raw, not accepted wholesale

2026-10-09 UTC. Existing review completed at user shutdown, no pending child runs.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h047-walk-algebra-review-fable-20261009-r1`.
Actual untruncated report recovered from backing-thread position21, item
`turn-item:provider:acpRegistry:native-item:provider-instance%3AacpRegistry_factory_droid%3Af9147a42-5569-4c61-af5a-d76dbe6e01c9%3Aturn%3A2%3Aassistant%3A0`; task_status summary again contained only a plan footer.
Root retains the arithmetic/label corrections as scoped paper evidence. The
claimed cycle rates, approximately16-step trapping, IID image-bias gain ceiling,
stationary occupation estimates and recalled comparative hitting constants are
UNVERIFIED. They do not establish necessary gain ceilings or actual stopping
laws. No fresh external sources were fetched by the reviewer. No followup
review or experiment is authorized under the user stop instruction.

Stopping here per the shutdown instruction. Below is the review as it stands, based on the versions of `H047-walk-grok-raw.md`, `H023-fixed-difference-walk.md`, `H019-xonly-baseline-screen.md`, `H043-fullwork-disposition.md`, `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md` and the top of `STATE.md` that I read. The raw file and STATE were modified externally after my read; this review covers the text I saw. Read-only; no experiments, scripts, files, children or commits. H034 cap untouched. No H038 Farey/height-lattice material consulted or used.

## Verdict

No named candidate survives as a testable improvement. Verified improvement stays **NONE**; best supported work stays exponent 1/2 with BLS negation rho (low memory) and x-only interleaved negation BSGS (square-root memory) as comparators.

## Card 1 (sibling-min successor)

**Cost correction.** From the shared denominator $d=(x_J-x_W)^{-1}$ (batched, $3M+\varepsilon_K$ per element, $\varepsilon_K=(I-3M)/K$):

- slope $\lambda_+=(y_J-y_W)d$: $M$; $x(W+J)=\lambda_+^2-x_W-x_J$: $S$
- slope $\lambda_-=-(y_J+y_W)d$: $M$; $x(W-J)$: $S$
- one ordinate for the winner, $\lambda_\pm(x_W-x_\pm)-y_W$: $M$

The sibling abscissa costs $M+S$ (as H043 already records), not $2M$. The sibling ordinate costs $1M$ (direct minus-slope), not $\approx 2M$. Both root objections confirmed. Grok's schedule (full sum first, then sibling, then ordinate if minus wins) is $(6+\rho_-)M+2S+\varepsilon_K$. The better schedule, both abscissae first then one ordinate, is **$6M+2S+\varepsilon_K$, independent of $\rho_-$**. Grok's $(7+2\rho_-)M+S$ and its $8/6$, $7/6$ ratios are wrong on both counts; the correct step ratio against $5M+S$ is $(6+2s)/(5+s)$: exactly $4/3$ at $s=1$, about $1.310$ at $s=0.8$. The useful hitting time $T$ must therefore shrink below $0.75$ (resp. $0.763$) of the control's.

**Structural errors.**

1. $T_0=O$ gives $J_0=O$. Then $W\pm J_0=W$, successor $\kappa(W)=W$: every state with $h(x(W))=0$ is an absorbing fixed point, about $1/16$ of the quotient. Walkers die within $\sim 16$ steps. Must start the chain at $T_0=G$ (still 23 additions).
2. Coalescence requires a single global transition map (hash, jump table, min rule). The per-walker "seed" may only fix the start point and labels; if it enters $g$, meeting walkers do not share a future and the rho mechanism is lost. Grok's sentence "g reads only $\kappa(W)$" is the consistent reading; the "state = $\kappa(W)$ and a seed" phrasing is not.
3. Fruitless 2-cycles exist at rate $\Theta(1/r)$: from $W'=-(W-J_i)$ with $h(x(W'))=i$, the minus candidate is $-W$, and the min rule returns $\kappa(W)=W$ with constant probability. A 2-cycle contains a DP with probability $\approx 2\theta$, so trapped walkers never reach a DP and the "two null replays" retirement never fires. The card has no cycle detection or escape; one must be added and charged (BLS-style check plus escape), which the card explicitly declines to inherit.
4. Lazy labels: replay from the walker's start costs a full re-walk per confirmation. Either carry $(a,b)$ per step (integer additions, as the control effectively does) or charge the replay.
5. Restart $\kappa(Q+[\rho]G)$ is a scalar multiplication ($\sim 1.5\log_2 q$ unbatched group operations), not "the start addition". The control pays the same per start, so only the extra restart frequency is the differential; it still must be charged.

**Quotient invariance.** The pair $\{x(W+J),x(W-J)\}$ depends only on the class $\{W,-W\}$, so the min rule is well defined on the negation quotient. Initialization $(0,\sigma_0)$ is correct here.

**Cheapest paper falsifier.** Grok's own kill test (a one-addition rule reproducing the successor) does not fire: the min needs both abscissae. The kill comes from the gain ceiling instead. Under the standard heuristic that the two candidate abscissae are independent uniform draws, the successor abscissa has density $2(1-t)$ and collision entropy $\sum p_i^2\approx (4/3)/N$. The IID-birthday hitting time then shrinks by at most $\sqrt{3/4}\approx 0.866$. The product with the cost ratio is $0.866\times 4/3\approx 1.155>1$ at $s=1$ (about $1.135$ at $s=0.8$). So even granting the full image-bias benefit, Card 1 loses. Limitation: this is a heuristic ceiling (IID sampling, uniform abscissae, useful-collision fraction equal on both sides), not a proof, and it is a ceiling on the gain, not an assertion that image bias yields any stopping law. As instructed, no inference from marginal bias to a useful stopping law is made.

## Card 2 (sorted pair, double on $z>u$)

**Labels.** The quotient is reflection $P\mapsto G-P$, not negation. With $P=aG+bQ$, reflection gives $(1-a,-b)$ (H023). Doubling the sorted representative gives $(2a,2b)$, then $(1-2a,-2b)$ if the output pair swaps. Grok's $\varepsilon(2a,2b)$ labels $-2P$, which is not in the class: wrong. Start labels are $(0,1)$ if the sorted pair keeps $Q$ as representative and $(1,-1)$ if it swaps to $G-Q$; Grok's $(0,\sigma_0)$ is wrong in the swapped case. Root objections confirmed.

**Lift.** Doubling is not invariant on the reflection quotient (classes of $2P$ and $2G-2P$ differ in general). It is well defined only with a deterministic lift. The sorted pair supplies one: the representative $P$ with $x(P)-g\le x(P-G)-g$ (when $u\ne v$; $u=v$ is the known-log $2P=G$ case). The card should state this lift explicitly; "double the represented point" is acceptable only under that reading.

**Cost.** $5M+\rho(11M+3S)+\varepsilon_K$ plus a second inversion batch in rounds containing a double, as in H023. The gate $\rho<s/(11+3s)$ ($0.071$ at $s=1$, $0.060$ at $s=0.8$) is arithmetically correct, under equal useful hitting time, which is not granted.

**Cheapest paper falsifier (answers Grok's question 2).** H023 proves exactly that translation never increases the sorted minimum: new $u'=\min(z,u)\le u$. An accepted translation requires $z\le u$, so every run of consecutive translations is a strictly descending sequence of shifted abscissae. Under the uniform-abscissa heuristic, $P(N\ge k\mid u_0)=u_0^k/k!$, hence $E[N\mid u_0]=e^{u_0}-1$; with $u_0$ the min of two fresh draws after a double, $E[N]=2(e-2)-1\approx 0.44$ accepted translations per double. Trajectory occupation $\rho\approx 1/(1+0.44)\approx 0.70$, about ten times the gate; step cost $\approx 12.7M+2.1S$, roughly $2.5\times$ the control at $s=1$. For $\rho<0.071$ one would need $>13$ consecutive descending uniform draws on average. Even if the heuristic were off by a factor of five, Card 2 loses. Limitation: heuristic, not a proof; a proof would need the stationary distribution of $u$. Also, the accepted-translation segments are deterministic $+G$ paths and contribute no merging, so the "equal hitting time" premise is additionally unsupported.

**Prior art.** This card is H023's own "concrete alternative" (compute $+G$, double when $z>u$), already parked. No new mechanism.

## Card 3 (bit-selected add or double)

**Cost.** Affine doubling from a batched inverse: $S$ ($x^2$) $+M$ ($\lambda$) $+S$ ($\lambda^2$) $+M$ ($y_3$) $+3M$ share $=5M+2S+\varepsilon_K$. Mixed step $5M+S+\rho S+\varepsilon_K$ as stated; doublings and additions share one batch. Penalty factor $(5+s+\rho s)/(5+s)$: $\approx 1.083$ at $\rho=1/2$, $s=1$.

**Correctness.** Doubling is invariant on the negation quotient ($2(-W)=-2W$) and is a bijection on the quotient (odd order), so labels $\varepsilon(2a,2b)$ and start $(0,\sigma_0)$ are correct here. Same defects as Card 1: $J_0=O$ is absorbing on $\beta=0$, $h=0$ states; add-add fruitless 2-cycles persist at rate $\Theta(1/r)$ (roughly $1/(8r)$ per step) with no detection, so trapped walkers never trigger the stated retirement; lazy replay and restart scalar multiplication must be charged.

**Cheapest paper falsifier.** This is Pollard's original mixed iteration (add or square by a hash of the current element), the comparator Teske and BLS already beat with pure $r$-adding walks. The only conceivable hitting-time gain is removing the $r$-adding slowdown relative to a random mapping, which for $r=16$ is a few percent (recalled heuristic $1/\sqrt{1-1/r}\approx 1.033$; not re-sourced in this pass). Break-even at $s=1$ would need $\rho<0.2$; the lsb rule gives $\rho\approx 1/2$. At best a $\le 3\%$ effect, so not a material improvement in either direction. Prior art: Pollard 1978, Teske, BLS, as known techniques.

## Common limitations of this review

- All hitting-time statements are heuristics (uniform abscissae, IID sampling, random mapping). None is a proof of impossibility, and none asserts a generic lower bound; they are gain ceilings against which the corrected costs are compared.
- Arithmetic counts follow the repo's EFD-based affine ledger (H043, H019, H023); I did not re-fetch EFD or BLS in this pass. Field additions, label integer work, memory traffic and dispatch are omitted by the same convention on both sides.
- The sibling ordinate identity Grok flags as "unchecked" is just $\lambda_-(x_W-x_-)-y_W$ with $\lambda_-=-(y_J+y_W)d$; this is the ordinary affine formula, so no separate confirmation is needed.
- I did not re-read the externally modified raw report or STATE after the change notice.

## Source scope

Repository records only: H047-walk-grok-raw (as read), H023-fixed-difference-walk, H019-xonly-baseline-screen, H043-fullwork-disposition, RESEARCH_LOOP, RESEARCH_TEAM, STATE lines 1 to 120. No external fetch, no experiment, no new hypothesis, no H038 route.
