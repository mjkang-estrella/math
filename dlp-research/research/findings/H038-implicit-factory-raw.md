# H038 independent implicit-relation report — raw testimony

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h038-independent-implicit-relations-factory-opus-20261008-r1`

Provider/model: acpRegistry_factory_droid/claude-opus-5-5. COMPLETED, no pending
children. No new primary source was opened. Raw mathematical and cost assertions
remain subject to root and independent review; usage figures are provider
reported and not independently verified or used for calibration.

# H038 information/cross-field lens: bounded negative outcome

**Result:** I found no card with a credible full-work gain. I worked three genuinely different operators through to paper ledgers, and none of them beats the square-root baseline. I also recorded one reduction gate and mapped the other constructions I tried to existing records. Verified improvement is still NONE. I did not pad the list to reach 3–5 cards.

**What I did:** I read RESEARCH_LOOP, RESEARCH_TEAM, STATE and these dispositions: H003 (character collapse), H004, H006, H013, H015, H017–H021, H024–H027 and H036. I did not read any H038 proposal. I ran no code, imports or experiments, made no edits and launched no children.

**Prior-art limitation:** I opened no primary paper myself. The fetch tool only accepts URLs the user supplies, and none were supplied. Every source statement below is what earlier root or reviewer records say they read. Treat each one as second-hand.

---

## Card 1: Point-count convolution aggregator (fibre-product covers)

- **Operator.** For fixed-degree rational functions $u,v$ and the quadratic character $\chi$:
  $$F(Q)=\sum_{P\in E(\mathbb F_p)}\chi(u(P))\,\chi(v(P+Q)).$$
  This sum comes from the point count of the double cover $w^2=u(P)\,v(P+Q)$ over $E$. For $u=x-c$ and $v=x-c'$ that cover has genus 3. One count aggregates about $q$ candidate pair-relations without listing any of them.
- **Hoped-for gain.** If $F$ correlated with structure in the log, such as parity or interval membership, a polylog number of counts would give a strong predictor.
- **Costs.** Fixed-genus point counting is polynomial in $\log p$ (Pila-type), but genus-3 constants are severe and I did not price them. Decoding and verification come on top.
- **Prior art (second-hand).** Kohel–Shparlinski Theorem 1, as recorded in H004/H026. H017 and H019 raised this family only as a heuristic.
- **Self-screen (exact, new to the records).** Write $F(kG)=\sum_i g(i)\,h(i+k)$ and use normalized log-Fourier transforms. Then
  $$\hat F(t)=q\,\hat g(-t)\,\hat h(t),\qquad |\hat F(t)|\le \frac{(c\,d_u\sqrt p)(c\,d_v\sqrt p)}{q}=O(d_u d_v)\ \text{ for every } t,$$
  while $\|F\|$ is of order $\sqrt p$. So the bias toward any single additive character is $O(d^2/\sqrt p)$, and parity bias picks up only an extra $\log q$. Aggregating does not amplify the linear signal beyond what its two factors already had.
- **Unsupported assumption.** The Kohel–Shparlinski nondegeneracy conditions and the pole conventions must hold for both factors. Nonlinear or multi-query uses are not excluded. Used as a matching key, though, $F$ is just an expensive hash of $x(Q)$ inside ordinary baby-step giant-step.
- **Cheapest falsifier.** Already applied: the identity above. Checking it numerically on a tiny curve is optional and was not run.
- **Verdict.** Rejected for linear decoding only. This is not a ban on point counting.

## Card 2: Compact-coset partner detector (Lucas-ladder resultant)

- **Operator.** Take an explicit list $A$ with polynomial $a(X)$ of degree $s$, and the large set $B_{n,d}=\{R: x(R)^n=d\}$ with $n\mid p-1$. Write $S_3=\alpha Y^2+\beta Y+\gamma$ in $Y$, where $\alpha=(X-x_Q)^2$. Then
  $$\mathrm{Res}_Y\big(Y^n-d,\ S_3(X,Y,x_Q)\big)=\gamma^n-d\,U_n+d^2\alpha^n,$$
  with $U_0=2$, $U_1=-\beta$, $U_k=-\beta U_{k-1}-\alpha\gamma U_{k-2}$ and $U_{2k}=U_k^2-2(\alpha\gamma)^k$. Run the ladder in $\mathbb F_p[X]/(a)$ and take a gcd with $a$. The case $X=x_Q$ needs separate handling.
- **Cost and coverage.** The test decides whether $Q\in\pm A\pm B$ in $\tilde O(s\log p)$ and covers up to $4sn$ signed sums, with $n$ as large as $p-1$, without listing $B$.
- **Self-screen.**
  - Because membership in $B$ is a compact test (one exponentiation), simply listing $A$ and testing each member decides the same question in the same $\tilde O(s\log p)$. The resultant buys nothing asymptotically.
  - Logs of members of $B$ are unknown. Multiplicative cosets of $x$-values are not structured in the log, except for automorphism orbits of size at most 6.
  - Two-level index-calculus schedule: $J$ queries, $s$ small-base points, $R$-collisions to eliminate the large base, and a uniform-landing heuristic. This needs $J\gtrsim q\sqrt{2/(sn)}$, so work $\gtrsim\sqrt2\,s\sqrt q$ for every $s$. Each such collision is literally a direct two-term relation, so the large base only acts as a filter.
- **Prior art (second-hand).** H019 resultant evaluator, H004 PKM/YYTK.
- **Verdict.** The identity is exact. The claimed operator gain is rejected for this schedule only.

## Card 3: Gauss-period descent of the pairing value

- **Operator.** Compute $\zeta^k=e_q(Q,H)\in\mathbb F_{p^{k_e}}$, with $k_e=\mathrm{ord}_q(p)$ and $d=(q-1)/k_e$. The label $L(Q)=\mathrm{Tr}(\zeta^k)$ is a Gauss period. It identifies the class of $k$ in $\mathbb F_q^*/\langle p\rangle$, assuming the $d$ periods are distinct mod $p$ (unverified, needs a check).
- **Hoped-for gain.** Split the search into a class search of size $d$ and a position-in-orbit search of size $k_e$. That is about $2q^{1/4}$ steps at the balanced point.
- **Costs.**
  - Each step costs $\tilde O(k_e\log q)$ (an exponentiation in $\mathbb F_{p^{k_e}}$), or $O(d)$ if the Galois action is applied as a polynomial on the $\mathbb F_p$ periods.
  - Finding $H$ costs $\tilde O(k_e^2\log p)$ (cofactor exponentiation). The pairing costs $\tilde O(k_e\log q)$. Memory is $\sqrt d$ labels.
- **Self-screen.** Total work is $\tilde O(\sqrt{q\,k_e}+k_e^2)$, which is at least $\sqrt q$ for every $k_e$. The $\mathbb F_p$-period representation gives $\tilde O(d^{3/2})$ for the class search, also no better. The split does beat naive baby-step giant-step inside $\mu_q$ by $\sqrt{k_e}$, which is expected prior art (Frobenius equivalence classes), not ECDLP progress.
- **Unsupported reopening assumption.** A way to obtain $\mathrm{Tr}(e_q(Q,H))$ in $o(k_e)$ without materializing the pairing value. The norm route is trivial: $\mathrm{Tr}(H)=0$ on the $p$-eigenline, consistent with H027.
- **Relation to existing records.** This adds a cost ledger to H027's trace/V-ambiguity identity. It is not a new invariant.

## Gate G: interval-product reduction (a restatement, not a new operator)

Suppose some algorithm evaluates $\Pi_L(\alpha)=\prod_{j\le L}(\alpha-x(jG))$ at any $\alpha$ in $\tilde O(L^\theta+S)$. Signed bisection then solves ECDLP in $\tilde O(q^\theta+S\log q)$. Any "cube-root Vélu" therefore counts as a full ECDLP improvement and should be reviewed under that standard. The three-level decomposition still needs H019's missing truncated-norm step.

The compact polynomials I could build ($\psi_n$, $\phi_n-x\psi_n^2$, Frobenius-based ones) have root sets on the $q$-part that are empty, a single point, or all of $E(\mathbb F_p)$. That is an observation about my own attempts, not a proof that no compact, log-structured, non-subgroup set exists.

## Other constructions that collapsed into existing records

- **Correspondence-branch relations.** These have a sum rule $R_1+R_2=\tau P$ but add one new unknown per point. Under a uniform-collision heuristic they need about $q$ nodes. This is GLUE/N2 territory (H013, H018, H036).
- **Kummer coboundary of the rational $q$-isogeny with kernel $E(\mathbb F_p)$.** It needs preimages over $\mathbb F_{p^q}$ (the Lang/elliptic-basis case, H026 C4).
- **$[u]$-orbit labels $\sum_i x(u^iP)$.** Labels cost $s$, giving $\sqrt{qs}$ overall (H017 card 3).
- **Special-$p$ half-size lifts.** The factor base is about $\sqrt p$ and linear algebra about $p$ (H013/H017 small-root and CSR).
- **Polynomial moment sketches.** These compute sums of products, not products, so detection needs degree $p$ (H019 Fourier count).
- **Xedni/CRT lifts, Hecke averages, $\mathbb F_{p^2}$ trace factor bases.** Covered by H015, H026 C3 and H021.

## Notes for the root's wave report

- **Best supported estimate:** the square-root reference, unchanged. Verified improvement: NONE.
- **Hypotheses tested:** Cards 1–3 above, all on paper.
- **Evidence:** the exact spectral identity for convolution counts, the Lucas-ladder resultant identity, and the Gauss-period ledger. All three are negative only for the schedules they price. No universal claims.
- **What would change the conclusion:** any one of these, built concretely and paid in full:
  - a set structured in the log with a compact (polylog-size) polynomial representation and none of the subgroup collapses above;
  - a way to compute Gauss periods of pairing values in $o(k_e)$;
  - a sub-$\sqrt L$ interval-product evaluator.

None is in hand. No experiment is warranted from this lens.

---
*Factory usage — local bridge. This turn: 1,942,108 tokens · ≈1,893,824 Factory credits. Saved session total: 1,942,108 tokens · ≈1,893,824 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
