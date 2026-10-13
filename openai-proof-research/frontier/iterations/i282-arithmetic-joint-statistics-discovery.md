# I282 — Arithmetic joint-statistics discovery

2026-10-12. **Verdict: no substantial new finding nominated.** Discovery only, not independent acceptance. The user's twenty-finding objective and eleven accepted findings before pending R018 are unchanged by this report. All applicable pinned OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true; no upstream truth audit was performed.

The strongest focused target was a joint mesoscopic/macroscopic law for a prime predecessor. A complete restricted partial and an exact conditional reduction are proved, but the estimate needed for the full target is unpaid. The proof and significance status are deliberately separated.

## Exact full target and verdict

For a uniform prime `p∈(X,2X]`, let `V(p)` be the ranked prime-factor log partition of `p−1`, with multiplicity and normalization `log(p−1)`. Put `y=exp((log X)^(1/3))` and `A_X=(v_q(p−1):q≤y)`. Let `Q_y` have independent coordinates with

\[
 \Pr(W_q=0)=1-1/(q-1),\qquad \Pr(W_q=j)=q^{-j}\quad(j\ge1).
\]

The selected target is, for every fixed continuous real `H:[0,1]^k→R`,

\[
 \sup_{|\psi|\le1}
 \left|E[H(V_1,\ldots,V_k)\psi(A_X)]
       -(E_{PD(1)}H)E_{Q_y}\psi\right|\to0.
 \tag{M, UNPROVED}
\]

The supremum permits arbitrary `X`-dependent small-vector tests. It is total variation in that discrete vector with a fixed weak macroscopic mark. It is not a claim of total variation convergence of the discrete ranked partition to continuous PD. Conditional laws on moving events need probabilities bounded away from zero, unless a further relative error is supplied.

The exact sufficient unpaid step is, for every nonnegative such `H` with positive PD mean, some fixed `θ_H∈(0,1)` such that

\[
 \frac1{N_H}\sum_{\substack{d\le(2X)^{\theta_H}\\P^+(d)\le y}}
 (2^{\omega(d)}+\log y)
 \left|\sum_{\substack{X<p\le2X\\d\mid p-1}}H(V(p))
                        -\frac{N_H}{\varphi(d)}\right|\to0,
 \qquad N_H=\sum_{X<p\le2X}H(V(p)).
 \tag{B, UNPAID}
\]

Gorodetsky's actual arbitrary-distribution Kubilius corollary turns (B) into (M). This reduction is complete, but no claim is made that (B) follows from a fixed progression law or is necessary for every conceivable proof. The [analytic record](../experiments/i282_arithmetic_joint_statistics_discovery/analysis.md) gives the precise total variation bound, the mean normalization, and treatment of signed or zero-mean tests.

## Complete rigorous partial

Fix a positive number of long-prime slots `(X^{a_i},X^{b_i}]`, all `a_i>0`, with `Σb_i<1/2`. Let `T_X(n)` count the ordered distinct prime tuples in these slots whose product divides `n`. Then

\[
 \sup_{|\psi|\le1}
 \left|\frac1{\pi(2X)-\pi(X)}\sum_{X<p\le2X}T_X(p-1)\psi(A_X(p))
           -C_X^{\varphi}E_{Q_y}\psi\right|\to0,
 \quad
 C_X^{\varphi}=\sum_{\boldsymbol\ell}\frac1{\varphi(\prod\ell_i)}
       \to\prod_i\log(b_i/a_i).
 \tag{P, PROVED — TECHNICAL}
\]

This controls the **entire** small-factor valuation vector under the nonnegative long-tuple bias. The proof pays its uniformity: for smooth `d≤(2X)^θ` with `Σb_i+θ<1/2`, count primes in class one modulo `d∏ℓ_i`. The modulus determines its small and long parts uniquely, with at most the fixed slot permutation multiplicity. BV controls the summed remainder. Cauchy and Brun–Titchmarsh absorb the required `2^ω(d)+log y` weight, using an explicit Euler-product bound. Gorodetsky's Corollary 2.2 then applies to the tuple-biased random integer. The full proof, including normalization by the actual tuple mean and the strict exponent margins, is in [analysis.md §2](../experiments/i282_arithmetic_joint_statistics_discovery/analysis.md).

Finite combinations and compactly supported factorial tests below total mass `1/2` follow. The threshold is a limitation of this paid distribution budget, not a global impossibility result. P cannot identify all fixed ranked-factor tests; the high-mass region needed for full PD remains outside this argument.

## Exact source and overlap screen

Read the project instructions, pinned metadata, catalogue families 011/012 and the complete 13,223-entry preprint path listing (`truncated=false`). The catalogue identifies three manuscripts in 011 and one in 012. Fresh raw pinned source bytes were matched to their Git blob IDs in that listing; the full source URL, SHA-256, exact read ranges and retention status are in [input-authentication.json](../experiments/i282_arithmetic_joint_statistics_discovery/input-authentication.json).

Accepted R006, R008 and R010 were screened first. They already pay fixed progression conditioning, Liouville/squarefree independence and fixed factor-count residue modes. Completed I07 §9 and I18 give the decisive duplication boundary: J's exact `prop:mixed` and `eq:distribution-characters` factor the whole pair of fixed bin-count vectors. Thus full joint PD for consecutive integers is already a standard fixed-grid transfer from a stronger actual source. It was not inferred from the catalogue's largest-factor statement. I197's large-gap runs were screened and excluded; unrelated I99/I145/I204 hits were classified without replaying their histories.

Actual D master statements read include `thm:main`, `thm:type-II`, `thm:two-sided`, `thm:interior`, the full probability passage, and the relevant endpoint/extraction ranges. Actual J master statements include `thm:main`, `prop:mixed`, its marginal and short-average lemmas, distribution section, and final energy argument. S and E companion final theorem statements were checked. Read limits, including unread retained proof interiors, are explicit in [reading-and-failures.md](../experiments/i282_arithmetic_joint_statistics_discovery/reading-and-failures.md); no whole-corpus semantic audit is claimed.

At the selected cutoff, arbitrary small-vector weights violate D's inert-prime invariance. Its two-sided first core is specified, and its general graph pairing leaves comparisons whose endpoint estimates were proved for that core. Moving the small cutoff below all marks repairs the literal invariance failure but does not prove the needed changed Fourier, presieve or prime-discrepancy estimates. J keeps its grid, phases and auxiliary residue periods fixed in the inner counting limit. These interfaces do not provide a license for a growing vector or a rate.

## Counterexample to the shortcut and prior-art boundary

The analytic record constructs an explicit probabilistic model with an exact PD marginal, the exact whole `Q_y` small-vector marginal, and exact independence from every fixed finite set of valuations, yet a nonvanishing correlation between the largest PD part and parity of a moving tail of small-factor hits. It also proves that the tail's normalized log mass vanishes. Hence marginal laws and negligible small mass do not logically yield (M). This is an inference counterexample, not an arithmetic refutation of (M).

The strongest external collision is [Gorodetsky's arbitrary-distribution Corollary 2.2](https://arxiv.org/html/2608.14190v1#S2), combined with the classical restricted factorial mechanism covered by [Bharadwaj–Rodgers, Lemma 8](https://arxiv.org/html/2402.11884v4). P follows from these existing tools after standard remainder bookkeeping; it is therefore not promoted as a substantial discovery. Ford already supplies the small-vector marginal, and Tao–Teräväinen already have a quantitative moving-parameter smoothness law on their good endpoint set. Exact hypotheses and versions are compared in [literature.md](../sources/i282_arithmetic_joint_statistics_discovery/literature.md) and [primary-excerpts.md](../sources/i282_arithmetic_joint_statistics_discovery/primary-excerpts.md). No novelty claim rests on unsuccessful searches.

The completed contribution is P, the sufficient bridge (B) with its complete conditional proof, and the countermodel. There is no demonstrated new-to-literature theorem, no nomination for the quota, and no independent review verdict. All writes are confined to the assigned I282 paths; no shared-index edits, agents, numerical scans, staging, commits or publication occurred. Detached hashes accompany the handoff; the authentication JSON binds every other owned artifact and excludes its own circular self-hash.
