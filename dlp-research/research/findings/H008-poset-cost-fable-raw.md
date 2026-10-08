# H008 new hyperplane paper: raw Factory Fable cost review

Provider acpRegistry_factory_droid, model claude-fable-5.1; request
ecdloop-h008-poset-cost-fable-20261008-r1. Raw report, not adopted wholesale.
Root does not accept its proposed matrix experiment, cap-fit estimate, unconditional
restart expectation, or exact independence after conditioning without review.
Arithmetic checks are source-formula checks, not ECDLP performance measurements.

# Research sub-agent report: arXiv 2607.09814 v2 (Mahalanobis, "Guess and Determine Attack on ECDLP")

Read-only. No edits, commits, experiments, children or infrastructure. Two calculator checks of the paper's binomial tables were run (arithmetic on published formulas, not an experiment on the hypothesis). **Verified improvement over the classical square-root baseline: NONE.** The paper itself says so in v2 ("no better than exhaustive search", Table 2; "poses no security risk").

## 1. Primary sources inspected (exact links)

| Item | Link | Status |
|---|---|---|
| Abstract page, current = v2 (6 Aug 2026, 25 KB) | https://arxiv.org/abs/2607.09814v2 | read |
| v2 full HTML (all sections, Alg. 1–2, Tables 1–3, Thms 1–5) | https://arxiv.org/html/2607.09814v2 | read in full (via saved artifact) |
| v1 full HTML (10 Jul 2026, 23 KB) | https://arxiv.org/html/2607.09814v1 | read: abstract, §1–3, §6 incl. Alg. 3 simulation + v1 Table 1, §7–8 |
| TeX source | https://arxiv.org/src/2607.09814v2 | not fetched (not needed) |
| Earlier "zero minor" paper (Abdullah–Mahalanobis, Exp. Math. 2025) | https://arxiv.org/abs/2310.04132 ; DOI 10.1080/10586458.2025.2525844 | already in H006 record; not re-read |
| INDOCRYPT 2018 Las Vegas paper (cited as [8]) | not online-inspected | **gap** (only its probability result is used, through the new paper's §6) |
| Code / data | none linked in v1 or v2; web search found no repository | **gap: implementation not available** |

v1 → v2 changes relevant here: v1 claimed "potential to be a polynomial time algorithm" and shipped a matrix-free **simulation (Alg. 3)** plus a 40–60-bit probability table; v2 withdraws the polynomial-time framing, deletes Alg. 3 and "simulation details" from the abstract, adds the outer factor $\binom{\ell'}{d}$ to the success probability, adds Table 2 ("no better than exhaustive search") and Table 3 (minimum defect vs bit size), and swaps $\ell'$ for $d$ inside eq. (4).

## 2. Executable schedule recovered (v2 Alg. 1 + Alg. 2, one recursion)

Notation: group order $p$ (prime), $n' \approx \log_2 p$, $\ell = 3n'$, $\ell' = \ell/2$, defect $d$.

1. **Construction.** Draw $2\ell$ distinct scalars; compute $P_i = n_iP$ ($\ell$ of them) and $Q_j = -n_jQ$ ($\ell$); evaluate degree-$n'$ monomials ($\binom{n'+2}{2}$ columns) at the $2\ell$ points; compute left kernel $\mathcal K$ ($\ell \times 2\ell$); row-reduce to anti-diagonal format $[A \mid J]$. Cost: $2\ell$ scalar mults $= O(\ell\log p)$ group ops, plus $O(\ell^4)$ field ops. Abort/redraw if a dense entry is zero (that already solves the DLP) or pivots fail: probability $O(\ell^2/p)$.
2. **Guess** $\mathtt a$: $\ell'$ of the $\ell$ dense ($P$-indexed) columns, uniformly. $\mathcal K' = \mathcal K[\mathtt a]^{\mathsf T}$ ($\ell' \times \ell$), re-reduced to anti-diagonal format: $O(\ell^3)$. This fixes the target $t = \sum_{i \in \mathtt a'} n_i$.
3. **Determine** (parallel over $\mathtt b$). For each of the $\binom{\ell'}{d}$ subsets $\mathtt b$ of $\ell'-d$ dense columns of $\mathcal K'$:
   - left kernel $T$ of $\mathcal K'[\mathtt b]$ (dim $d$): $O(\ell'^2(\ell'-d))$;
   - $d$ signature RREFs ($\ell' \times (\ell'-1+d)$ each), the other $\ell'$ signatures free from the anti-diagonal: $O(d\,\ell'^3)$;
   - **intersection-poset enumeration**: all $\binom{\ell'+d}{d-1}$ row-subsets of the $(\ell'+d)\times d$ signature matrix, one $(d-1)\times d$ right kernel each ($O(d^3)$, or $O(d^2)$ amortized with Gray codes/rank-one updates), normalize, hash. Memory: up to $\binom{\ell'+d}{d-1}$ entries of $d$ field elements **per $\mathtt b$** (tables are not shareable across $\mathtt b$ since $T$ changes).
   - stop at first hash duplicate.
4. **Empty attempts.** If no duplicate for any $\mathtt b$, the whole guess $\mathtt a$ is dead; redraw $\mathtt a$ (same point pool) and repeat 2–3. Everything above is charged.
5. **Extraction** (Alg. 2). Union of the two colliding $(d-1)$-sets must have size exactly $d$ (else "No result", a charged false alarm); map back to $\ell'$ $Q$-indices $U$; then $m \equiv \sum_{\mathtt a'} n_i \,/\, \sum_{U} n_j \pmod p$, verify $mP = Q$. $O(\ell)$ scalar ops plus one scalar mult.

What the whole thing computes, in the H006 group-sum lens: for a fixed guess $\mathtt a$, the determine step tests exactly the family of $\ell'$-subsets $U$ of the $\ell$ $Q$-columns that contain at least $\ell'-d$ members of the fixed dense half, for the predicate $\sum_{\mathtt a'} n_i - m\sum_U n_j \equiv 0$. Each (d−1)-set's kernel vector $v$ is "the unique element of $\mathcal K'$ vanishing on $\ell'-1$ prescribed columns"; a duplicate means it also vanishes on one more column. The hashtable detects that deterministically; there is **no birthday gain**, which the paper concedes in §5.2 ("we could not find a way to define the collision").

## 3. Full cost equation

Let $N_a$ be the number of **distinct** predicates tested per guess:

$$N_a = \sum_{i=0}^{d} \binom{\ell'}{i}^2 \;\approx\; \binom{\ell'}{d}^2 .$$

The paper's exponent is instead $N_{\text{paper}} = \binom{\ell'}{d}\binom{\ell'+d}{d}$, which counts each $U$ once per $(\mathtt b, x)$ pair covering it. Overcount factor $\approx \binom{\ell'+d}{d}/\binom{\ell'}{d}$: $2^{3.8}$ at $(\ell',d)=(300,20)$, $2^{6.8\text{–}7.8}$ at Table 2's implied parameters.

Per-guess success, given the group-sum lemma and general position (each predicate is a nonzero linear form in iid uniform scalars, hence exactly uniform; distinct predicates are pairwise independent), with $\mu = N_a/p$:

$$\frac{\mu}{\mu+1} \le \Pr[\text{guess succeeds}] \le \mu .$$

Expected total work (field operations), $c_{\ker} \in [d^2, d^3]$:

$$W \approx W_{\text{setup}} + \max\!\Big(1,\tfrac{p}{N_a}\Big)\cdot\Big[\,O(\ell^3) + \binom{\ell'}{d}\Big(O(d\,\ell'^3) + \binom{\ell'+d}{d-1}\,c_{\ker}\Big)\Big] + W_{\text{extract}} .$$

Using $\binom{\ell'+d}{d-1} = \binom{\ell'+d}{d}\cdot\frac{d}{\ell'+1}$, the enumeration term per guess is $N_{\text{paper}}\cdot\frac{d}{\ell'+1}\,c_{\ker}$, so whenever $N_a \lesssim p$:

$$W \;\approx\; p \cdot \frac{N_{\text{paper}}}{N_a}\cdot\frac{d}{\ell'+1}\cdot c_{\ker} \;=\; p \cdot \mathrm{polylog}(p).$$

The $d$-tradeoff is void: smaller $d$ lowers per-guess cost by the same factor it lowers per-guess success, so expected work stays $\Theta(p\cdot\text{polylog})$. "Polynomial time for fixed $d$" (v2 §1.1) is only the per-guess cost; the expected number of guesses is $p/\mathrm{poly}(\log p)$. Memory per $\mathtt b$ is $\binom{\ell'+d}{d-1}\, d\log p$ bits ($\approx 2^{64}$ bits at the 100-bit Table 2 row); a memoryless variant (check $vT$ against the $\ell'+1$ remaining columns directly) costs a factor $\ell'/d$ more time and does not change the exponent.

**Arithmetic verification of the paper's tables (my calculator check):**
- Table 3 (minimum $d$ for probability ≥ 0.5) reproduces exactly from eq. (4) with $\ell' = 1.5\log_2 p$ and $1/p$ per subset: $d = 15, 20, 24, 29, 38, 47$ at 150, 200, 250, 300, 400, 500 bits. With the corrected $N_a$ the same $d$ works except 500 bits ($d=48$). At those $d$, kernel computations $\binom{\ell'}{d}\binom{\ell'+d}{d-1} \approx 2^{150.1}, 2^{203.1}, 2^{248.4}, 2^{301.7}, 2^{400.3}, 2^{499.0}$, i.e. $\approx p$, versus $\approx 2^{\log_2 p/2}$ for rho.
- Table 2 does **not** reproduce at $\ell' = 1.5\log_2 p$ (that would give $2^{145}$ kernels at 100 bits, not $2^{101}$). It reproduces only with $\ell' \approx 0.6\log_2 p$ ($\ell' = 60, 60, 66, 72, 78$ for 100, 101, 110, 120, 125 bits), which the paper never states (it resembles the Table 1 shrink of $n'$ by $5+\mathtt{tt}$). At those parameters the paper's probabilities (≈ 1.0, listed as > 0.9) drop to **0.13, 0.33, 0.24, 0.08, 0.10** under the distinct-subset count, while work stays $2^{2\text{–}4.5}\cdot p$ kernel computations. Conclusion unchanged, but Table 2's ">0.9" rows are overcount artefacts.

Bottom line versus reference: at 100 bits, $\approx 2^{101}$ kernel computations $\times\, d^2 \approx 2^{109}$ field ops against rho's $\approx 2^{53}$, a factor $\approx 2^{56}$; the gap grows as $\sqrt p$.

## 4. Theorem / heuristic / conjecture

**Theorems (hold as stated, elementary linear algebra):** Thm 1 (zero minor of the tall $\mathcal K[\mathtt a]$ ⇔ zero maximal minor of $\mathcal K$ with the complementary anti-diagonal columns); Thm 2 (singular ⇔ central arrangement); Thm 3 + Cor. 3.1 (signature RREF computes $H\cap T$); Thms 4–5 (equal normalized penultimate intersections ⇒ zero minor; Alg. 2 recovers indices); count of kernel computations polynomial in $\ell$ for fixed $d$; zero minor ⇒ DLP relation (earlier work, equivalently the H006 group-sum lemma / Cheng). Exactly-$1/p$ per predicate and pairwise independence (hence the two-sided bound above) are theorem-level under the H006 pivot/general-position conditioning.

**Heuristics:** eq. (4) and Table 2/3 treat all $(\mathtt b, x)$ pairs as independent $1/p$ trials (overcounts distinct subsets, see §3); general position assumed throughout; "rare event inside a rare event" (two ultimate intersections sharing a vector) ignored; the $\binom{p}{k}$ partition correction uses $k=d$ in v2 and $k=\ell'$ in v1 (both negligible, $O(\ell/p)$ relative).

**Conjectures / speculation:** Table 1's "Pollard rho on penultimate intersections is comparable to original rho" is a comparison of $\log_2\binom{2\ell}{\ell-1}$ with $\log_2 p$ after shrinking $\ell$; no walk is defined and no analysis given (the paper: "further research is needed"). A function-iteration walk on normalized 1-dim subspaces would mostly produce useless revisits of the same $(\ell-1)$-set; a useful collision needs two distinct $(\ell-1)$-sets in the same cluster of size $\ell$, which is a fraction $\approx \ell/p$ of states. In the group-sum lens this is subset-sum hitting with $\ell+1$ targets; its birthday version is H006 Mechanism A (BSGS on subset sums, $\approx 2\sqrt{2p}$), not a win. Also speculative: two-step recursion helping at larger $\ell$; "structure underneath" closing remark.

## 5. Claimed sizes, runtimes, implementation, simulation match

- **Claimed solved sizes / runtimes:** none. §7: SageMath + FLINT 3.5.0 + Python multiprocessing, "proof of concept", "we do not have much data to share"; experiments used $d = 4$ or $5$ (field size unstated). v1 promised data "later"; v2 provides none. No repository, no URL, ChatGPT used for coding, preliminary version by Ansari Abdullah. **Implementation availability: not public.**
- **Simulation vs ECDLP matrices:** v1 Alg. 3 simulates with $2\ell$ distinct random integers, a random $r$ standing in for $m$, and tests $(r\cdot\sum_{\overline{U}} + m_0) \bmod p = 0$ over the same $(\mathtt a,\mathtt b,x)$ family. By the H006 lemma (det $A[\alpha|\beta]=0$ ⇔ group-sum relation, with fixed valid pivot), the matrix algorithm's zero-minor events on genuine $\mathcal K$ from $n_iP, -n_jQ$ are **identically distributed** to the simulation's integer events, up to $O(\ell^2/p)$ degenerate cases, provided the simulation's "first half of the Q-pool" is identified with the dense half chosen by the pivot (value-independent pivot order, exactly the H006 objection #1 conditioning). So the simulation is faithful, and it also shows the matrix is computationally irrelevant: the attack is an exhaustive structured subset-sum search. v2 deleting Alg. 3 removed the clearest statement of this.

## 6. Comparison with the old H006 minor corrections (not the same algorithm)

H006 analyzed 2310.04132's almost-principal-minor / GESC / all-2×2 searches. This paper is a different schedule: random $\ell'$-column guess, then defect-$d$ hyperplane-signature enumeration with hashing. But it falls inside H006 §1(a)'s class: minor selection depends only on indices (random $\mathtt a$, enumerated $\mathtt b, x$) and boolean outcomes (stop at first duplicate). Hence the H006 bound applies as a theorem: $\ge \approx p/2$ distinct predicates must be tested in expectation. The only genuine efficiency here is combinatorial: one $(d-1)$-kernel participates in $\ell'+1$ predicates, each predicate is paid $d$ times, net $(\ell'+1)/d$ predicates per kernel. That matches my cost equation and is polynomial, not exponential. H006's constant-success/second-moment correction, the distinct-sampling caveat, and the "matrix adds no information beyond the points" conclusion all carry over unchanged. New here relative to H006: the explicit overcount in the success exponent, the Table 2 parameter inconsistency, the per-$\mathtt b$ hashtable memory, and the empty-guess charge $p/N_a$.

## 7. Cheapest synthetic test that could alter the conclusion (design only; not run)

**Question.** Does the matrix algorithm (Alg. 1+2 on genuine ECDLP kernel matrices) hit at a rate above the group-sum prediction $N_a/p$, i.e. does $\mathcal K$ carry exploitable structure beyond the subset-sum predicate? Any statistically significant excess would reopen the file; exact agreement closes it for this algorithm.

**Design.**
- Instances: prime-order short-Weierstrass curves over $\mathbb F_q$ with group order $p \in [2^{10}, 2^{14}]$, 3 declared seeds × ~50 curves. Use $\ell = 12$ ($n'=4$, 24 points), $\ell' = 6$, $d = 2$: $N_a = 1 + 36 + 225 = 262$, so $\mu \approx 0.26$ at $p \approx 2^{10}$ and $\approx 0.016$ at $2^{14}$ (exercises the empty-guess regime).
- Arm A: faithful Alg. 1 + Alg. 2 in plain Python exact $\mathbb F_q$ arithmetic (no Sage available here; Gaussian elimination is ~50 lines). Arm B: v1 Alg. 3 integer simulation on the same scalars and the same $(\mathtt a,\mathtt b,x)$ family, with value-independent pivot order fixed in advance.
- Ledger per instance: scalar mults, field ops in construction, kernel computations, hashtable entries, empty $\mathtt a$-guesses, false alarms (union ≠ $d$), extraction verifications.
- Predictions: (i) per-$(\mathtt a,\mathtt b,x)$ event agreement A ⇔ B of 100% outside $O(\ell^2/p)$ degenerate instances; (ii) per-guess hit rate within the second-moment band $[\mu/(\mu+1), \mu]$ using $N_a$, and **below** the paper's $N_{\text{paper}}$ prediction; (iii) every hit extracts the correct $m$; (iv) total charged work $\approx p\cdot\frac{N_{\text{paper}}}{N_a}\cdot\frac{d}{\ell'+1}\cdot c_{\ker}$.
- Budget: $\le 10^6$ instrumented kernel computations, well under 60 s. Decisive threshold: matrix hit count exceeding the B-arm prediction by > 3σ over $\ge 10^5$ predicates.

Secondary falsifier (pure arithmetic, already done above): Table 3 reproduces from eq. (4); Table 2 requires an unstated $\ell' \approx 0.6\log_2 p$ and its probabilities collapse under the distinct count.

## 8. Explicit gaps

- INDOCRYPT 2018 [8] and Exp. Math. [2] not re-read this session; their Thms 4–5 / Cor. 1 are used only as cited by the new paper.
- No code or data exists to inspect; "rigorously tested and passed all tests" (§8) is unverifiable.
- Table 2's $\ell'$ is inferred, not stated; the inference reproduces all five checked rows, but the author's intended scaling is unknown.
- The Table 1 "rho on penultimate intersections" idea has no defined walk; my negative assessment of it is a paper argument in the group-sum lens, not a proof about every possible walk.
- No Lean statement and no numerical trial were produced or authorized; this report is paper evidence only.
