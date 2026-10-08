# H006 minor mechanisms (Factory Opus), unverified raw report

Retained reviewer report. Root disposition controls accepted claims; this is not a Lean proof or experiment. Numerical estimates and broad exclusions require separate checking.

I found no procedure that beats the classical $\sqrt p$ baseline. The verified improvement over baseline remains NONE.

The useful output is one exact structural lemma. It turns every minor test in this framework, including tests after pivoting and Schur complements, into a single group-sum test. From it I get three concrete procedures, each with a stated cost and falsifier, and one precise gap. I made no edits, ran no experiments or code, and launched no children.

Sources I read: `RESEARCH_LOOP.md`, `research/findings/H004-recent-bridges-disposition.md`, arXiv 2310.04132v1 (full text), Cheng cs/0507026 (full HTML) and Li–Wan–Zhang 1501.01138 (abstract only). Guruswami–Sudan 1999 and the duality facts for algebraic-geometry codes (residue construction) are used from memory and were **not inspected** this session.

---

## 0. The lemma: each minor is one balanced subset-sum test

**Setup.** The paper's matrix M evaluates degree-$n'$ forms at $N=d+l$ points, with $d=3n'$. Restricted to the curve E, those forms give exactly $L(D)$ with $D=3n'\cdot O$. So the left kernel K is the dual of the elliptic code $C_L(D)$ on those points. Write K in reduced form $[A\mid J]$:
- the columns of A are indexed by points $S_1,\dots,S_d$;
- each row $i$ has its single 1 at the column of a point $R_i$.

**Lemma.** For any row set $\alpha$ and column set $\beta$ with $|\alpha|=|\beta|=k$:

$$\det A[\alpha\mid\beta]=0 \iff \sum_{i\in\alpha}R_i-\sum_{j\in\beta}S_j=\tau,\qquad \tau:=-\sum_{j}S_j .$$

**Proof sketch.**
1. $A[\alpha\mid\beta]$ is, up to sign, the maximal minor of K on the columns $T=\beta\cup\{R_i : i\notin\alpha\}$.
2. That maximal minor is nonzero exactly when T is an information set of K, which holds exactly when the complement $T^c$ is an information set of $C_L(D)$.
3. $T^c$ is an information set exactly when $L(D-\sum_{T^c})=0$.
4. That divisor has degree 0, so this happens exactly when $\sum_{T^c}\neq O$. Expanding $T^c=(\text{all }S\setminus\beta)\cup\{R_i:i\in\alpha\}$ gives the formula.

The proof does not depend on the characteristic. Generic position is assumed: distinct points, none equal to O.

**Pivoting and Schur complements.** By the Schur determinant formula,

$$\det H'[\alpha'\mid\beta'] = \frac{\det A[E\cup\alpha'\mid E\cup\beta']}{\det E}.$$

So every minor of a Schur complement tests the same kind of predicate, with a shifted target

$$\tau'=\tau-\Big(\sum_{E\text{ rows}}R-\sum_{E\text{ cols}}S\Big).$$

Choosing a different information set to pivot on gives another reduced form of the same type. **Scope:** this does not cover minors of an arbitrary product $UK$. Those are Cauchy–Binet combinations of minors and do not yield relations in the paper's sense.

**Closed form of the entries (sketch, not needed for any conclusion).** Using the dual-code residue construction with $\eta=dx/2y$:

$$a_{ij}=u_j\cdot\frac{\ell_i(S_j)}{x(S_j)-x(R_i)},$$

where $\ell_i$ is the line through $\tau$ and $R_i-\tau$, and the $u_j$ are nonzero column scalars. This is an elliptic analogue of a Cauchy matrix. It is the "structure beyond a generic dense matrix" in this lens. It also shows that every entry and every minor is a polynomial-time function of the points.

**Prior art.** Cheng (cs/0507026, Theorem 1 and Lemma 3) already proves that minimum weight $n-k$ in an elliptic code is equivalent to a k-subset summing to a target point. His Theorem 2 reduces ECDLP to the minimum-distance problem with $n\le\log q$; that reduction uses an oracle, so it is not an algorithm. The paper's Theorem 3.1 is the dual-code form of Cheng's Theorem 1. My refinement to individual minors uses the standard fact that information sets of a dual code are the complements of information sets of the code. Treat it as known in substance, not a discovery.

## 1. Consequences that settle open H004 disputes

**(a) A rigorous bound for index-only and outcome-adaptive families.** The paper picks multipliers $n_i$ uniformly at random. Each predicate is a nonzero linear form in independent uniform variables, with coefficients 1 or $-m$ and $m\neq0$. So each tested minor is zero with probability exactly $1/p$.

Take any sequence of tests chosen from indices alone, or chosen adaptively from earlier zero/nonzero outcomes only. Before the first success every outcome is "nonzero", so the path is fixed. Hence $\Pr[\text{success within } t \text{ tests}]\le t/p$, and the expected number of tests is at least about $p/2$. This holds after pivot conditioning too, because the predicates are unchanged. It covers all-2-minors, GESC, APM with any fixed deviation count, and every uniformly defined family of "initial minors".

**(b) The initial-minor conjecture fails in its uniform form.** For distinct subsets, the predicates are pairwise independent. A second-moment argument then gives $\Pr[\text{no zero maximal minor}]\le p/\binom{2l}{l}$. So if $\binom{2l}{l}\ge 2p$ and the family has size $F\le p/4$, then with probability at least 1/4 a zero minor exists but none lies in the family. A version where the family may depend on the matrix is an ECDLP algorithm in itself, so it is not a conjecture about minors.

**(c) The published numbers are consistent with independent $1/p$ trials.** These are hand calculations from the published values. Root should re-check them. The cofactor 2 (so $p\approx q/2$) is an assumption, and it matches Table 1's listed $\log_2 p$.

| Data point | My count / prediction | Paper |
|---|---|---|
| 25-bit field, $l=75$, zero almost-principal minors per size-2 principal block, $\binom{73}{n}^2/p$ with $p\approx2^{24}$ | n=2: 0.41; n=3: 230.6 (Poisson sd 15.2); n=4: 70,600 (sd 266) | 1; 230 (sd 15); 70,498 (sd 349) |
| Table 1, all 2×2 minors of a square $l\times l$ matrix, kernels needed $\approx p/\binom{l}{2}^2$ | 132 / 788 / 4,813 (40, 43, 46 bits) | 113.4 / 716.3 / 4,406 |
| APM, 3 deviations, $F\approx(l-1)\binom{l-2}{3}^2$ with $l=3\log_2 q$, expected kernels | 1.49 / 2.08 / 3.15 (45, 46, 47 bits) | 1.2 / 1.6 / 1.8 |

- The 25-bit row is the strongest check: the mean and the n=3 spread both match the Poisson prediction. The paper's "related partitions" clustering is not needed to explain it. The 2-deviation entry "1" is unexplained.
- The APM predictions run 1.3 to 1.8 times high. That is plausibly because I undercounted their family or because of p's exact value. I have not resolved it.
- I did not use GESC Table 2, because the block-size sweep is ambiguously defined.
- APM's apparent polynomial behavior comes from $l^7/36\approx p$ in the 28–47 bit range. For a fixed deviation count, the kernel count grows like $p/\text{polylog}$. Total work for GESC or APM, even with ratio hashing, is at least $p^{1-o(1)}$, which is worse than $\sqrt p$.

## 2. Mechanism A: hashed balanced-subset collision (explicit; equals the baseline)

**Procedure.**
1. Choose $S_j=a_jP$ and $R_i=-b_iQ$ with random known multipliers $a_j, b_i$, and compute $\tau=-\sum S_j$.
2. Enumerate $M$ k-subsets of rows in revolving-door order, keeping running sums $\sum_\alpha R$. Each step is one point addition, using precomputed differences $R_i-R_{i'}$.
3. Enumerate $M$ k-subsets of columns the same way, storing $\tau+\sum_\beta S$.
4. Hash both lists and look for a collision. A collision is a zero k-minor of A. No matrix generation and no linear algebra are needed.

**Recovering m.** A collision gives $m\sum_\alpha b_i\equiv\sum_{j\notin\beta}a_j\pmod p$. The coefficient of m is nonzero unless $\sum_\alpha b\equiv0$, which has probability $1/p$. This avoids the paper's Remark 2 issue about needing both P-type and Q-type points.

**Paid cost.**
- Choose l and k with $\binom{l}{k}\ge M\approx\sqrt{2p}$, so $l\approx\tfrac12\log_2 p+O(\log\log p)$.
- About 2M point additions, $M\log M$ for hashing, and memory for M points.
- Failures: coinciding points or a zero coefficient, each with probability $O(l^2/p)$.
- Matrix generation, if you insist on literal minors: N×d evaluation with the basis $x^i$, $x^iy$ plus one $O(l^3)$ elimination, which is negligible.
- **Total about $2\sqrt{2p}$ group operations.** This is baby-step giant-step with subset-sum baby steps, and its constant is worse than rho with the negation map.

**Variant A′ (pivot-steered walk).** Pivoting moves the target $\tau$ by one row-point minus one column-point. A walk over pivots that checks for 1×1 zeros by hashing is an r-adding Pollard rho walk, with $O(1)$ memory and about $\sqrt p$ work.

**Unsupported assumption.** None for the upper bound. Pairwise independence of distinct subset sums gives about $M^2/p$ expected collisions.

**Prior art.** Baby-step giant-step and rho; Cheng's subset-sum equivalence.

**Cheapest decisive falsifier (proposed only).** Have the lemma proof refereed. As a capped check, on a 13–16-bit prime-field prime-order curve with $l=d\le9$, compare the zero sets of all k ≤ 3 minors of A and of one Schur complement against the group predicate. The prediction is zero mismatches, using well under 1M events.

**Verdict.** This is the best batching of minor searches I can construct. It matches $\sqrt p$ and does not beat it.

## 3. Mechanism B: list-decoding interpolation as a batched minor finder

**Procedure.**
1. Use the code $C_L(D)$ with $D=d\cdot O$ on N points with known multipliers.
2. Take as the received word the evaluation of a random $g\in L((d+e)O)\setminus L(D)$, extending Cheng's Lemma 3 to general e.
3. Run Guruswami–Sudan interpolation (with multiplicities) and root-finding. This returns every $f\in L(D)$ that agrees with the received word in more than $\sqrt{Nd}$ positions. It tests exponentially many candidate subsets in one structured linear-algebra pass, which is genuinely more than a generic dense-matrix method.
4. A useful output has agreement exactly $t=d+e$. Then $g-f$ vanishes on a set T with $\sum_T=O$, which gives a relation; recover m as in Mechanism A.

**Expected yield (exact over the random g and multipliers).** Per call:

$$\mathbb E[\#\text{useful outputs}]\le\binom{N}{d+e}\cdot\frac1p\cdot\frac{q-1}{q^e-1},$$

and decoding requires $N<(d+e)^2/d$. Each extra agreement position e costs about a factor q, because the class of $g$ must point in the right direction in the e-dimensional quotient $L((d+e)O)/L(D)$. It buys only a binomial factor in return. With $u=e/d$:
- for $u\le1$, $(1+u)\ln\big(e(1+u)/u\big)\ge\ln q$ forces $u\lesssim e/q$, so $N\ge d\gtrsim q/e$;
- for $u\ge1$, the requirement forces $u\gtrsim q/e$.

Here $e\approx2.718$. **In every regime, $N=\Omega(q)$, so the work is at least q. It loses.**

**Prior art.** Guruswami–Sudan list decoding of algebraic-geometry codes (not inspected), Cheng's Lemma 3, and the Cheng–Wan view that discrete-log hardness lies beyond the Johnson radius (cited through Cheng).

**Unsupported assumption.** Decoding beyond the Johnson radius. Useful relations have agreement about equal to the code dimension, which is the capacity boundary.

**Cheapest falsifier (mathematical, proposed only).** Check the yield formula and confirm the inequality has no solution with $N\le\sqrt q$.

## 4. Mechanism C: codes folded along translation orbits (high risk; rough analysis)

**Procedure.** Pick points in orbits $\{P,P+T_0,\dots,P+(F-1)T_0\}$ under translation by a known point $T_0$. That is an automorphism of E. Then use capacity-style list decoding of the folded code, Guruswami–Xing style.

**Why it loses.** Zero sets must be unions of whole orbits, so there are only about $\binom{N/F}{(d+e)/F}$ candidates. Two cases:
- With e = 1 (no extra direction cost), the capacity gap must satisfy $\varepsilon<1/N$, and decoding time $N^{O(1/\varepsilon)}$ becomes exponential in N.
- With e > 1, $2^{N/F}\ge q^{\varepsilon N}$ forces $1/\varepsilon\ge F\log q$.

Either way the cost exceeds p. This is my estimate, not a proof.

## 5. Ideas rejected quickly

- **Steering by minor values.** Every value is a polynomial-time function of the points (see the closed form). The difference $\sum_\alpha R-\sum_\beta S-\tau$ is directly computable, so minor values add no information.
- **Arbitrary row-equivalent matrices.** Their minors do not yield relations.

## 6. The gap

Beating $\sqrt p$ in this lens requires one specific thing. Given 2l points with known multipliers (equivalently, the elliptic Cauchy matrix A), find one balanced pair with

$$\sum_\alpha R-\sum_\beta S=\tau$$

in $o(\sqrt p)$ work.

What is already ruled out:
- Generating two explicit lists loses by the AM–GM bound (Mechanism A).
- Index-only or outcome-adaptive selection of minors needs at least about $p/2$ tests (§1a).
- Interpolation-based list decoding reaches only the Johnson radius, where there are no relations unless $N=\Omega(q)$ (Mechanism B).
- Folding by translation is worse still (Mechanism C).

The missing primitive is an $\mathbb F_q$-algebraic method that, on random instances, finds one codeword of weight $n-k$ (one below the Singleton bound) in an elliptic code, or decodes at agreement $k+1$, in time $o(\sqrt q)$. Cheng proves the worst-case versions NP-hard, which says nothing either way about random instances. Since the matrix adds no information beyond the points, this primitive is the same thing as a coordinate-aware relation-finding algorithm for ECDLP. **I do not have one.**

**For root.** The best supported estimate is unchanged: classical $\sqrt p$. The only evidence above is the published data plus my hand arithmetic (no experiments). The next decisive step is to referee the lemma, then optionally run the capped 13–16-bit zero-set check from Mechanism A.
