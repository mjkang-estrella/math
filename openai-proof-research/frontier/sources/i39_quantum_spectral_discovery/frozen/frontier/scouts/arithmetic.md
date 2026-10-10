# Arithmetic frontier scout: a three-point Chowla bridge and its obstructions

Date: 2026-10-08. Accepted upstream revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of [openai/math](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). All pinned upstream theorems are assumed true. This report does not audit them.

**Outcome: no complete new named conjecture or meaningful new arithmetic case is proved here.** The main attempted advance is a midpoint-weighted divisor-graph route to ordinary three-point Chowla. A precise conditional bridge is proved below, but its two genuinely arithmetic estimates remain unproved. Two tempting generic shortcuts are disproved by explicit examples. These are research diagnostics, not a replacement for the requested breakthrough and not claims of new-to-literature theorems.

The earlier power-free conditioning, divisor-overlap, inverse-sine, and undecidability corollaries were excluded. The complete 719-manuscript/372-family catalogue and the complete preprints tree were screened for relevant statements; actual source statements and proof mechanisms were inspected for the selected route. This is not a claim to have read all 719 proofs or to have proved formal independence from their conjunction.

## 1. Named targets and observed MathDB significance

The observations below were obtained from MathDB on this date. Numerical significance scores and a stable global rank were **not visible**. The unlabeled counters beside entries were not interpreted as scores. MathDB's public status summaries are not authoritative about what follows after accepting this corpus.

- **Riemann hypothesis**, [MathDB 315854](https://mathdb.com/p/315854/riemann-hypothesis): explicitly one of the homepage's **Featured Problems**, and in its Millennium Prize Problems collection. Target: every nontrivial zero of zeta has real part (1/2). Family 003 gives zero-freeness only for real part greater than (7/8), with no endpoint assertion. No RH theorem was found elsewhere in the catalogue. Functional-equation reflection leaves the entire strip (1/8\le\Re s\le7/8); it does not iterate to the critical line.
- **Birch–Swinnerton-Dyer**, [MathDB 315850](https://mathdb.com/p/315850/birch-and-swinnerton-dyer-conjecture): also explicitly **Featured**, and in the Millennium collection. Remaining target includes curves with full (q)-power Selmer corank at least two at every prime. Family 002 already proves the complete leading-term formula, rank equality, and finiteness of Sha whenever one such corank is zero or one; family 006 already supplies density-one twist consequences. Neither is a new target.
- **abc**, [MathDB 343078](https://mathdb.com/p/343078/the-abc-conjecture): the retrieved page explicitly displays **Celebrated**. Target: for every (\epsilon>0), finitely many coprime positive (a+b=c) have (c>\operatorname{rad}(abc)^{1+\epsilon}). The squarefree/power-free density results in family 020 concern typical values of fixed polynomials, not exceptional height bounds uniform over all triples. No route from those density statements to abc was established.
- **Higher Chowla**, [MathDB 382364](https://mathdb.com/p/382364/chowla-s-conjecture-for-liouville-correlations) and [383276](https://mathdb.com/p/383276/chowla-s-conjecture): present in the analytic-number-theory listing; entry 382364 records 17 source papers. No high-rank/Featured/Celebrated badge was verified for this target. Target: for every fixed finite set of distinct nonnegative shifts (h_1,\ldots,h_k),
  \[
  \frac1N\sum_{n\le N}\prod_{j=1}^k\lambda(n+h_j)\longrightarrow0,
  \qquad \lambda(n)=(-1)^{\Omega(n)}.
  \]
  Family 007 settles (k=2), not (k=3). This was chosen for the substantive proof attempt because the corpus supplies an unusually concrete graph mechanism to extend. That choice is a research judgment, **not a verified MathDB ranking**.
- **Prime tuples**, [MathDB analytic-number-theory listing](https://mathdb.com/database?tag=analytic-number-theory), including its Hardy–Littlewood and Bateman–Horn entries: no significance badge verified. Binary Liouville cancellation has error on the scale (N), while twin primes occupy a set of order (N/(\log N)^2). Bounded multiplicative inputs in family 007 do not include the unbounded von Mangoldt weight. Families 011/012 control factor-size laws and family 029 supplies a primitive-root lower bound; none states the required prime-tuple asymptotic. A fixed-residue approximation cannot isolate primes with an error smaller than their density. No prime result is proposed.

Two further BSD escape routes fail before any deep input: (E(\mathbb Q)\hookrightarrow E(K)) prevents base extension from lowering Mordell–Weil rank; a rational isogeny preserves rank. Twisting changes the curve, and density-one BSD for twists does not settle a prescribed exceptional twist. No rank-two descent bridge was obtained.

## 2. Source contracts and duplication checks

All upstream files used here are catalogued in [the source catalogue](../sources/arithmetic/CATALOGUE.md), with full pinned URLs, SHA-256 hashes, and git blob hashes in [manifest.json](../sources/arithmetic/manifest.json). Twenty-four files were copied/retrieved and their git blob hashes checked against the complete pinned preprints tree. Copies are confined to this scout's source directory.

**U7. Binary correlations.** In [the actual introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/introduction.tex), `thm:q-affine` states: there exists an absolute (c>0) such that, for every fixed (a_1,a_2\ge1), (b_1,b_2\ge0) with (a_1b_2-a_2b_1\ne0),
\[
\left|\sum_{n\le X}\lambda(a_1n+b_1)\lambda(a_2n+b_2)\right|
\le C_{a_1,a_2,b_1,b_2}X/(\log X)^c\quad(X\ge3).
\]
It explicitly asserts no uniformity for growing coefficients. Its `thm:elliott` and `cor:affine` treat two bounded multiplicative functions when an original factor satisfies, for every fixed Dirichlet character (\chi),
\[
\inf_{|t|\le X}\sum_{p\le X}
\frac{1-\Re(f(p)\overline{\chi(p)p^{it}})}p\longrightarrow\infty.
\]
The shifted product (n\mapsto\lambda(n+h)\lambda(n+2h)) is not supplied as a multiplicative function, so it cannot be substituted as one factor.

The [qualitative graph setup](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/graph-setup.tex), `prop:graph-estimate`, bounds sums with **two arbitrary endpoint functions** (F(x)G(x+hd)), coefficients depending on (d), and the specified centered divisor kernel. Its bound is (L_0 B^{-1-c_*/2}) after division by the long interval length; the bias comparison scale is (L_0/B). It does not allow an arbitrary edge-dependent third function.

The [analytic transfer](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/analytic-transfer.tex), `prop:analytic-centering`, `eq:analytic-rough-target`, and `eq:analytic-overlap`, reduces a **binary** shifted convolution to a one-frequency Fourier integral. Its short-exponential-sum supremum stays outside the interval integral. Adding a third factor is not one of its stated estimates. Both qualitative and quantitative parts, the affine consequences, and the source bibliography were inspected for an existing higher-order assertion; none was located. The catalogue has only one manuscript in family 007.

**U145/U154. Mixing.** Family 145, [introduction, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/build/sections/01-introduction.tex), says every invertible mixing probability-preserving transformation is mixing of all finite orders as the pairwise time gaps diverge. Family 154, [introduction, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Pointwise-Multiple-Ergodic-Averages-for-Mixing-Transformations-October-4-2026/build/sections/introduction.tex), gives almost-everywhere convergence of (N^{-1}\sum_{k\le N}\prod_{j=1}^r f_j(T^{jk}x)) to the product of integrals in such a mixing system. These are growing-gap statements, not fixed-gap independence. The latter introduction explicitly describes its fourfold and distinct-slope companions; their described consequences still concern multiple-time ergodic averages, not fixed-shift Liouville correlations.

**U2/U3. Scope exclusions.** The current [full BSD introduction, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Birch-Swinnerton-Dyer-Formula-from-Low-Selmer-Corank-October-7-2026/build/sections/01-introduction.tex) explicitly retains the low-Selmer-corank hypothesis; even low Mordell–Weil rank alone is not substituted for it. Its current every-prime Selmer-converse companion introduction was also read. The [(7/8) manuscript, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex) states the finite-order Hecke result over (\mathbb Q(\sqrt{-3})), with its Dirichlet consequence. The catalogue's (11/12) and Siegel-zero companions do not advertise RH. No improved zero-free theorem is claimed here.

**Primary literature already beyond the proposed easy consequences.**

- Tao–Teräväinen, [arXiv:1708.02610v2](https://arxiv.org/html/1708.02610v2), Corollary 1.8: odd-order Liouville correlations vanish in logarithmic averages, including on intervals ([x_m/\omega_m,x_m]) with (\omega_m\to\infty). This is not a new case.
- Tao–Teräväinen, [arXiv:1809.02518v2](https://arxiv.org/html/1809.02518v2), Corollaries 1.14–1.15: ordinary odd-order Chowla and all length-three sign-pattern densities hold outside a set of scales of logarithmic density zero. Remark 1.11 explicitly explains why upgrading the exceptional set to natural density zero would yield all-scale cancellation. Thus merely proposing an exceptional-scale upgrade is not a novel reduction.
- Helfgott–Radziwiłł, [arXiv:2103.06853](https://arxiv.org/html/2103.06853), develops the binary divisibility-graph spectral method. Pilatte, [arXiv:2310.19357v3](https://arxiv.org/html/2310.19357v3), Theorem 1.1, Sections 3–5 and Appendix C, supplies the logarithmic binary improvement and the centered-graph/nonbacktracking architecture. The proposed midpoint insertion below is not claimed to invent those methods.
- Krishnamoorthy, [arXiv:2501.10962v2](https://arxiv.org/html/2501.10962v2), Theorem 1, treats the modified Liouville function attached to a prime set with convergent reciprocal sum. It does not establish ordinary three-point Chowla for the full prime set. Approximating the full Liouville function by this class loses the needed uniform error.

## 3. Main attempt: a midpoint-weighted divisor graph

The specific meaningful target is
\[
S_h(N):=\sum_{n\le N}\lambda(n)\lambda(n+h)\lambda(n+2h)=o(N)
\tag{T}
\]
for a fixed integer (h\ge1), ideally every fixed (h). Even (h=1) at every scale would go beyond U7 and the almost-all-scale literature above. With U7 and the prime number theorem, (T) for (h=1) would give density (1/8) for every consecutive length-three sign pattern by expanding its indicator. That implication is elementary; it is not the proposed innovation.

The additional factor is placed at the midpoint of the edge from (x) to (x+2hd). This preserves complete-multiplicativity transfer on the raw divisor side and identifies an exact operator estimate to investigate on the centered side.

### Proposition A: a conditional bridge, with complete proof

Fix (h\ge1). Suppose that for every (0<\varepsilon<1) there are a real (H\ge1), a finite nonempty set of positive integers
\[
\mathcal D\subset[H,(1+\varepsilon)H],
\]
positive weights (a_d), with (V=\sum_{d\in\mathcal D}a_d), and real numbers (g_{d,N}(x)) for (N\ge1), (1\le x\le\lfloor HN\rfloor), satisfying the following two hypotheses. These choices may depend on (\varepsilon,h), but (H,\mathcal D,a_d) are fixed before (N\to\infty).

Write
\[
F_h(x,d)=\lambda(x)\lambda(x+hd)\lambda(x+2hd),
\]
\[
R_N=\sum_d a_d\lambda(d)\sum_{x\le HN}1_{d\mid x}F_h(x,d),
\qquad
C_N=\sum_d\lambda(d)\sum_{x\le HN}g_{d,N}(x)F_h(x,d).
\]
The first hypothesis is the cubic centering/deletion estimate
\[
\limsup_{N\to\infty}\frac{|R_N-C_N|}{NV}\le\varepsilon. \tag{A1}
\]
Let (M_N=\lfloor HN\rfloor+2h\max\mathcal D). Define a real (M_N\)-by-(M_N) matrix by setting, for every indicated (x,d),
\[
(K_N)_{x,x+2hd}=\lambda(d)g_{d,N}(x)\lambda(x+hd),
\]
and setting all other entries to zero. There is at most one (d) for an entry. The second hypothesis, for the Euclidean operator norm, is
\[
\limsup_{N\to\infty}\frac{H\|K_N\|_{2\to2}}V\le\varepsilon. \tag{A2}
\]
Then (T) holds.

**Proof.** Complete multiplicativity and (\lambda(d)^2=1) give the exact identity
\[
R_N=\sum_d a_d S_h(\lfloor HN/d\rfloor).
\]
Indeed all three factors at (x=dm) acquire (\lambda(d)^3=\lambda(d)), canceled by the outside (\lambda(d)). Since (HN/d\in[N/(1+\varepsilon),N]) and every summand of (S_h) has modulus one,
\[
|R_N-VS_h(N)|\le V(\varepsilon N+1).
\]
For (u=(\lambda(1),\ldots,\lambda(M_N))), we have (C_N=u^{\mathsf T}K_Nu). Consequently
\[
|C_N|\le M_N\|K_N\|,
\quad M_N/N\to H.
\]
Divide the triangle inequality by (NV), apply (A1)–(A2), and obtain
\[
\limsup_N|S_h(N)|/N\le3\varepsilon.
\]
Finally send (\varepsilon\downarrow0). This proves the implication. No upstream theorem is required for this algebraic implication; upstream supplies the proposed choices and strategy for estimating its two hypotheses. ∎

**What is new in the attempted bridge, and what is not proved.** One would choose (g_{d,N}) from a centered, truncated divisor kernel modeled on U7, now with step (2hd). The new object is its Liouville-midpoint twist. In U7's parameters, the useful target is to beat (V/H\asymp L_0/B), after choosing an appropriate divisor bin. The existing graph saving is encouraging, but applies to the untwisted endpoint kernel only. Neither (A1) nor (A2) is proved here. Proposition A is a precise conditional reduction, not an arithmetic theorem resolving any case of Chowla and not a demonstrated new-to-literature reduction.

### Why centering is an independent obstacle

Already for a single prime (p), (a_p=1), and elementary centering (g_p(x)=1_{p\mid x}-1/p),
\[
R_N-C_N=\frac{\lambda(p)}p\sum_{x\le HN}F_h(x,p)
=-\frac1p S_{hp}(\lfloor HN\rfloor).
\]
This is another **three-point** correlation. When (H\asymp p), its trivial bound after division by (N) is of order one, not (o(1)). The actual U7 argument saves by combining many divisors and a binary short-interval Fourier calculation. It cannot be copied with a third factor silently absorbed into a bounded test function. Logarithmic cancellation of (S_{hp}) does not give the required terminal-scale bound.

### Why the trace expansion also changes

Consider the closed four-edge walk with increments (2hd,2he,-2hd,-2he), for distinct positive (d,e). Its four midpoint arguments are
\[
x+hd,\quad x+2hd+he,\quad x+hd+2he,\quad x+he.
\]
They are all distinct. The midpoint-twisted fourth trace therefore contains the product of Liouville at these four affine arguments. The edge coefficients also contain the specified periodic divisor weights. U7 does not provide cancellation for this four-point product even with the weights removed. Treating each new trace term by binary cancellation thus becomes circular or requires an additional higher-order theorem. This does **not** prove that an aggregate arithmetic trace estimate is impossible; it identifies why the available binary estimate cannot justify the proposed step term by term.

## 4. A generic midpoint transfer is false

### Proposition B: an exact spectral counterexample

For every odd prime (q), let (\chi:\mathbb F_q\to\{-1,0,1\}) be the quadratic character, extended by (\chi(0)=0). Define real matrices, indexed by (x,y\in\mathbb F_q), by
\[
A_{xy}=\chi((x+y)/2),\qquad
B_{xy}=A_{xy}\chi((x+y)/2).
\]
Then
\[
\|A\|=\sqrt q,\qquad \|B\|=q-1.
\tag{B}
\]
In particular, a uniformly bounded midpoint multiplier can turn a normalized operator of norm (q^{-1/2}) into one of norm (1-q^{-1}). There is no universal constant bounding the norm of a midpoint twist by the original norm.

**Proof.** The diagonal entries of (AA^{\mathsf T}) equal (q-1). For (x\ne z), substitution gives
\[
(AA^{\mathsf T})_{xz}=\sum_{t\in\mathbb F_q}\chi(t(t+1))=-1.
\]
For completeness, the number of pairs (t,v) satisfying (v^2=t(t+1)) is (q+\sum_t\chi(t(t+1))). The change to
\((2t+1-2v)(2t+1+2v)=1\) bijects these pairs with the (q-1) nonzero choices of the first factor. Hence the sum is (-1). Thus (AA^{\mathsf T}=qI-J), giving the first norm in (B).

Also (B_{xy}=1_{x+y\ne0}), so (B=J-P), where (P) is the permutation matrix for (x\mapsto-x). On constants its eigenvalue is (q-1); on their orthogonal complement its norm is one. This gives the second norm. ∎

This does not refute a Liouville-specific bound for U7's particular graph. It refutes the suggested functional-analytic shortcut “a bounded midpoint factor preserves spectral cancellation.” The example is multiplicative in the finite-field argument, but it is not a model satisfying all of U7's integer nonpretentiousness hypotheses.

A valid replacement exposes the loss. For any odd cyclic group and any (w), Fourier inversion gives
\[
\|A\circ w((x+y)/2)\|
\le\left(\sum_\xi|\widehat w(\xi)|\right)\|A\|.
\tag{B'}
\]
Here Fourier coefficients use normalized counting measure. Each Fourier term is a left and right diagonal unitary multiplication of (A), so the triangle inequality proves (B'). Boundedness or small individual Fourier coefficients does not bound this Fourier (\ell^1) norm uniformly. For the character example it is ((q-1)/\sqrt q), exactly the loss needed in (B). Accordingly ordinary exponential-sum cancellation for Liouville is not by itself the missing multiplier theorem.

## 5. Binary Chowla plus multiple mixing is insufficient as an abstract argument

### Proposition C: pairwise-independent, mixing signs with a biased fixed triple

There is a stationary strongly mixing process (X_n\in\{-1,1\}), indexed by all integers, such that
\[
\mathbb EX_n=0,\qquad \mathbb EX_nX_m=0\ (n\ne m),\qquad
\mathbb EX_0X_1X_2=1/7.
\tag{C}
\]

**Construction and proof.** Concatenate independent blocks. Choose the length (L) to be three or four with equal probability. A length-three block is ((U,V,UV)), where (U,V) are independent uniform signs; a length-four block has four independent uniform signs. Make the process stationary by giving the block containing the origin its size-biased law and choosing a uniform position within it. Equivalently, use the stationary finite Markov chain whose state is the complete signed block and the current position in it.

There are four possible length-three blocks and sixteen possible length-four blocks, hence (4\cdot3+16\cdot4=76) states. Within a block the next state increments its position; at a last position a fresh block is sampled. The chain is irreducible and aperiodic: all block choices have positive probability and return paths permit the relatively prime block lengths three and four. A sufficiently large transition power is strictly positive, so elementary finite-state coupling gives exponential convergence to stationarity. Its stationary two-sided shift and its sign factor are mixing (indeed mixing of all finite orders).

Condition on the unsigned block layout. Each sign is fair, and any two different signs within one block are independent; different blocks are independent as well. This proves the first two assertions in (C). A product of three consecutive signs has nonzero conditional expectation only if it is exactly one length-three block, in which case it equals one. The stationary probability of such a block starting at the origin is
\[
\frac{\Pr(L=3)}{\mathbb EL}=\frac{1/2}{7/2}=1/7.
\]
All other layouts leave either an independent fair sign or a proper, mean-zero subset of a length-three block. This proves the last assertion. ∎

Thus even full mixing, plus independence of every pair of coordinate signs, does not force fixed-triple independence. Birkhoff's theorem supplies sample sequences having all these ordinary correlation limits simultaneously. The example does not have Liouville's complete multiplicativity and does not refute Chowla or U145. It shows that a bridge using only coordinate pair correlations and mixing is false.

There are actually two gaps in the proposed U7+U145 deduction: U7 does not prove mixing for all cylinder functions of a Liouville Furstenberg system; and even if such mixing were established, U145 concerns **diverging gaps**, whereas (T) fixes (h). U154 similarly concerns (k,2k,\ldots), not (k,k+h,k+2h). Multiplicative rescaling requires its own arithmetic and scale-uniformity argument.

Nor do logarithmic or almost-all-scale results remove these gaps automatically. For a simple exact scalar example, let (N_j=2^{2^j}) and let (b(n)) be the indicator of the disjoint intervals ([N_j,2N_j]). Then
\[
\frac1{\log X}\sum_{n\le X}\frac{b(n)}n\to0,
\qquad \limsup_X\frac1X\sum_{n\le X}b(n)\ge1/2.
\]
Each completed interval contributes at most (\log2+O(1/N_j)) to the numerator of the first expression, and the number of intervals up to (X) is (O(\log\log X)). The second assertion follows at (X=2N_j). This is a counterexample to the averaging implication, not a multiplicative counterexample. Proposition C alone does not incorporate the already-known logarithmic odd-Chowla restriction; these obstructions must not be described as a single model satisfying every arithmetic input.

## 6. Validation and honest novelty boundary

Run
```
python openai-proof-research/frontier/experiments/arithmetic_obstructions.py
```
The exact-arithmetic checks verify (AA^{\mathsf T}=qI-J) and the twisted row sums for (q=5,7,11,17,31,101); the 76-state stationary law, zero pair moments at lags 1–16, and triple moment (1/7); and the complete-multiplicativity raw-transfer identity for a finite Liouville sample. Output is preserved in [validation.json](../sources/arithmetic/validation.json). The proofs above cover all stated parameters; the computations check algebra and implementation, not asymptotic truth.

Proposition A is **proved as a conditional implication**; (A1)–(A2) remain **unproved arithmetic hypotheses**. Propositions B and C and the scalar averaging obstruction are **proved counterexamples to generic routes**. No new arithmetic case, quantitative three-point bound, rank-two BSD statement, prime-tuple result, or RH improvement is established. The finite-field and renewal constructions use classical mechanisms; no literature priority is claimed for them.

The concrete continuation worth considering is an arithmetic estimate for the midpoint-twisted graph **together with** a trilinear centering estimate that beats its raw divisor mass at every terminal scale. A proof must address the new four-midpoint trace factors rather than invoke binary cancellation on them. Until those estimates are supplied, this branch should be recorded as an attempted bridge with explicit obstructions, not integrated into a solved-results index.

No shared index was edited, and no files were staged or committed. External MathDB pages were readable through web retrieval but direct Python downloads returned HTTP 403; the observation record distinguishes those facts rather than pretending a full local MathDB snapshot was saved.
