# Independent referee report: Section A, round 1

**Verdict: ACCEPT THE MAIN RESULT WITH CORRECTIONS.** The unbalanced incidence theorem has a valid complete proof after the exponent convention and minor bookkeeping are made explicit. Its substantive partition argument survives adversarial checking. **A1: accept the inequality with corrections; reject its exponent-comparison prose. A2: accept. A3: accept the elementary counting inequality; reject the claimed classical comparison.** The sharpness paragraph and assertion of established literature novelty require correction. These optional claims do not invalidate Theorem A.

Scope: only Section A of `proposals/combinatorics.md` and its corollaries. All upstream results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted as true; this report checks downstream deductions, not upstream proofs. No proposal files were edited.

## 1. Source statements actually checked

The revision in `sources/upstream.json` agrees with the assigned revision. I retrieved the following two files from their pinned raw URLs and verified byte-for-byte agreement with the local cache:

- [A power saving for planar unit distances, introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-saving-for-planar-unit-distances-September-23-2026/build/sections/00-introduction.tex), Theorem `thm:main`: there are absolute $C_0>0$ and $1\le\beta_0<4/3$ with $u(N)\le C_0N^{\beta_0}$ for every nonnegative integer $N$; pairs are unordered and endpoints distinct.
- [The same paper, incidence section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-saving-for-planar-unit-distances-September-23-2026/build/sections/01-incidence.tex), Proposition `inc:incidence`: the bound is $C\log^2(2+m+l)(m^{2/3}l^{2/3}+m+l)$. Its proof explicitly invokes the stronger classical bound without the logarithm. This proposition is not the new power-saving unbalanced theorem.

I also retrieved the actual family-167 companion, [The weak pinned planar distance theorem, introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-weak-pinned-planar-distance-theorem-September-23-2026/build/sections/introduction.tex), and checked statement headings and relevant terminology in its other section files. Its `thm:main` states uniform decay of the fraction of ordered pairs having distance-fiber size at least $N^s$, for each fixed $s>0$; `cor:pins` gives almost-every-pin distinct distances. Neither is Theorem A or A1–A3. The proposal's description of “the companion” as a balanced unit-distance statement is ambiguous/misleading: name the power-saving paper and distinguish the weak-pinned companion explicitly.

The standard partition input is supported by [Guth–Katz, Theorem 4.1](https://arxiv.org/pdf/1011.4105), or by [Sharir–Sheffer–Zahl, Theorems 2.1 and 2.2](https://arxiv.org/pdf/1208.0053), which separately state partitioning and the connected-component bound. The latter paper is incorrectly attributed to “Aronov et al.” in the proposal.

## 2. Main result: exact acceptable statement

> **Theorem (balanced-to-unbalanced unit-distance transfer).** Suppose $C_0>0$, $1<\beta<4/3$, and $u(N)\le C_0N^\beta$ for every positive integer $N$. There is a constant $K=K(C_0,\beta)$ such that, for every pair of finite sets $P,Q\subset\mathbb R^2$ with $m=|P|\ge n=|Q|\ge1$,
> \[
> I(P,Q)\le K\bigl(m^{2-\beta}n^{2\beta-2}+m\bigr).
> \]
> The sets may overlap. For $m<n$, interchange $m,n$. In particular the pinned upstream theorem supplies absolute constants $1<\beta<4/3$ and $K$ for this conclusion. Writing $\delta=4/3-\beta\in(0,1/3)$, the nonlinear term equals $(mn)^{2/3}(m/n^2)^\delta$.

Choose, for example, $\beta=(\beta_0+4/3)/2$, and retain $C_0$. This is legitimate since $N\ge1$, and makes every denominator in A1 positive. It is essential to redefine $\delta$ using this chosen exponent, rather than silently retaining $4/3-\beta_0$.

The main theorem itself also holds at $\beta=1$: the grouping argument immediately gives $I(P,Q)=O(m+n)=O(m)$. Thus enlarging the exponent is a clean shared convention for the theorem and corollaries, not a substantive obstruction to the main result. No variable exponent $1+o(1)$ may be inserted into this fixed-exponent statement without controlling constants.

### Complete verification of the proof

**Grouping.** For nonempty sets of sizes $a\ge b$, split the first set into at most $2a/b$ groups of size at most $b$. Each group's incidences give at most two ordered realizations of each unordered unit pair in a union of size at most $2b$, even when the sets overlap. Hence $I\le 2^{2+\beta}C_0ab^{\beta-1}$. Symmetry gives
\[
I\le A\bigl(ab^{\beta-1}+ba^{\beta-1}\bigr).
\]
Empty inputs have zero incidences and should be omitted from subsequent cell sums.

**Large imbalance and KST orientation.** With $d_p$ the number of incident circles,
\[
\sum_{p\in P}\binom{d_p}{2}\le2\binom n2,
\]
because each pair of distinct circles has at most two common points. Consequently $I^2/m-I\le2n(n-1)$, and $I\le m+\sqrt{2m}\,n$. This verifies the proposal's orientation of the $K_{2,3}$-free estimate. For $m\ge n^2$, it is (O$m$). Even the simpler inequality $d\le1+\binom d2$ gives $I\le m+n(n-1)\le2m$ in this range.

**Degree choice and partition.** In $n\le m\le n^2$, $D=\lfloor m/n\rfloor$ satisfies
\[
1\le D,\qquad m/(2n)\le D\le m/n,\qquad D^2\le m.
\]
The standard planar partition theorem can be normalized to degree at most $D$, at most $c_2D^2$ connected complementary cells, and at most $c_1m/D^2$ points per cell. If using the version of degree $O(\sqrt r)$, choose $r\asymp D^2$ with a sufficiently small absolute proportionality constant; bounded $D$ is covered by a line and a larger absolute cell constant. Thus the exact degree cap is legitimate, including $D=1$. There is no assumption that points avoid the zero set.

**Contained circles and complex irreducibility.** After a complex linear change of coordinates, the polynomial of a unit circle becomes (uv-1). Its quotient ring is $\mathbb C[u,u^{-1}]$, an integral domain, so the polynomial is irreducible over $\mathbb C$. This also explains why factoring the homogeneous quadratic part over $\mathbb C$ is irrelevant. If a real circle lies in (Z(f)), infinitely many common zeros and Bézout force its irreducible polynomial to divide (f). Different centers give non-associate factors. Hence there are $s\le D/2$ contained circles. Their total contribution is
\[
\sum_pd_p\le m+\sum_p\binom{d_p}{2}
\le m+2\binom s2\le m+D^2/4=O(m).
\]
This counts all points on these circles and is safe at singular points of (Z(f)) and when (f) has repeated factors.

**Other boundary incidences and crossings.** A noncontained circle has at most (2D) intersections with (Z(f)), again by Bézout. Its boundary incidences therefore contribute at most $2Dn\le2m$. Removing $t>0$ distinct points from a circle gives (t) connected arcs; if $t=0$, the circle is connected. Each connected piece lies in one connected complementary cell. Thus each noncontained circle meets at most $\max(1,2D)\le3D$ cells. Tangencies and repeated roots cause no problem.

**Cell sums.** Let $m_i,n_i\ge1$ for cells having both points and a noncontained circle. Then
\[
L\le c_2D^2,\quad m_i\le c_1m/D^2,\quad\sum_i n_i\le3Dn.
\]
For $\theta=\beta-1\in(0,1/3)$, concavity gives
\[
\begin{aligned}
\sum_i m_i n_i^{\beta-1}
&\le (c_1m/D^2)L^{2-\beta}(3Dn)^{\beta-1}\\
&\lesssim m n^{\beta-1}D^{1-\beta}
\lesssim m^{2-\beta}n^{2\beta-2},\\
\sum_i n_i m_i^{\beta-1}
&\le(c_1m/D^2)^{\beta-1}(3Dn)\\
&\lesssim n m^{\beta-1}D^{3-2\beta}
\lesssim m^{2-\beta}n^{2\beta-2}.
\end{aligned}
\]
The first substitution uses $D\ge m/(2n)$ and $1-\beta<0$; the second uses $D\le m/n$ and $3-2\beta>0$. The degree exponents are respectively $-2+2(2-\beta)+(\beta-1)=1-\beta$ and $1-2(\beta-1)=3-2\beta$. Summing the contained-circle, boundary, and cell contributions proves the theorem. No induction or unproved uniformity assertion is hidden here.

### Classical comparison and sharpness

The displayed exponent identity is correct. Moreover
\[
\frac{m^{2-\beta}n^{2\beta-2}}m=(n^2/m)^{\beta-1}\ge1
\]
when $n\le m\le n^2$, so the additive $m$ term does not destroy the claimed saving. For fixed $0<\varepsilon\le1$, throughout $n\le m\le n^{2-\varepsilon}$, the upper-bound scale improves by at least $n^{\varepsilon\delta}$, up to constants. At $m=n$, the exponent is $\beta$; take $P=Q$ and use $I(P,P)=2u(P)$ to recover the upstream order of growth.

The linear lower example is valid: put all $m$ points on the unit circle centered at one chosen member of $Q$, and add $n-1$ distinct centers. Then $I\ge m$. For $m\ge n^2$, the nonlinear term is at most $m$, so the order $\Theta(m)$ is sharp. There is no claimed or proved matching nonlinear lower bound in the remaining range.

**Delete the final sentence about “the conjectural $\beta=1+o(1)$.”** The pinned power-saving paper's introduction explicitly reports a fixed-power superlinear lower construction and a later bound $u(n)\gg n^{1.014114}$ along an unbounded sequence. Calling the historical near-linear conjecture a present conjectural target conflicts with the source's own account. Independently, a variable exponent cannot simply be substituted into this proof with a uniform constant. A safe replacement is: “The nonlinear exponent is inherited from the chosen fixed upstream exponent; no optimality is asserted for $n\le m<n^2$.”

## 3. Optional corollaries: separate decisions

### A1: accept the displayed bound after choosing $1<\beta<4/3$

Require integer $r\ge r_0\ge2$. The set $P_r$ is finite: every such point is an intersection of two distinct circles, so $|P_r|\le2\binom n2$. Mention this before applying a theorem about finite point sets. Empty $P_r$, and $n<r$, are harmless.

Writing $x=|P_r|$, the two cases $x\ge n$ and $x<n$, and absorption for $r\ge2K$, give exactly
\[
|P_r|\le K'\left(n^2r^{-3/(1-3\delta)}
+n^{(2+3\delta)/(1+6\delta)}r^{-3/(1+6\delta)}+n/r\right).
\]
All constants are absolute for the fixed upstream exponent. The $x>n^2$ case is already impossible when $r\ge2$; alternatively the proposal's large-degree exclusion works.

**Reject** “Both exponents of $r$ beat ... 3.” The first exponent exceeds 3; the second is strictly less than 3. Comparing only the $r$-exponent ignores the simultaneous improvement in the power of $n$.

Exact replacement prose:

> “The first term has decay exponent $3/(1-3\delta)>3$. The second term has decay exponent $3/(1+6\delta)<3$, accompanied by a smaller power of $n$. Its ratio to $n^2/r^3$ is $(r^2/n)^{9\delta/(1+6\delta)}$, so it improves that nonlinear scale for $r<\sqrt n$; for $r\ge\sqrt n$, it is at most (n/r).”

Indeed the second term divided by (n/r) equals $(n/r^2)^{(1-3\delta)/(1+6\delta)}$. This gives an honest comparison with the classical total bound $O(n^2/r^3+n/r)$, without falsely promising an improvement below its linear contribution.

### A2: accept, with precise interpretation of the count

Fix a finite configuration with two distinct marked points. For each ordered image pair at their fixed positive separation, there are exactly two ambient plane isometries sending the ordered source pair to it, and thus at most two restrictions to the configuration. Scaling the target set gives at most (2u$n$) ordered pairs. Therefore there are at most $4u(n)\le4C_0n^\beta$ distinct restricted maps. For a collinear configuration the two restrictions can coincide, which only helps. Every congruent subset is the image of at least one such map, so the subset bound follows too. Constants are uniform even in the chosen configuration.

This is a direct consequence of the balanced upstream theorem, not a new consequence requiring Theorem A. Describe the reduction as classical and the improved exponent as inherited; independent literature novelty for this corollary has not been established.

### A3: accept the sum bound; reject the stated comparator

Exact acceptable statement:

> “For any $n$-point planar set and any set of $k$ positive distances, the number of unordered pairs realizing one of those distances is at most $\min\{\binom n2,ku(n)\}\le \min\{\binom n2,C_0kn^\beta\}$.”

For each positive radius, rescale and use the definition of $u(n)$, then sum. The classical comparison justified by this argument is $O(kn^{4/3})$, with improvement $n^{-\delta}$ in that upper-bound expression, prior to imposing the trivial quadratic cap.

The proposed uniform bound $O(k^{2/3}n^{4/3})$ is not merely uncited: **as stated for arbitrary growing $k$, it is false.** Take an $n$-point square grid and let the distance set contain all its $k=O(n/\sqrt{\log n})$ distinct distances. All $\binom n2$ pairs are counted, whereas the alleged upper bound is $O(n^2/(\log n)^{1/3})=o(n^2)$. The grid's distance count is recorded in [Guth–Katz, introduction](https://arxiv.org/pdf/1011.4105) and the pinned weak-pinned paper's introduction. Thus delete the comparison and the claimed $k<n^{3\delta}$ crossover. The crossover algebra is formally correct between the two expressions, but cannot validate a nonexistent general comparator.

There is also a structural problem with a naive Pach–Sharir invocation: when $k$ radii vary, the maximum number of eligible circles through two fixed points grows with $k$; its multiplicity cannot be treated as an absolute constant.

Finally, revise the “open gap” saying extension to $k$ radii needs more than $u(n)$. A radius-by-radius extension is immediate, including $kK(m^{2-\beta}n^{2\beta-2}+m)$ for $k$ prescribed radii around a common $n$-point center set when $m\ge n$. A better dependence on $k$ is a legitimate further question; a bare extension is not an unresolved gap.

## 4. Novelty and final disposition

The two cited literature papers do not establish priority. [Sharir–Sheffer–Zahl](https://arxiv.org/pdf/1208.0053) primarily treats circles in three dimensions. [Sharir–Solomon–Zlydenko](https://arxiv.org/pdf/2003.02190) treats almost-two-degrees-of-freedom problems, including anchored unit circles in three dimensions and planar tangencies; its introductory unit-circle bound is the classical one. Neither provides this particular transfer theorem, but absence from two papers or a web search is not a proof of novelty. An improved bound confined to sufficiently unbalanced regimes also need not imply a balanced unit-distance improvement, so the proposal's historical inference is too broad.

Use this final novelty phrasing:

> “This is a standard polynomial-partitioning transfer of the pinned balanced unit-distance estimate to unequal point and center sets. The resulting power-saving statement was not found in the checked upstream manuscripts or the cited references. We regard it as a new-to-this-project downstream corollary; priority or new-to-literature status has not been established.”

**Accept after corrections:** Theorem A and its full proof; the claimed power saving on $n\le m\le n^{2-\varepsilon}$; linear sharpness for $m\ge n^2$; A1's formula; A2; A3's elementary sum bound.

**Reject/remove:** A1's “both exponents” sentence; A3's claimed uniform classical comparator and its crossover; the present-tense near-linear conjectural sharpness discussion; unconditional literature-novelty language; the assertion that any extension to finitely many radii needs an additional theorem.

Validation was analytic: independently derived degree and cell exponents, handled zero-set degeneracies and overlapping point/center sets, verified the source statements against pinned bytes, and supplied a counterexample to the disputed comparator. The proposal's lattice experiment about congruent copies is not evidence for the incidence theorem and was not used as such.
