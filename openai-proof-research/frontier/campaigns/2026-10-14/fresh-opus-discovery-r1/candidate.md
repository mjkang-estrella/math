# Candidate (fresh-opus-discovery-r1): optimality of the Friedgut–Kalai hypergraph exponent

**Family 186.** Status recorded at end: **PROVED, contribution TECHNICAL (not a substantial
nominee).** Frozen target = `TARGET.md` (unchanged; no weakened variant). Pin
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; pinned source theorems stipulated true.

## Notation
$n\ge r\ge3$, $E_{n,r}=\binom{[n]}r$, $G^{(r)}(n,p)$ = random $r$-uniform hypergraph
(each edge independently w.p. $p$). A hypergraph property is a Boolean function on
$\{0,1\}^{E_{n,r}}$ invariant under all vertex permutations. For nontrivial increasing
$\mathcal P$, $q(p)=\Pr_p(\mathcal P)$, $p_a=\inf\{p:q(p)\ge a\}$. Logs are natural.

## Theorem OPT
Fix an integer $r\ge3$ and set $t_n=\lceil c(\log n)^{1/(r-1)}\rceil$ with
$c=(r!/\log 2)^{1/(r-1)}$. Let
$$\mathcal P_n=\{H\subseteq E_{n,r}: H\ \text{contains a clique (complete }r\text{-graph) on }t_n\text{ vertices}\}.$$
Then $\mathcal P_n$ is a nontrivial increasing vertex-invariant property, its median
satisfies $p_{1/2}(\mathcal P_n)\to e^{-r!/c^{r-1}}=\tfrac12$, and there is a constant
$c_r>0$ (explicit below) such that for all sufficiently large $n$,
$$p_{0.9}(\mathcal P_n)-p_{0.1}(\mathcal P_n)\ \ge\ c_r\,(\log n)^{-r/(r-1)}.$$
Hence the exponent $r/(r-1)$ in the pinned uniform-influence / sharp-threshold upper bound
(hypergraph companion, $\mathrm{Var}_p f\le C_r(\log n)^{-r/(r-1)}I_p f$) is **best possible**
for every $r\ge3$.

## Lemma (exact overlap / second-moment bound)
Let $r,t_n$ be as above and let $p$ range so that $\mu=\mu(p)=\binom n{t_n}p^{\binom{t_n}r}$
lies in a fixed compact $[\mu_0,\mu_1]\subset(0,\infty)$. Let $X$ count $t_n$-cliques in
$G^{(r)}(n,p)$. Then
$$\mathbb E X^2\ \le\ (1+o(1))\,(\mu+\mu^2),$$
uniformly in this range, the $o(1)$ depending only on $r,c,\mu_0,\mu_1$.

### Proof of Lemma
Write $t=t_n$. Expanding the indicator product over ordered pairs $(T,T')$ of $t$-subsets,
grouped by $j=|T\cap T'|$ (shared edges $=\binom jr$, zero for $j<r$):
$$\frac{\mathbb E X^2}{\mu^2}=\sum_{j=0}^{t}T_j,
\qquad
T_j=\frac{\binom tj\binom{n-t}{t-j}}{\binom nt}\,p^{-\binom jr}.$$
Split the sum.

*Edge-disjoint part* ($0\le j\le r-1$): here $\binom jr=0$, so $T_j$ is exactly the
hypergeometric probability that a uniform $t$-set shares $j$ vertices with a fixed $t$-set;
thus $\sum_{j=0}^{r-1}T_j\le1$.

*Diagonal* ($j=t$): $T_t=\binom nt^{-1}p^{-\binom tr}=1/\mu$.

*Overlap part* ($r\le j\le t-1$): we show $\sum_{j=r}^{t-1}T_j=o(1)$. Since
$\mu\in[\mu_0,\mu_1]$, $p^{-\binom jr}=\Theta\!\left(\binom nt^{\beta_j}\right)$ with
$\beta_j=\binom jr/\binom tr$. Using $\binom{n-t}{t-j}\le\binom n{t-j}$ and
$\frac{\binom n{t-j}}{\binom nt}=\prod_{i=0}^{j-1}\frac{t-i}{\,n-t+j-i\,}\le\bigl(\frac{t}{n-t}\bigr)^j$,
and $\binom tj\le t^j$,
$$\log T_j\ \le\ j\log t+j\log\tfrac{t}{n-t}+\beta_j\,\log\binom nt+O(1)
\ \le\ -j\log(n-t)+\beta_j\,t\log\tfrac{ne}{t}+O(j\log t).$$
Now $\beta_j=\prod_{i=0}^{r-1}\frac{j-i}{t-i}=\frac jt\prod_{i=1}^{r-1}\frac{j-i}{t-i}$.
For $j<t$ each factor $\frac{j-i}{t-i}<\frac jt$ (equivalently $i(t-j)>0$), so
$\beta_j\,t<j$; moreover dropping factors $<1$ gives
$\beta_j\,t\le j\,\frac{j-1}{t-1}$, hence
$$j-\beta_j t\ \ge\ j\Bigl(1-\tfrac{j-1}{t-1}\Bigr)=\frac{j(t-j)}{t-1}.$$
Since $\log\tfrac{ne}{t}\le2\log n$ and $\log(n-t)=\log n+o(1)$,
$$\log T_j\ \le\ -\frac{j(t-j)}{t-1}\,\log n\,(1-o(1))+O(j\log t).$$
For every $j\in[r,t-1]$, $\frac{j(t-j)}{t-1}\ge\min\bigl\{\frac{r(t-r)}{t-1},\,1\bigr\}\ge\tfrac12$,
while $j\log t\le t\log t=o(\log n)$ (as $t=\Theta((\log n)^{1/(r-1)})$). Hence
$\log T_j\le-\tfrac14\log n$ for all large $n$, so each $T_j\le n^{-1/4}$, and with fewer
than $t$ terms, $\sum_{j=r}^{t-1}T_j\le t\,n^{-1/4}=o(1)$.

Adding the three parts,
$\mathbb E X^2/\mu^2\le 1+\tfrac1\mu+o(1)$, i.e.
$\mathbb E X^2\le\mu^2+\mu+o(\mu^2)=(1+o(1))(\mu+\mu^2)$ since $\mu$ is bounded. $\blacksquare$

## Proof of Theorem OPT
$\mathcal P_n$ is increasing (adding edges cannot destroy a clique), vertex-invariant
(clique containment is isomorphism-invariant), and nontrivial
($\varnothing\notin\mathcal P_n\ni E_{n,r}$). Let $q(p)=\Pr_p(X\ge1)$; it is continuous and
strictly increasing with $q(0)=0$, $q(1)=1$, so the quantiles $p_a$ are unique.

Two-sided control of $q$ by the mean:
- (Markov) $q(p)\le\mu(p)$.
- (Paley–Zygmund + Lemma) $q(p)\ge\dfrac{\mu^2}{\mathbb E X^2}\ge(1-o(1))\dfrac{\mu}{1+\mu}$.

At $p_{0.1}$: Markov gives $\mu(p_{0.1})\ge0.1$; Paley–Zygmund gives
$0.1\ge(1-o(1))\mu/(1+\mu)$, hence $\mu(p_{0.1})\le\tfrac19(1+o(1))$. So
$\mu(p_{0.1})\in[0.1,\,0.112]$.
At $p_{0.9}$: Markov gives $\mu(p_{0.9})\ge0.9$.
Therefore
$$\frac{\mu(p_{0.9})}{\mu(p_{0.1})}\ \ge\ \frac{0.9}{0.112}\ \ge\ 8.$$
Because $\mu(p)=\binom n{t_n}p^{\binom{t_n}r}$,
$$\Bigl(\frac{p_{0.9}}{p_{0.1}}\Bigr)^{\binom{t_n}r}\ge8
\quad\Longrightarrow\quad
\frac{p_{0.9}}{p_{0.1}}\ge8^{1/\binom{t_n}r}\ge1+\frac{\log8}{\binom{t_n}r},$$
so
$$p_{0.9}-p_{0.1}\ \ge\ p_{0.1}\,\frac{\log8}{\binom{t_n}r}.$$
Now $\mu(p_{0.1})\ge0.1$ gives
$p_{0.1}\ge\bigl(0.1/\binom n{t_n}\bigr)^{1/\binom{t_n}r}=p_c\,e^{\,\log 0.1/\binom{t_n}r}
=p_c(1-o(1))$, where $p_c$ solves $\mu(p_c)=1$. By Stirling,
$\log\binom n{t_n}=t_n\log n-t_n\log t_n+t_n+O(t_n^2/n)$ and
$\binom{t_n}r=\frac{t_n^r}{r!}(1+O(1/t_n))$, so with $t_n=c(\log n)^{1/(r-1)}(1+o(1))$,
$$\log p_c=-\frac{r!\,(\log n-\log t_n+1)}{t_n^{\,r-1}}(1+o(1))
=-\frac{r!}{c^{\,r-1}}(1-o(1)),$$
since $\log t_n=o(\log n)$. Thus $p_c\to e^{-r!/c^{r-1}}=\tfrac12$ (by the choice of $c$),
so $p_{1/2}\to\tfrac12$ (the median has $\mu\approx1$) and
$p_{0.1}\ge\tfrac12 e^{-r!/c^{r-1}}=\tfrac14$ for large $n$.
Finally $\binom{t_n}r=\frac{c^r}{r!}(\log n)^{r/(r-1)}(1+o(1))$, so
$$p_{0.9}-p_{0.1}\ \ge\ \underbrace{\frac{r!\,\log 8}{4\,c^r}}_{=\,c_r}\,
(\log n)^{-r/(r-1)}\,(1-o(1)).\qquad\blacksquare$$

**Consistency check (against the stipulated-true source).** The pinned hypergraph companion
gives $p_{0.9}-p_{0.1}\le2C_r(\log n)^{-r/(r-1)}\log 9$. Our lower bound $\sim c_r(\log
n)^{-r/(r-1)}$ is below it (since $C_r$ is large), so the two are consistent and the exponent
is matched from both sides.

## Operation-level comparison (bounded) — verdict: TECHNICAL
Per parent instruction, each proof operation is checked for a direct classical antecedent:
1. Clique-count first moment $\mu=\binom nt p^{\binom tr}$ — classical random (hyper)graph
   subgraph count (Erdős–Rényi; Bollobás).
2. Overlap decomposition $\mathbb E X^2=\sum_j\binom nt\binom{t_n}j\binom{n-t_n}{t_n-j}
   p^{2\binom{t_n}r-\binom jr}$ — the standard second-moment/correlation expansion, identical
   in form to the classical $K_t$ clique second moment in $G(n,p)$ (Matula; Bollobás) with
   $\binom j2$ replaced by $\binom jr$.
3. Two-sided transition via Markov + Paley–Zygmund — textbook second-moment threshold method.
4. Width-from-mean scaling $\Delta p\sim p/\binom{t_n}r$ — logarithmic-derivative (chain-rule)
   read-off from $\mu\propto p^{\binom{t_n}r}$; this is the parameter-substitution step.
5. Matching the exponent $r/(r-1)$ — obtained by choosing $t_n=\Theta((\log n)^{1/(r-1)})$ so
   $\binom{t_n}r\asymp(\log n)^{r/(r-1)}$, i.e. reading off the source's own exponent.

Every operation has a direct classical antecedent; the sole new content is substituting
$r$-uniform cliques into the known $r=2$ clique-sharpness example (FK96 p.2994 pointer) and
matching the source's exponent. **The matching exponent is not, by itself, a substantial
contribution.** Verdict: **TECHNICAL optimality example**, consistent with the parent's
assessment. Not nominated; no formal/review pipeline spent on it.

## Scope / status (honest)
- Frozen target (`TARGET.md`) proved **unchanged**; no weakened variant substituted.
- Proof status: **complete** (all steps above are elementary and self-contained; the only
  external inputs are the stipulated-true pinned source statements used for the consistency
  check, not for the proof).
- Contribution: **TECHNICAL** (see comparison). Campaign count unchanged (17/20); no result
  counted here.
- Novelty: **new to this corpus** (the pinned sources prove only the upper bound and give no
  $r\ge3$ optimality statement). Not screened against the external literature; likely known in
  spirit via the $r=2$ clique example. No worldwide priority claimed.
