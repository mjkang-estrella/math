# Frozen target — family 186 (DRAFT, pre-proof)

## Setting (matches pinned sources)
For integers $n\ge r\ge3$, $E_{n,r}=\binom{[n]}{r}$, $G^{(r)}(n,p)$ = random $r$-uniform
hypergraph (each $r$-edge present independently w.p. $p$). A hypergraph property is a
Boolean function on $\{0,1\}^{E_{n,r}}$ invariant under all permutations of $[n]$.
For nontrivial increasing $\mathcal P$, $q(p)=\mathbb E_p[\mathbf 1_{\mathcal P}]$ and
$p_a=\inf\{p:q(p)\ge a\}$.

## What the pinned sources already prove (PAID — do not re-prove)
- Graph paper (r=2): $\mathrm{Var}_p(f)\le 2^{17}(\log n)^{-2} I_p(f)$ for every
  vertex-invariant Boolean $f$ (no monotonicity); threshold width
  $p_{1-\varepsilon}-p_\varepsilon\le 2^{19}(\log n)^{-2}\log(1/2\varepsilon)$.
  Optimality for $r=2$ is pointed to (clique example, FK96 p.2994).
- Hypergraph paper (r>=3): $\mathrm{Var}_p(f)\le C_r(\log n)^{-r/(r-1)} I_p(f)$; width
  $\le 2C_r(\log n)^{-r/(r-1)}\log((1-\varepsilon)/\varepsilon)$.
  **No optimality/lower-bound statement is made for $r\ge3$.**

## Frozen target (Theorem OPT, new to corpus)
For every fixed integer $r\ge3$ the exponent $r/(r-1)$ is optimal: there is $c_r>0$
such that for all sufficiently large $n$ there is a nontrivial increasing vertex-invariant
$r$-uniform hypergraph property $\mathcal P_n$ with median $p_{1/2}\in[\tfrac14,\tfrac34]$
and
$$ p_{0.9}(\mathcal P_n)-p_{0.1}(\mathcal P_n)\;\ge\; c_r\,(\log n)^{-r/(r-1)}. $$
Equivalently the uniform-influence bound is tight up to the constant $C_r$.

## Witness construction
$\mathcal P_n$ = "$G^{(r)}(n,p)$ contains a complete $r$-graph (clique) on $t_n$ vertices",
$t_n=\lceil c(\log n)^{1/(r-1)}\rceil$ for a suitable constant $c=c(r)$.

## Unpaid operation (the actual estimate)
Second-moment control of the $t$-clique count $X$ at $\mu=\mathbb E X=\Theta(1)$:
$\mathbb E X^2\le(1+o(1))(\mu+\mu^2)$ in the regime $t=\Theta((\log n)^{1/(r-1)})$,
$p\in[\tfrac14,\tfrac34]$. Overlap pairs sharing $j$ vertices contribute
$\approx \binom{t}{j}(t/n)^j\,\bigl(\binom nt/\mu\bigr)^{\binom jr/\binom tr}$; the
$j=r$ term is $\asymp t^{2r}/n^r\to0$ and the $j=t-1$ term is $\asymp t^{r+1}/n^{r-1}\to0$;
intermediate $j$ are dominated. Then Markov + Paley–Zygmund give
$\Pr(X\ge1)\in[(1-o(1))\mu/(1+\mu),\min(\mu,1)]$, so $\Pr$ transitions from $0.1$ to $0.9$
over $\mu$ in a constant ratio, i.e. relative $p$-width $\Theta(1/\binom tr)
=\Theta(t^{-r})=\Theta((\log n)^{-r/(r-1)})$. Since $p_c=\exp(-r!/c^{r-1})(1+o(1))$ is
bounded away from $0,1$, the absolute width is $\Theta_r((\log n)^{-r/(r-1)})$.

## First concrete derivation (location)
$\mu(p)=\binom nt p^{\binom tr}$. $\mu=1$ with $t=c(\log n)^{1/(r-1)}$:
$\binom nt\approx e^{t\log n}=\exp(c(\log n)^{r/(r-1)})$, $\binom tr\approx t^r/r!
=c^r(\log n)^{r/(r-1)}/r!$, so $p_c=\exp(-r!/c^{r-1})(1+o(1))\in(0,1)$ — a constant
strictly between $0$ and $1$, so the median is interior and the width is a genuine
absolute $p$-width.

## Substantiality flag (for parent judgment)
New work = the $r\ge3$ clique second-moment in the polylog regime + recognizing this
saturates the source's new exponent. It mirrors the known $r=2$ clique pointer, so there
is a ROUTINE-GENERALIZATION risk. Harder alternative if rejected: optimal thresholds under
symmetry strictly weaker than $S_n$ (cyclic/affine) — genuinely open, likely a checkpoint.

## Paid/avoid boundaries
- Hypergraph threshold/influence UPPER bound (all $r\ge3$): PAID by the 186 companion.
- Containment threshold LOCATION ($p_c$ vs $p_E$): family 176 (claimed; different question).
- Multicolor/non-Boolean alphabet, product-alphabet, chain-rule parameter swaps: routine —
  NOT proposed.
