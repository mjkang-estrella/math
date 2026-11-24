# The two smallest nonmonomial coefficient-growth rates over $\mathbb F_2$

## Abstract

We prove Garbe’s Conjecture 3.7 for every binary polynomial with at least two nonzero terms. The smallest coefficient-growth rate is $3$, attained exactly by the similarity class of $1+x$. The next is $1+\sqrt{5}$, attained exactly by the class of $1+x+x^2$. As printed, the conjecture does not exclude monomials, and its first sentence fails for them: a monomial has rate $2$, and the zero polynomial has rate $1$ under coefficient-count growth. Lean proves both of these values. Lean also checks the theorem with $\lambda$ read as the growth rate $\lim_k r_f(2^k)^{1/k}$ of the cumulative count of nonzero coefficients of $f^n$, $n<2^k$, together with both equality characterizations. Garbe defines $\lambda$ as the Perron eigenvalue of Willson’s matrix. The identification of that eigenvalue with the growth rate is stated by the source, and is proved here by a short row-sum argument outside Lean. The proof projects factor multiplicities and delays the three-way choices in a finite section graph.

## Source statement and definitions

Kevin Garbe, *Patterns In The Coefficients Of Powers Of Polynomials Over A Finite Field*, arXiv:1304.4635v1, §3, Conjecture 3.7 (MathDB 325374) reads as follows. [Garbe, arXiv:1304.4635v1](https://arxiv.org/abs/1304.4635v1)

> When $p=2$, $\lambda\ge 3$. Furthermore, $\lambda=3$ only for polynomials similar to $1+x$. If $p=2$ and $\lambda>3$, then $\lambda\ge 1+\sqrt 5$. Furthermore, $\lambda=1+\sqrt 5$ only if $f(x)$ is similar to $1+x+x^2$.

The source defines the counts in §3.1.

> For a polynomial $f(x)$, prime $p$, and positive integer $\alpha\le p-1$, we define $q_{f(x),p}(k,\alpha)$ to be the number of occurrences of $\alpha$ among the coefficients of $f(x)^k$ reduced modulo $p$. Similarly, we define $q_{f(x),p}(k)$ to be the total number of nonzero coefficients of $f(x)^k$. We then define $r_{f(x),p}(n,\alpha)=\sum_{i=0}^{n-1}q_{f(x),p}(i,\alpha)$ and $r_{f(x),p}(n)=\sum_{i=0}^{n-1}q_{f(x),p}(i)$.

Over $\mathbb F_2$ the counts $q_{f,2}(k,1)$ and $q_{f,2}(k)$ coincide. In Lean the count of a row is the cardinality of its polynomial support.

~~~lean
abbrev P2 := Polynomial (ZMod 2)

def r (f : P2) (N : ℕ) : ℕ := ∑ n ∈ range N, (f ^ n).support.card
~~~

The source gives the matrix convention in §3.3.

> The matrix $B$ has nonnegative entries and is irreducible. Following Willson [6], define $\lambda$ to be the Perron-Frobenius eigenvalue of $B$, i.e., the largest positive eigenvalue of $B$ (it exists by the Perron-Frobenius theorem). We define $\lambda(f)$ to be the value of $\lambda$ for the polynomial $f(x)$. We can approximate the value of $r_{f(x),p}(p^k,\alpha)$ with $\lambda^k$ because the entries of $B^k$ grow as a constant times $\lambda^k$.

The coefficient-count formulation uses the limit of $k$-th roots of $r_{f,2}(2^k)$. The source states this identification itself. Its introduction says that $\lambda$ “characterizes the rate of growth of the total number of nonzero coefficients in $f^i$ for $0\le i<p^n$”, §3.3 approximates $r_{f,p}(p^k)$ by $\lambda^k$, and Example 3.5 makes the same point for $1+x$. Willson’s formula in Garbe’s Theorem 3.1 gives $uB^kv=r_{f,2}(2^k)$. The proof of Theorem 3.9 identifies $\log\lambda$ with the exponential growth exponent of path counts.

The source justifies the identification by the claim that $B$ is irreducible, and that claim is false in general. Garbe’s printed matrix in Example 3.2 is the transpose of Willson’s window matrix $W$. The states of $W$ are the $2^d-1$ nonzero coefficient windows of length $d=\deg f$, and the four maps send a window ending at position $j$ of row $n$ to the windows ending at positions $2j,2j+1$ of rows $2n,2n+1$. Among the $1023$ rules with constant term $1$ and degree at most $10$, $W$ is reducible for $800$, including $1+x+x^2+x^4$ from Table 4. The identification nevertheless holds for every $f$, by the following argument.

A length-$k$ path from a window $s$ corresponds to a row $i<2^k$ and an offset $e<2^k$ at which the window of $G(x^{2^k})f^i$ is nonzero, where $G$ is $s$ placed as a polynomial with at most $d$ terms. Each nonzero coefficient lies in at most $d$ windows, so the row sums of $W^k$ are at most $d\sum_{i<2^k}w(G(x^{2^k})f^i)\le d^2r_f(2^k)$. Conversely, $r_f(2^k)=uW^kv\le d\,\|W^k\|_\infty$. By the spectral-radius formula, $\lim_k r_f(2^k)^{1/k}=\rho(W)=\rho(B)$, with or without irreducibility. The same argument applies to the section realization used below. This step is outside Lean. Lean proves the exact section recurrence, the path-to-weight bounds and the convergence of the root path-count rate to the coefficient-count rate.

The identification has also been checked numerically. Under it, all $30$ values of Table 4 are reproduced to the printed precision. For all $1023$ rules above, $\rho(W)$, the spectral radius of the part of $W$ accessible from $u$, and the spectral radius of the section matrix agree to within $10^{-6}$. For thirteen rules, including reducible ones, monomials and rules with $f(0)=0$, $r_f(2^k)/\rho^k$ stays between fixed positive constants for $k\le400$.

~~~lean
def HasGrowthRate (f : P2) (rate : ℝ) : Prop :=
  Tendsto (fun k : ℕ => (r f (2 ^ k) : ℝ) ^ ((1 : ℝ) / k)) atTop (𝓝 rate)
~~~

Theorem 3.6 gives the transformations.

> We define the polynomials $f(x)$ and $g(x)$ to be similar if we can transform $f(x)$ into $g(x)$ through a combination of the transformations $f(cx)$ and $cf(x)$ with integer $1<c<p$, $x^c f(x)$ with integer $c>0$, $f(x^c)$ with integer $c>1$, $x^{\deg(f)}f(x^{-1})$, and $f(x)^c$ with integer $c>1$. Any two similar polynomials have the same $\lambda$.

The two coefficient-scaling transformations have no instances at $p=2$. We use the equivalence relation generated by the four remaining transformations. Squaring, for example, preserves the rate of $1+x$, and the equivalence relation places $(1+x)^2$ and $1+x$ in the same class. Polynomial reversal is `reflect f.natDegree f`, which reflects exponents about the degree in the source formula. Dilation uses substitution and coincides with `Polynomial.expand` by `Polynomial.expand_eq_comp_X_pow`.

~~~lean
inductive SimStep : P2 → P2 → Prop
  | shift (f) (c : ℕ) (hc : 0 < c) : SimStep f (X ^ c * f)
  | dil (f) (c : ℕ) (hc : 1 < c) : SimStep f (f.comp (X ^ c))
  | rev (f) : SimStep f f.reverse
  | pow (f) (c : ℕ) (hc : 1 < c) : SimStep f (f ^ c)

def Similar (f g : P2) : Prop := Relation.EqvGen SimStep f g
~~~

This relation matches the source’s usage. Its classes that meet degree at most $6$ number exactly $30$, and Garbe’s Table 4, which lists “non-similar polynomials with degree of up to 6”, contains one member of each. Read one way (“$f$ can be transformed into $1+x$”), the relation would make the second sentence of the conjecture false for $(1+x)^2=1+x^2$. The class of $1+x$ is $\{x^m(1+x^s)^c\}$ and the class of $1+x+x^2$ is $\{x^m(1+x^s+x^{2s})^c\}$. These are also exactly the polynomials obtainable from $1+x$, respectively $1+x+x^2$, by forward transformations.

**Theorem.** For each $f\in\mathbb F_2[x]$ with at least two nonzero terms, the coefficient-count growth rate exists and is at least $3$. It equals $3$ precisely when $f\sim 1+x$. If it exceeds $3$, it is at least $1+\sqrt5$, and it equals $1+\sqrt5$ precisely when $f\sim 1+x+x^2$.

For a monomial $x^j$, every row has one nonzero coefficient, so $r_f(2^k)=2^k$. For $f=0$, only the zeroth row contributes, giving $r_f(2^k)=1$. Under the source’s matrix definition the monomial $x$ already contradicts the printed unrestricted bound, since its only state is $1$ with two loops. For degree-zero rules the source’s state set is empty. The source plainly means the nonmonomial range. Its introduction gives the general bounds $p\le\lambda\le p^2$, and the lower bound $p$ is attained by monomials, so the conjectured bound $\lambda\ge3$ refines that bound for non-degenerate rules. Table 4 starts at $1+x$, and the sentence “We see that $\lambda$ is between 3 and 4” is drawn from it. The remark after Theorem 3.9 names $1+x$ as the only polynomial of degree at most one.

## Proof

### The finite transition graph

Write $w(g)$ for the number of nonzero coefficients, and $S_k(g)=\sum_{0\le n<2^k}w(g f^n)$. For any polynomial $g$, define its sections $C_0 g,C_1 g$ by $g=(C_0 g)^2+x(C_1 g)^2$. The four candidate children of $g$ are
$$
 C_0g, C_1g, C_0(gf), C_1(gf).
$$
Discard the zero children and remove the largest monomial factor of each child. Keep repeated children as separate edges. Multiplying $g$ by a monomial only shifts supports and permutes the sections up to monomials. Thus $S_{k+1}(g)$ is the sum of $S_k$ over this child list. This follows from
$$
 C_i(g f^{2n+b})=C_i(g f^b) f^n \qquad(b=0,1).
$$
Normalize $f$ to have constant term $1$. With $d=\deg f$, every state reachable from $1$ has degree less than $d$, since $\deg(gf)\le 2d-1$. Every such state has constant term $1$, and repeated application of $C_0$ to $g$, without multiplication by $f$, reaches $1$. The reachable graph is finite and strongly connected.

Let $P_k(g)$ be the number of length-$k$ paths from $g$, with edge multiplicities. Then $P_k(1)\le S_k(1)\le dP_k(1)$, since $1\le S_0(g)\le d$ at all reachable states. The limit of the $k$-th roots of $P_k(1)$ exists directly. To see this, the maximum of $P_k(g)$ over states is submultiplicative, and a bounded-length route from $1$ to each state, padded by the loop at $1$, compares this maximum with $P_{k+D}(1)$ for fixed $D$. The upper and lower growth limits agree by the submultiplicative-sequence lemma. No spectral theorem is needed for the existence argument. The section matrix is a realization of Willson’s method of the size stated in Theorem 3.1. Its entries count labelled edges, and zero sections are omitted. Starting at $1$ with terminal weight $w(g)$ gives the identity of Theorem 3.1. It is not the matrix printed in Example 3.2 (for $1+x+x^2$ it is $\left(\begin{smallmatrix}2&0&1\\1&1&1\\3&1&0\end{smallmatrix}\right)$ on the states $1,x,1+x$), but it has the same spectral radius by the argument above. Theorems 3.3 and 3.9 describe the transition-graph interpretation. Even if all states of degree less than $d$ are retained, paths starting at any state $g$ have count at most $S_k(g)\le w(g)r_f(2^k)$ by the support-product bound. The maximum row sum of the $k$-th matrix power is at least the root path count and at most $d r_f(2^k)$. The matrix-norm spectral radius formula thus identifies the rate with the Perron eigenvalue, whether one keeps only accessible states or uses the full section matrix. The same argument works with sections before removing monomial factors because the weight of a polynomial is invariant under such a removal.

We also normalize $f$ to be a polynomial with no proper power representation, meaning that the gcd of its positive irreducible multiplicities is $1$. Indeed, remove the greatest common power by Theorem 3.6. For a direct count proof of that invariance, for any $c\ge1$ one has
$$
 \sum_{j<N} w(f^{cj})  \le \sum_{i<cN} w(f^i)
  \le \Big(\sum_{r=0}^{c-1}w(f)^r\Big)\sum_{j<N}w(f^{cj}).
$$
Sandwich the cutoff $c2^k$ between dyadic cutoffs at fixed offsets to compare the exponential rates. Dilation of exponents and reversal preserve weight in each row, as does a monomial factor. So all these normalizations preserve both similarity and the rate.

### Valuations modulo the direction of $f$

Use $V=\bigoplus_{P\ne x}\mathbb Z$, indexed by the monic irreducibles in $\mathbb F_2[x]$ other than $x$. For a nonzero rational function $h$, write $v(h)$ for its signed multiplicities in $V$, and put $e=v(f)$. The multiplicities of $f$ have gcd $1$, so choose an integer linear functional $\ell$ with $\ell(e)=1$ by Bézout. Set $L=\ker\ell$, $\pi(v)=v-\ell(v)e$, and $u(h)=\pi(v(h))$. The group $L$ is torsion free, and $2^jL=L\cap 2^jV$, since $\ell(2^j v)=0$ implies $\ell(v)=0$.

A nonzero binary polynomial has a single nonzero section exactly when it is $x^s$ times a square for some $s\ge 0$. This is equivalent to the evenness of every coordinate of $v$. Because $e$ has an odd coordinate, this property cannot hold for both $g$ and $gf$. Thus there are three children if $u(g)\in 2L$, and four otherwise. Call these states three-child and four-child states respectively. Indeed, $u(g)\in 2L$ is equivalent to $v(g)$ being congruent to $0$ or $e$ modulo $2V$.

More generally, if $u(g')-u(g)=2h$ for $h\in L$, then the child lists of $g,g'$ can be matched so that corresponding child vectors differ by $h$, with multiplicities preserved. To prove this, the definition of $\pi$ and unique factorization give
$$
  g'=x^s f^r H^2 g,\qquad u(H)=h
$$
for integers $s,r$ and a rational function $H$. Sections extend to rational functions using the basis $1,x$ of $\mathbb F_2(x)$ over its square subfield. Existence follows by clearing denominators with a square and splitting the resulting polynomial by parity. The decomposition is unique because $x$ is not a square in the rational function field, as seen from its odd multiplicity at $x$. For time choice $b\in\{0,1\}$ on the $g'$ side, write $r+b=2j+b'$ with $b'\in\{0,1\}$. The map $b\mapsto b'$ permutes the two time choices. The factor $x^s$ permutes the two sections up to monomial factors, and the square factor becomes $f^j H$ on the sections. The child vector therefore changes by $h$ because powers of $f$ and $x$ have zero projection.

Consequently the finite graph can be projected to its reachable vectors $u$ as a directed multigraph. For each realized residue class $\sigma\in L/2L$, fix a representative vector $u_\sigma$ attained by a state, and let $c_{\sigma,i}$ list the child vectors of that representative, with multiplicities. The ordered list at $u\equiv u_\sigma\bmod 2L$ is
$$
   \frac{u-u_\sigma}{2}+c_{\sigma,i}.
   \tag{1}
$$
Any projected path with edge indices can be lifted to an original path, since the projected child list depends only on $u$. In particular the projected graph is strongly connected and has the same path counts. For the even class choose $u_0=0$ from the state $g=1$. Its three offsets are $0,a,b$, where $a=u(C_0 f)$ and $b=u(C_1 f)$. Call the first of these three edge indices the zero choice, also when offsets coincide.

A reachable state with vector $0$ must be $1$. In fact its multiplicities are $r e$ for an integer $r$, so as a normalized polynomial it is $f^r$ with $r\ge0$. Its degree is less than $d$.

If $a=b=0$, every projected path stays at $0$ and has three choices per step. Hence $\lambda=3$. Also both $C_0f$ and $C_1f$ are monomials, since their normalizations have vector $0$. Thus $f$ is a binomial and is similar to $1+x$.

### Deferring the three choices

Assume at least one of $a,b$ is nonzero. Let $t\ge0$ be the largest integer with $a,b\in 2^t L$, and put $T=t+1$. In (1), defer the three-way choice made at time $j$ at a three-child state until time $j+T$. Four-way choices are made immediately. At times $0,\ldots,T-1$ there are no earlier choices due.

Here are the exact state and update for the deferred process. Before time $n$, a state consists of a default vector $u$ and a length-$T$ queue recording which of the preceding $T$ times were three-child times and have pending choices. Pad times before $0$ with empty entries. The vector $u$ is obtained using offset zero for each pending choice. A pending offset $c\in\{0,a,b\}$ from time $j$ changes the current vector by $c/2^{n-1-j}$. For the oldest entry this is $c/2^t$, whereas all younger entries have even effects. If the oldest entry is occupied, branch over its three offsets $c$ and first add $c/2^t$ to $u$. If it is empty, make no change. Then the parity of the current vector is known. If even, apply (1) with its zero choice and append an occupied entry. If odd, choose one of the four edges of (1) and append an empty entry. In both cases remove the oldest entry.

To verify this description inductively, the actual quotient vector for any completion of the pending choices is the default vector plus the sum of the stated effects. After the oldest entry is resolved, all remaining effects are even. Hence the representative parity class in (1) is independent of the younger choices, and (1) halves their effects while adding the same chosen offset. The new pending choice at an even state contributes its full offset at the next stage. This proves the update and shows that all completions follow valid original paths. Conversely an original prefix specifies a unique deferred prefix together with the choices still pending at its end, by revealing each index at its scheduled time. In particular, denoting the number of deferred prefixes of length $k$ by $D_k$, each deferred prefix with $m$ occupied entries has exactly $3^m$ original prefixes above it, and we have
$$
  D_k\le P_k(1)\le 3^T D_k.
  \tag{2}
$$
The deferred graph is finite because its default vector is always realized by some original path and the queue has fixed finite length.

Put $\alpha=1+\sqrt 5$, so $\alpha=2+4/\alpha<4$. Give a deferred state with $m$ occupied entries weight $\alpha^m$. If its oldest entry is empty, the child-to-parent weight sum is $\alpha$ for an even current vector and $4$ for an odd one. If the oldest entry is occupied, one of the three possible vectors must be odd. Their residues are obtained by adding $0,a/2^t,b/2^t$, which do not all coincide modulo $2L$. An even outcome contributes ratio $1$, whereas an odd outcome contributes $4/\alpha>1$. Thus the total ratio is at least $2+4/\alpha=\alpha$. Iterating the weight inequality and using bounded weights and (2) gives $\lambda\ge\alpha$.

### When the weight bound is sharp

If the inequality is strict at a reachable deferred state, then $\lambda>\alpha$. To see this, there can be no strict state before time $T$ from the root, because the default vector remains $0$ with no choices due. At any time $n\ge T$ a strict state can be described by the last $T$ original edges of the default completion of its history. Every three-way choice in that segment uses its zero label. None of those choices has yet been revealed. From any other deferred state, complete its pending choices with the zero labels, then use strong connectivity of the original projected graph to reach the beginning of that segment. Follow the segment with the same labels. A complete original prefix can be followed in the deferred process by revealing its labels when due, as verified above. At the end of the segment the queue and default vector agree with the original strict state. Thus all reachable deferred states can reach a strict state.

For the deferred transition operator $M$, let $W$ be the positive queue weight. We have $MW\ge\alpha W$. If strict vertices can be reached from every vertex, finiteness gives an integer $K$ for which $M^K W>\alpha^K W$ pointwise: a positive difference at the end of a path propagates backwards under the appropriate power of $M$, and $\alpha^{-k}M^k W$ is pointwise nondecreasing. Take the minimum of the finitely many strict ratios and iterate the resulting improved bound in blocks of length $K$. By (2) the exponential rate is strictly above $\alpha$.

Assume now that $\lambda=\alpha$. Thus no reachable deferred state is strict. At time $T$ starting from $0$, consider the default path using only zero choices. Its due step has candidate residues $0,a/2^t,b/2^t$, and exactly one must be nonzero. Call the corresponding one of the two section labels the special choice, and call both other positions ordinary. For any occupied oldest entry, the three candidate residues at disclosure are $s,s,s+c$ where $c\ne0$ in $L/2L$. Exactly one must be nonzero, which forces $s=0$. With an empty oldest entry the current vector must be even. We conclude that, along every original path at times $n\ge T$,
$$
  \text{the state at time }n\text{ has four children}
  \quad\Longleftrightarrow\quad
  \text{the edge at time }n-T\text{ used the special choice}.
  \tag{3}
$$
Here four-way edges are never called special. Before time $T$ all original states along all paths from the root have three children, by the update rule with no choice yet due.

If a prefix has no special choice in its last $T$ steps, its current vector is zero. For prefixes of length less than $T$, use the preceding paragraph for the initial three-child property and pad the past with no specials. In all cases, continue with zero choices. By (3), every subsequent state has three children, and these zero choices repeatedly halve the current vector. A finitely supported integer vector divisible by every power of $2$ is zero.

Choose the special edge at time $0$, then zero choices at times $1,\ldots,T-1$. The state $g$ at time $T$ has four children by (3). Each child is preceded by a segment of $T$ steps with no special choice, namely times $1,\ldots,T$. Its vector is therefore zero, so the corresponding normalized polynomial is $1$. It follows that $g$ and $gf$ each have exactly one even and one odd monomial. Both have constant term $1$, so write
$$
g=1+x^{2s+1},\qquad gf=1+x^{2t+1}.
$$
Write $A=C_0 f$ and $B=C_1 f$. Multiplication and the parity section identities give
$$
 A+x^{s+1}B=1,\qquad B+x^s A=x^t.
$$
The ordinary root edge belonging to a section of $f$ has vector zero, since its one-edge history has no special choice. Thus that section is a monomial. If the ordinary section is $A$, then $A=1$ by the constant term. The first equation would force $B=0$, contrary to the fact that $f$ has both sections nonzero. Therefore $B=x^m$ for some $m\ge0$. The equations give $A=1+x^{s+1+m}$ and
$$
 x^m+x^s+x^{2s+1+m}=x^t.
$$
The last exponent on the left is strictly greater than both $m$ and $s$. The left side is a monomial only when $m=s$. Substituting in $f=A^2+xB^2$ yields $f=1+x^{2s+1}+x^{2(2s+1)}$, which is similar to $1+x+x^2$.

For $1+x$ the graph is one vertex with three loops. For $1+x+x^2$ its normalized vertices are $1$ and $1+x$. The first has two edges to itself and one to $1+x$, while the second has four edges to $1$. The positive vector $(1,4/\alpha)$ is an eigenvector of the row-acting operator with eigenvalue $\alpha$. The terminal-weight vector $(1,2)$ is bounded above and below by positive multiples of this eigenvector. Applying the nonnegative matrix $k$ times bounds the coefficient sum between the corresponding multiples of $\alpha^k$. Taking roots gives the rate. Invariance under similarity gives both converses.

## Significance and prior work

The finite section construction and the individual values $3$ and $1+\sqrt5$ were available in Garbe’s Theorems 3.1 and 3.3 and Examples 3.2 and 3.5. The gap requires uniform control even when all paths from the initial state branch three ways for arbitrarily many levels, as for the first $m$ levels of $1+x+x^{2^m}$. The valuation quotient and deferred choices yield a lower bound independent of that delay. Equality in the weight calculation recovers the rule up to similarity.

The result is modest. The bound $\lambda\ge3$ takes a few lines, because every state has at least three nonzero children once common powers are removed. The case $\lambda=3$ is also short. The content is the gap above $3$ and the classification at $1+\sqrt5$. The source is a high-school research paper (MIT RSI 2012) whose conjectures come from computations up to degree $9$. Its three citing works concern line complexity, so the problem has had little exposure. The argument is elementary and uses no published theorem beyond Fekete’s lemma.

The adversarial prior-art review checked Garbe’s arXiv and MIT RSI versions, Ellison’s 2011 PRIMES paper on nonzero coefficients, Wolfram’s note on the fractal dimensions of additive cellular automata, and the Principia, mio-math, Omega and mxym/math registries. The final check repeated the registry and GitHub searches on 2026-11-23 with no relevant hit. It also read Gütschow, Nesme and Werner, *The fractal structure of cellular automata on Abelian groups* (arXiv:1011.0313), and Allouche, von Haeseler, Peitgen and Skordev, *Linear cellular automata, finite automata and Pascal’s triangle* (1996). Both compute dimensions of individual rules and state no minimum or gap. Ellison and Wolfram give individual rule values. Willson’s 1987 paper supplies the counting method, and Garbe’s Theorem 3.9 supplies an upper bound. The citing work *Line complexity asymptotics of polynomial cellular automata* concerns a different statistic. The review found no proof of the minimum, gap or rigidity statements. The reviewer did not read the full texts of Willson’s earlier papers or the von Haeseler–Peitgen–Skordev papers. [Willson 1987](https://doi.org/10.1016/0167-2789(87)90074-1) · [Wolfram’s note](https://www.wolframscience.com/nks/notes-6-6--fractal-dimensions-of-additive-cellular-automata/) · [Line complexity](https://arxiv.org/abs/1604.02753)

## Formalization and provenance

The Lean existence proof uses submultiplicativity directly for the coefficient sums. Write exponents in blocks as $j2^b+i$ and use $f^{j2^b}=(f^j)(x^{2^b})$ in characteristic two. Weight is unchanged by expansion and submultiplicative under products, so $r_f(2^{a+b})\le r_f(2^a)r_f(2^b)$. Apply Fekete’s lemma to the logarithms of these positive counts and exponentiate. Lean checks invariance under all four generators, including the two cutoff comparisons for powers.

Lean proves the lower bound by repeatedly removing homogeneous-parity square factors until both sections of the rule are nonzero. For the rate-$3$ rigidity proof, a uniform block estimate excludes four-child vertices at that rate. The formal proof then uses the square side of each three-child transition. Any reachable $g$ can be lifted through $k$ such transitions to $q^{2^k}=gf^s$ for some $s\ge0$. Comparing degrees and multiplicities shows that $2^k$ divides $(\deg f)v_P(g)-(\deg g)v_P(f)$ for every irreducible $P$ and every $k$. The difference is zero. Taking the gcd over $P$ and using primitivity gives $\deg f\mid\deg g$, so $g=1$. Both sections of $f$ are consequently monomials.

The formal proof of the sharp gap clears signed powers into polynomial identities for the child-list translation. The affine list is ordered by the offsets of a fixed representative per residue, and Lean compares the child lists by permutation. The finite sums in `pendingSum_step` preserve indexed multiplicities through a deferred transition. For equality, `replay_step` follows a tagged original edge with a full queue and `lift_step` lifts a deferred edge for any filling of the later queue. The length-$T$ replay then takes every reachable state to the same strict state in uniformly many steps if one exists. The exact local weight identity yields the special label, and the polynomial section equations above finish the classification. The three endpoints are printed in `GarbeConjecture.lean`.

GPT-6.2 Sol lanes produced the proof, the Lean formalization and this paper. Claude Opus 5.5 lanes performed the adversarial review of the written proof before Lean and the final check of the definitions, the paper and the prior art. All of these are AI systems, and no human has checked the result. The identification of Garbe’s Perron eigenvalue with the coefficient-count growth rate is proved in the text and not in Lean.
