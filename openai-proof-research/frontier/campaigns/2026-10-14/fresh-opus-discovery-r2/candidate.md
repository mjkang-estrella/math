# r2 / family 113 — supporting barrier record (full target unresolved)

**Title.** A structural barrier to improving the perfect-matching entropy coefficient by
higher-degree forcing gadgets.

**Family:** 113 (perfect-matching counting and entropy). **Status: full-target-unresolved
SUPPORTING BARRIER RECORD — not a frontier candidate, not an acceptance, and not a nominee
for the substantial count.** The headline coefficient $c^\*$ is left **open**; this record
only documents a rigorous obstruction to the natural lower-bound (cut-forcing) method, plus
bounded computation. It is archived for provenance so the dead-end and its (finite) evidence
are on record, not as a claimed advance on $c^\*$.

**Scope caveats (read first).** (a) The one external theorem relied on — Hetyei's edge bound
— is a **cited general-theorem dependency, not reproved here**; my $n=2,3$ enumerations are
finite consistency diagnostics only and do not establish the general statement. (b) No
numeric or sampled **absence** of gadgets is claimed to prove **general** gadget
nonexistence; the computations are exhaustive only at order $5$ and are sampling-based
evidence at orders $7,9,11$.

---

## 1. The open finite estimate

For a finite simple graph $G$ with perfect-matching polytope $P(G)$ and a point
$x\in P(G)$, write
$$F(x)=\sum_{e}-x_e\log x_e,\qquad B(x)=\sum_{e}-(1-x_e)\log(1-x_e),$$
and let $H(x)$ be the entropy of the maximum-entropy perfect-matching law with marginals
$x$. The source (*Entropy and Face Dimension of the Perfect-Matching Polytope*) proves, for
$|V(G)|=2m$,
$$F(x)-\Big(2-\tfrac2m\Big)\,B(x)\;\le\;H(x)\;\le\;F(x),$$
and the Klee / triangle-expansion family $G_m$ ($2m$ vertices, $3m$ edges, $3$-regular) forces
the lower-bound constant
$$c^\*\;\ge\;\frac{\ln 3}{2\ln(3/2)}\;=\;1.3548\ldots$$
The source **explicitly does not establish optimality of the coefficient two**, leaving
$$c^\*\;=\;\sup_{G,\,x\in P(G)}\frac{F(x)-H(x)}{B(x)}\;\in\;\big[\,1.3548\ldots,\;2\,\big]$$
as a flagged open finite estimate. (Bipartite graphs have coefficient exactly $1$
— Schrijver / Gurvits–Bethe; the gap to $2$ is driven by odd cuts.) Both ingredients of the
source's upper-bound argument (the trace obstruction $s-d\ge(c+1)m$ and the geometric
codimension bound $s-d\le 3m-2$) are individually sharp, so the upper bound is not improvable
by rearranging the existing proof.

## 2. The forcing method and why higher degree is the only lever

The Klee lower bound is a **cut-forcing** construction. Its local atom is a *forcing gadget*:
an odd graph $T$ with $k$ distinguished ports, embedded so that every perfect matching crosses
the gadget boundary exactly once and, conditioned on the crossing edge, the internal matching
is forced. For the assembled graph to be $k$-regular with uniform marginals $x_e=1/k$, the
gadget must be degree-compatible.

**Definition ($k$-forcing gadget).** A finite simple graph $T$ with a distinguished
$k$-subset $P\subseteq V(T)$ (ports) such that
(i) $\deg_T(p)=k-1$ for every $p\in P$;
(ii) $\deg_T(v)=k$ for every $v\notin P$;
(iii) for every $p\in P$, $T-p$ has a **unique** perfect matching.

For $k=3$ the triangle $T=K_3$ with $P=V(T)$ is a $3$-forcing gadget with $0$ non-ports
(each $T-p$ is a single edge); this is exactly the Klee atom.

**Heuristic gain (conditional).** A $k$-regular family assembled from $k$-forcing gadgets,
at the uniform point $x_e=1/k$, has $F=|E|\tfrac{\ln k}{k}$,
$B=|E|\tfrac{k-1}{k}\ln\tfrac{k}{k-1}$, and (because forcing makes the max-entropy law
sublinear, $H=o(|E|)$) deficit $F-H=(1-o(1))F$, giving
$$\frac{F-H}{B}\;\longrightarrow\;\frac{\ln k}{(k-1)\ln\frac{k}{k-1}}\;=\;R(k).$$
$R(k)$ is strictly increasing with
$$R(3)=1.3548\ (\text{Klee}),\quad R(4)=1.6063,\quad R(5)=1.8031,\quad R(6)=1.9655,\quad R(7)=2.1039>2 .$$
So higher-degree forcing gadgets are the *only* way the method could approach $2$ — and
degree $\ge7$ is impossible outright, since $R(k)>2$ would contradict the source's proven
bound $c^\*\le 2$. The method is therefore confined to $k\le 6$, where $R(k)\le R(6)<2$.
*(The value $R(k)$ for $k\ge4$ is the natural extrapolation of the $k=3$ case, conditional on
the existence and forcing behavior of a degree-$k$ gadget; it is a target for the method, not
a proved ratio.)*

## 3. Main theorem — the forcing-gadget size condition

**Theorem.** If a $k$-forcing gadget has $s$ non-port vertices, then
$$(s-1)^2\ \ge\ (k-2)^2 .$$
Hence for $k\ge4$ one must have $s\ge k-1$ (so $|V(T)|\ge 2k-1$). The case $k=3$ is the
boundary: the condition reads $1\le(s-1)^2$, i.e. $s=0$ or $s\ge2$, and the Klee triangle
realizes $s=0$. In particular **the Klee triangle is the unique zero-non-port forcing gadget
degree**, and every higher-degree forcing gadget requires a growing number $\ge k-1$ of
non-port vertices.

**Proof.** Let $T$ be a $k$-forcing gadget with $s$ non-ports, so $|V(T)|=k+s$. Since $T-p$
has a perfect matching, $k+s-1$ is even. Summing degrees,
$$|E(T)|=\frac{k(k-1)+sk}{2}.$$
Fix a port $p$ (degree $k-1$). Then $T-p$ has a *unique* perfect matching on $2j$ vertices,
$j=\tfrac{k+s-1}{2}$, and
$$|E(T-p)|=\frac{k(k-1)+sk}{2}-(k-1).$$
By **Hetyei's theorem** (a graph on $2j$ vertices with a unique perfect matching has at most
$j^2$ edges),
$$\frac{k(k-1)+sk}{2}-(k-1)\ \le\ \Big(\frac{k+s-1}{2}\Big)^2 .$$
Multiplying by $4$ and expanding $(k+s-1)^2=k^2+s^2+1+2ks-2k-2s$:
$$2k(k-1)+2sk-4(k-1)\ \le\ (k+s-1)^2
\ \Longleftrightarrow\ k^2-4k+3\ \le\ s^2-2s
\ \Longleftrightarrow\ (k-2)^2\ \le\ (s-1)^2 .$$
For $k\ge4$ and $s\ge0$ this forces $s\ge k-1$; the degree sum and $j$ are integers
throughout because $k+s$ is odd. $\square$

**External theorem dependency (finite diagnostics only).** The proof rests on **Hetyei's
theorem**: a graph on $2n$ vertices with a unique perfect matching has at most $n^2$ edges
(Hetyei 1964; see also Kotzig's work on unique perfect matchings and Lovász,
*Combinatorial Problems and Exercises*). I do **not** reprove this general theorem; it is a
cited external dependency whose general validity I assume. As **finite consistency
diagnostics only** — *not* a verification of the general theorem — I enumerated the
unique-PM graphs at $n=2$ and $n=3$ and confirmed $\max|E|=4$ and $9=n^2$ respectively, with
the expected extremal fan graphs. The algebraic simplification was checked symbolically and
numerically ($k=4\Rightarrow s\ge3$, $k=5\Rightarrow s\ge4$). These small checks guard against
a misstatement of the *bound's value* at tiny $n$; they say nothing about the general $n$
case, which is taken on Hetyei's authority.

## 4. Computational obstruction at small orders

I searched for degree-$4$ forcing gadgets ($k=4$: four ports of degree $3$, non-ports of
degree $4$, every port-deletion a unique-perfect-matching graph):

| order | non-ports $s$ | Hetyei status | search | gadgets found |
|-------|---------------|---------------|--------|---------------|
| 5 | $1$ | excluded (Thm: $1<3$) | **exhaustive** | $0$ |
| 7 | $3$ | tight ($|E(T-p)|=9=3^2$) | sampled $>10^4$ | $0$ |
| 9 | $5$ | slack | deg.-preserving Markov chain | $0$ (best UMG-port count $=0$) |
| 11 | $7$ | slack | deg.-preserving Markov chain | $0$ (best UMG-port count $=0$) |

The 5-vertex case is excluded analytically by the Theorem ($s=1<3$) and confirmed
exhaustively. The 7-vertex case is Hetyei-*tight* — every $T-p$ would have to be an
*extremal* ($3^2$-edge) unique-PM graph — and no sampled example realizes all four ports.
At 9 and 11 vertices not even a *single* port had a unique-PM deletion in any sampled graph
(best count $0$), reflecting the structural tension: degree-$4$ regularity forces density,
whereas a unique-perfect-matching graph is sparse (Hetyei) and bridge-structured (Kotzig).

*These computations are exhaustive only at order $5$ (where the Theorem already excludes a
gadget analytically). At orders $7,9,11$ they are sampling-based diagnostics over a
degree-preserving Markov chain, and their finding "no gadget observed" is **absence of
evidence, not evidence of absence**: it does **not** prove that no degree-$4$ forcing gadget
exists at those or larger orders. A rigorous general nonexistence statement is left open.*

## 5. Conclusion

The cut-forcing method behind the source's lower bound $\tfrac{\ln3}{2\ln(3/2)}$ cannot be
pushed to higher degree in any obvious way: the only potential gains come from degree-$k$
forcing gadgets, which (a) are structurally forced to have $\ge k-1$ non-ports (Theorem),
(b) cannot exist for $k\ge7$ (they would exceed the source's own upper bound $c^\*\le2$),
and (c) were not found at small orders for $k=4$ (Section 4: exhaustive at order $5$,
sampling diagnostics — *absence of evidence only* — at orders $7,9,11$). Any forcing-based
gain is therefore capped strictly below $2$ (since the feasible degrees satisfy $k\le6$ and
$R(6)<2$). Separately, a numerical grid search over the Klee $3$-simplex found the uniform
point to maximize the deficit ratio — *numerical evidence only, not a proved optimality
statement* — suggesting (not proving) that re-weighting the Klee marginals does not help
either. Determining whether $c^\*<2$ or $c^\*=2$ requires a fundamentally new lower-bound
construction or an upper-bound argument beyond the source's two individually-sharp
ingredients.

## 6. Honest limits

- The open coefficient $c^\*\in[1.3548,2]$ is **not** resolved; no bound is improved.
- Theorem (Section 3) is rigorous **conditional on two cited inputs**: the source's upper
  bound $c^\*\le 2-2/m$, and Hetyei's classical $n^2$ edge bound, which is **assumed as a
  general external theorem (not reproved)**; only finite diagnostics at $n=2,3$ were run, and
  they do not establish the general case.
- $R(k)$ for $k\ge4$ is a conditional extrapolation (no degree-$\ge4$ forcing family is known).
- Gadget nonexistence is exhaustive at order $5$ (and analytically forced there) and
  sampling-based at orders $7,9,11$ — evidence, not proof, at the larger orders.
- Freshness is bounded-evidence only (tasks.json registry + semantic grep + accepted audit);
  no worldwide/new-to-literature novelty is claimed beyond these bounded reads.
