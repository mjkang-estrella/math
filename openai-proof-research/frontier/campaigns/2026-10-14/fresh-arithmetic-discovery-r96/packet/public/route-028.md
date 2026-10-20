# Main direction: source028 Gaussian moat, other lattices of prime elements

Status: screened, never frozen, no nominee. Nothing below is offered as a proved new result. The calculations are prefreeze feasibility checks by the author of this packet; they are not independent mathematical gates.

## Why this family

The family-history table (`private/history/r95-family-history-counts.txt`) gives 028 three authored units. The only developed study is I204 (copied as `private/history/i204-arithmetic-structures-discovery.md`, section "028: no new effective mechanism"). I204 asked for an *effective* component bound and stopped because that is constant extraction. r72 rejected 028 at catalogue level because of I204. No authored study of other rings, other quadratic forms or higher rank was found (targeted `rg` over `frontier/`, `proposals/`, `notes/`, `experiments/` for moat/Eisenstein/number-field/quaternion strings; hits are navigation, not absence certificates).

## Source contract (read in the pinned bodies)

`main.tex`, `thm:main`: for every finite $D$ there is $B_D$ such that every component of the graph $G_D$ on Gaussian primes (edges at Euclidean distance at most $D$) has at most $B_D$ vertices. It follows from two statements.

- `thm:sieve` (main.tex): for every $D\ge1$ there is a finite set $\mathcal P_D$ of rational primes $p\equiv1\pmod 4$ such that $\mathcal A(\mathcal P_D)=\{z\in\mathbb Z[i]: \pi_p\nmid z,\ \bar\pi_p\nmid z\ (p\in\mathcal P_D)\}$ contains no infinite self-avoiding walk with steps at most $D$.
- `prop:periodic` (periodicity.tex): a translation-invariant locally finite graph with no infinite simple path has components injecting into $(\mathbb Z/Q)^2$; deleting the finitely many associates of selected factors costs a factor $K_D|E|$.

The proof of `thm:sieve` fixes an arbitrary deterministic walk and samples times. Its sections are:

| Section | Operation | Dimension-specific? |
|---|---|---|
| preliminaries.tex | split primes in $[T,2T]$ by PNT in progressions mod 4; `lem:displacement` (entropy of a displacement over $n$ steps $\le 2\log(n+1)+O_D(1)$); continuity; `lem:list` | Only the harmless constant 2 in `lem:displacement` |
| geometry.tex | `lem:differences` (planar torus-degree: $\lvert E-E\rvert\ge c_D RW$); `lem:rectangle` (2×2 determinant divisibility, a unique witness line, Hoeffding over signs, cube isoperimetry); `lem:enrichment` | **Yes: both input lemmas are planar** |
| coverage-transfer.tex | shared continuation data, coverage | No; its first paragraph says it uses only finite abelian residue groups (lines 1–5) |
| schedule.tex | scales, checkpoints, displacement sets $\mathcal D_i$ | Only lattice-point counts such as `eq:native-data` (lines 240–262), which become $d$-dimensional counts with the same logarithmic form |
| information.tex | increment words, information budget | Uses residue addition given the full lattice displacement (lines 250–275); no planar geometry was found by `rg` |

The reading extents are in `reading-limits.md`. The later sections were checked by targeted `rg` for planar inputs and by reading the displayed passages, not line by line.

## Candidate A (rank two): every positive definite binary form, every imaginary quadratic order, real quadratic fields

Considered statement (never frozen): for every positive definite primitive integral binary quadratic form $f$ and every $D$, the $D$-graph on $\{v\in\mathbb Z^2: f(v)\text{ prime}\}$ has uniformly bounded components. A companion version covers prime elements of any order in an imaginary quadratic field, and of $\mathcal O_K$ for a real quadratic $K$ under the Minkowski embedding.

Transfer check. Write $f$ as the norm form of a lattice ideal $\mathfrak a$ in an order $\mathcal O$, so that $f(v)=N(\alpha)/N(\mathfrak a)$ for $\alpha\in\mathfrak a$. Sieve by $\mathfrak a\mathfrak p$ for split primes $\mathfrak p$ of degree one. Each source step has a direct substitute:

- Batch counts: Chebotarev (or PNT in progressions for the splitting condition) replaces the mod-4 count, with $k_T\asymp T/\log T$.
- "Sign": choose $\mathfrak p$ or $\bar{\mathfrak p}$ over each split $p$.
- `lem:rectangle`, determinant step: if $w,w'\in\mathfrak c$ for a lattice $\mathfrak c$ of index $N$ in $\mathbb Z^2$, then $\det(w,w')\in N\mathbb Z$. This holds for every index-$N$ sublattice and needs no Gaussian arithmetic.
- `lem:rectangle`, fixed-line step: a primitive $v$ lies in at most one of $\mathfrak p,\bar{\mathfrak p}$, because $\mathfrak p\cap\bar{\mathfrak p}=p\mathcal O$. The product of eligible norms is at most $|N(v)|\le C\lvert v\rvert^2$.
- "Nonzero multiples of $\pi$ have length at least $\sqrt p$": replaced by $\lvert v\rvert^2\ge c_f\,p$ for positive definite norm forms.
- `lem:differences` is planar and unchanged.
- `prop:periodic`: the exceptional points $\alpha\in\mathfrak a\mathfrak p$ with $(\alpha)\mathfrak a^{-1}$ prime satisfy $(\alpha)=\mathfrak a\mathfrak p$. In the definite case there are finitely many units, so this set is finite, as in the source.

Real quadratic case. The unit group is infinite, so the exceptional set $E=\{\pi\varepsilon^j\}$ is infinite and `prop:periodic` needs one more step. Let $\sigma_1,\sigma_2$ be the real embeddings. For two exceptional points $x=\pi\varepsilon^j$ and $y=\pi'\varepsilon^{j'}$ with $x\ne y$ and $\lvert\sigma_1 x\rvert$ large, $\sigma_1x-\sigma_1y=\sigma_1(\varepsilon^{j})\bigl(\sigma_1\pi-\sigma_1(\pi'\varepsilon^{j'-j})\bigr)$. The second factor is bounded below by $\min_m\lvert\sigma_1\pi-\sigma_1(\pi'\varepsilon^m)\rvert>0$: this minimum exists because the terms tend to $\lvert\sigma_1\pi\rvert>0$ or to infinity, and no term vanishes since $\sigma_1$ is injective. So far exceptional points are pairwise separated by more than any fixed multiple of the bounded diameter $DQ^2$ of avoiding-graph components, and the source's degree count applies to each far exceptional point separately. (The same argument with $\sigma_2$ handles the other asymptote.)

Stop reason: this is the source mechanism with lattice and arithmetic parameters substituted, plus one elementary separation step. By the brief's calibration (parameter variants and black-box transfers of a source mechanism are TECHNICAL) it was not frozen. No proof was written. The check above is a feasibility sketch only.

## Candidate B (rank at least three): degree-$d$ number fields, quaternary norm forms

Considered question (never frozen): for a number field $K$ of degree $d\ge3$ (or a positive definite integral form in $d\ge3$ variables), are the components of the $D$-graph on prime elements (respectively prime values) uniformly bounded? `prop:periodic` transfers verbatim with $(\mathbb Z/Q)^d$ (in the totally complex case, or with the unit-orbit step above in general). So the question reduces to a rank-$d$ `thm:sieve` for sublattices $\Lambda_{\mathfrak p}=\ker(a_{\mathfrak p}\cdot x \bmod p)$ of index $p$, where $a_{\mathfrak p}$ is the reduction functional of a degree-one prime.

The rest of the source machinery (coverage transfer, schedule, information budget) is dimension-free up to constants. The two planar inputs of `lem:enrichment` do not transfer. Exact failure points:

1. **Determinant step.** For $d=3$, if $w,w'\in\Lambda_{\mathfrak p}$ are independent mod $p$, then $w\times w'\equiv\lambda a_{\mathfrak p}\pmod p$ with $\lambda$ not necessarily $0$: both vectors lie in the plane $a_{\mathfrak p}^\perp$ over $\mathbb F_p$, so their cross product is in $(a_{\mathfrak p}^\perp)^\perp=\mathbb F_p a_{\mathfrak p}$. Small witnesses for nearby sign vectors therefore need not be collinear. The unique-witness-line partition, which drives the cube-isoperimetry count, disappears. A replacement must control witnesses on sublattices of every intermediate rank.
2. **Many differences.** The planar bound $\lvert E-E\rvert\ge c_D\cdot(\text{area of the diameter rectangle})$ has no rank-3 analogue with volume. Take the lattice path $E=S_1\cup S_2\cup S_3$ with $S_1=\{(a,0,0)\}$, $S_2=\{(m,b,0)\}$, $S_3=\{(m,m,c)\}$, $0\le a,b,c\le m$ ($3m$ unit steps, self-avoiding). Then $E-E=\bigcup_{i,j}(S_i-S_j)$ has at most $6(m+1)^2+3(2m+1)=O(m^2)$ points. But $(E-E)-(E-E)=E+E-E-E$ is three-dimensional. It contains every lattice point of the cube $[-m,m]^3$ except those in the two open octants with sign patterns $(-,+,-)$ and $(+,-,+)$, so it has $(2m+1)^3-2m^3$ points. Indeed:
   - $S_1+S_3-S_2-S_1=\{(a-a',\,m-b,\,c)\}$ covers $x\in[-m,m]$, $y\in[0,m]$, $z\in[0,m]$;
   - $S_2+S_3-S_3-S_1=\{(m-a,\,b,\,c-c')\}$ covers $x\in[0,m]$, $y\in[0,m]$, $z\in[-m,m]$;
   - the negatives of these two sets cover the remaining sign patterns except the two named octants.

   A finite enumeration at $m=6$ confirms that exactly the $2m^3=432$ points of those two open octants are missing (see `reading-limits.md`). The source excludes every nonzero sublattice point from a region containing the differences of differences. It does this through a volume condition ($R_1W_1\le P^{1-d}$ in `lem:rectangle`) together with the line argument. Any exclusion of this kind over a region with about $6m^3$ lattice points needs $\log P\gtrsim3\log m$. The entropy gained is only $\log\lvert E-E\rvert\le2\log m+O(1)$. The literal transfer therefore runs at rate about $2/3$, and the enrichment recursion would stabilize below full entropy. This does not say that every index-$P$ sublattice with $P\ll m^3$ collides on $E-E$. A skewed sublattice whose short vectors all lie in the two missing octants can be injective there. Such sublattices are what a sign or Hoeffding argument would have to rule out.
3. **Near-injectivity instead of injectivity.** The natural replacement counts collisions: $\mathbb E_J\sum_{0\ne u\in\Lambda_J}r_{E-E}(u)$, where $r$ counts representations as a difference of two elements of $E-E$. This needs $\Pr_J(u\in\Lambda_J)\le P^{-1+o(1)}$ for every fixed nonzero $u$ in range. The crude bound is $\binom{\omega}{r}/\binom{k}{r}\le(\omega/k)^r$, with $\omega\le d\log(Cn)/\log T$ batch prime divisors. That is $P^{-1+\theta}$ with $\theta\approx\log\log n/\log T$. In the schedule's middle band (`schedule.tex` lines 240–250, scales $U$ up to about $T^{1/4}$), $\theta$ stays near $1/4$. A $d$-dimensional analogue of the fixed-line Hoeffding step must therefore handle skewed sublattices of every rank before collision counting closes. No such lemma was built. In the three-segment example, $E-E$ is a union of six planar squares and three segments. A translate of such a square by a vector not parallel to its plane meets each other square in $O(m)$ points. So for sublattices whose nonzero points in the cube avoid those plane directions, collisions are few. That is a property of the example, not a lemma.

Stop reason: candidate B needs a new $d$-dimensional geometric enrichment (a replacement for `lem:differences` plus `lem:rectangle` with intermediate-rank sublattice control, or a different entropy-raising operation). That is a wholly unbuilt mechanism. Finishing it would also mean re-running every rate in the source schedule at the new constants, which was not feasible in this round. The calculations above are method diagnostics. They are not a counterexample to the rank-$d$ moat and not an impossibility result for any rank-$d$ proof. Any prime-existence counterexample would need unconditional short-range prime existence, so the only plausible proof direction is a sieve obstruction.

Generic reductions tried before stopping: restriction to a rank-2 sublattice (fails, since walks leave it); linear projection to a rank-2 quotient, and the relative norm $N_{K/k}$ to an imaginary quadratic subfield (the projection does not preserve primality, and the norm is not Lipschitz, so bounded steps become unbounded).
