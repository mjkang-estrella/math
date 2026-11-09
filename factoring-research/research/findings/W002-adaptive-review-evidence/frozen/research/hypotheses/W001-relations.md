# W001 — Relations, residuals, and dependency structure

Bounded independent ideation pass, 2026-10-07 America/Los_Angeles.
Scope: classical integer factoring; relation generation and dependency extraction.
Evidence level: **ideas plus explicit model calculations, not an experimental screen**.
Verified new factoring improvement: **NONE**.

Read the project instructions and specification, including the required loop/checkpoint documents. No other hypothesis was used as a starting point. This report is the only output of this pass. No solver, harness, Lean, checkpoint, or other research output was changed; no scratch computation was run.

## Accounting shared by the cards

Write $n=\lfloor\log_2N\rfloor+1$, $t=\log N=\Theta(n)$, and

\[
 L_N[\alpha,c]=\exp((c+o(1))t^\alpha(\log t)^{1-\alpha}).
\]

Thus an improvement in the leading constant $c$, an improvement in the exponent $\alpha$, and a finite-size speedup are different claims. Polynomial factors in $n$ do not change a positive-$\alpha$ leading constant. No card below establishes any of these improvements.

The relevant reference scales are heuristic QS $L_N[1/2,1]$, ordinary GNFS $L_N[1/3,(64/9)^{1/3}]$, and Coppersmith's multiple-field improvement with constant

\[
 c_C=((92+26\sqrt{13})/27)^{1/3}\simeq1.90188,
\]

against ordinary GNFS's approximately 1.92299. Reusing a rational smoothness computation across fields is already known. Lee–Venkatesan prove bounds for generating square congruences in randomized variants; their factor-extraction result has additional hypotheses and restricted scope. Their result must not be cited as unconditional general factoring at these bounds. Sources: [Pomerance, *Smooth numbers and the quadratic sieve*](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/03carl.pdf), [Coppersmith, *Modifications to the Number Field Sieve*](https://research.ibm.com/publications/modifications-to-the-number-field-sieve), and [Lee–Venkatesan, introduction and §2](https://arxiv.org/html/1805.08873v1).

For every card the actual trial cost is

\[
 T_{\rm trial}=P+G+C+F+T_{\rm LA}+T_{\rm root}+T_{\rm gcd},
\]

where $P$ includes prime-base, polynomial, lattice, and other preprocessing; $G$ all candidates generated, including rejected ones; $C$ exact smooth-part/cofactor/ideal processing; and $F$ deduplication, filtering, and dependency lifting. If the filtered matrix has dimension scale $D$ and $W$ nonzero entries, the usual sparse Krylov model costs roughly $\widetilde O(DW)$ bit operations and $\widetilde O(W+D)$ bits, with restart/verification costs included. Dense fill invalidates a claim of quadratic cost in $D$. [Thomé's primary paper](https://arxiv.org/abs/1604.02277) supplies the relevant sparse-linear-algebra context.

All modular operands can be kept to $O(n)$ bits; exact norm operands instead have their measured width $w$, and product/remainder trees have nodes as large as the aggregate input bit length $S$. These are not unit-cost operations. Relation records, factor exponents, provenance, and dependency lifting are charged. Batch arithmetic may reduce overhead, but cannot manufacture smooth values: [Bernstein, *How to find smooth parts of integers*](https://cr.yp.to/factorization/smoothparts-20040510.pdf), whose indexed primary text was verified, explicitly prices its algorithm in the total input bits.

For NFS cards, ideal parity alone is insufficient: retain signs, exceptional-prime handling, square-class/character conditions, and the algebraic square-root computation. No maximal-order computation, class-group computation, factoring of a discriminant, or algebraic-square-root oracle is assumed free. The conditional leading-constant models below require the usual NFS completion costs to stay within the quoted total bound. A candidate that makes them larger fails that model. [Stevenhagen, §§5–10](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf) explains the distinction between even ideal valuations and an actual square.

Let $\sigma(N)$ be the probability that a completed independent trial produces a verified proper divisor, including unsuccessful collection and trivial square congruences. Expected splitting cost is $T_{\rm trial}/\sigma(N)$, not just relation cost. A lower bound on $\sigma(N)$ is unsupported for every new sampling bias proposed here. Even inputs and perfect powers can be handled separately with polynomial-bit algorithms; a favorable result on the remaining tested semiprimes would still not establish the all-composite contract.

## Card A — Force square prime-ideal divisors, then optimize the lattice shape

**Primitive.** Let $f(m)\equiv0\pmod N$, $\deg f=d$, and $F(a,b)=b^df(a/b)$. Generate a known prime $q\nmid N\operatorname{disc}(f)$, find a simple root $r\bmod q$, and Hensel-lift it to $r_e\bmod q^e$, with $e\ge2$ even. Enumerate primitive points in

\[
 \Lambda_{q,e}=\{(a,b):a-r_eb\equiv0\pmod {q^e}\}.
\]

The known ideal $(q,\alpha-r)$ then has valuation at least $e$ in $a-b\alpha$. Remove that known even contribution and test $F(a,b)/q^e$ and $a-bm$. Further $q$-valuation is not silently discarded. A gcd with $N$ at any failed invertibility check is an allowed factor discovery.

The speculative part is to choose a reduced, skewed lattice window aligned with a small-value region of $F$, rather than accept a generic square window. Construct the window using explicit real-root approximations and two-dimensional reduction, and count every examined window and prime. This attempts to obtain square-ideal divisibility without its full geometric norm penalty.

**Proposed gain and full cost.** With $J$ windows, $K_j$ enumerated points, and qualifying probability $p_j$, the usable relation count is at most $\sum_jK_jp_j$, before duplicate/rank losses. Cost is

\[
 P_{q,\mathrm{roots},\mathrm{windows}}+
 \widetilde O\!\left((\sum_jK_j+B)\operatorname{poly}(n,d,w)\right)
 +F+\widetilde O(DW)+T_{\rm root},
\]

using batched exact smooth processing; retaining partial cofactors adds their actual processing. Streamed windows need their sieve storage plus prime/ideal records and the relation matrix. Enumerating all primes up to a cutoff costs that enumeration; random prime generation still charges primality tests, failed primes, finite-field polynomial factorization, and lifts.

Here is the cheap adverse calculation. Put $Q=q^e$. The lattice determinant is $Q$. To retain $A^2$ points in a generic isotropic window, coordinate size increases from $A$ to about $A\sqrt Q$. Consequently,

\[
 |F|/Q:\quad Q^{d/2-1}\text{ times the old scale},\qquad
 |a-bm|:\quad Q^{1/2}\text{ times the old scale}.
\]

The product of the residual sizes worsens by $Q^{(d-1)/2}$. Alternatively, holding the physical window fixed loses a factor $Q$ in candidate count. Neither accounting permits a free $Q$-fold smoothness improvement. Reusing many windows must count repeated pairs only once.

An $L_N[1/3,c]$ improvement would require an explicitly constructed anisotropic family whose *total* relation yield, after window-search costs, improves the relevant smoothness exponent and still supplies $D$ plus excess independent rows. Small fixed $q,e$ improvements normally change lower-order/practical costs. No $\alpha<1/3$ mechanism appears here.

**Prior art and distinction.** Special-$q$ lattice sieving and sieving prime powers already exist; forcing known factors is not the invention. The narrow proposed delta is systematic even-valuation conditioning combined with a quantified low-norm lattice-shape selection rule. Modern sieving also pays cofactor-processing costs: [Bouillaguet–Fleury–Fouque–Kirchner, *We Are on the Same Side*](https://eprint.iacr.org/2023/801). The original NFS treatment already describes lattice/partial-relation mechanisms: [Lenstra et al., *The Development of the Number Field Sieve*](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/1993_Book_TheDevelopmentOfTheNumberField.pdf). No novelty claim follows from this bounded search.

**Assumptions and scope.** Polynomial selection must be performed from $N$. Easily skewed polynomials for special-form $N$ give only a special-family result. The determinant argument is an isotropic model calculation, not a lower bound for all lattices or real-root neighborhoods. The missing assumption is a sufficiently frequent, cheaply locatable favorable anisotropic shape.

**Cheapest decisive falsifier.** Before smoothness testing, compare the distribution of
$\log|F(a,b)/Q|+\log|a-bm|$ at equal *total enumerated points and preprocessing work* against ordinary special-$q$ windows. Reject the proposed selector if its apparent norm reduction disappears under that accounting. The isotropic version already fails this calculation. **Disposition: reject the generic version; reserve only the explicitly missing shape lemma.**

## Card B — Defer cofactorization and solve over a coprime residual basis

**Primitive.** Start with exact QS/MPQS relations

\[
 U_i^2\equiv S_iR_i\pmod N,
\]

where $S_i$ is completely factored over primes $\le B$, including its sign, and $R_i>0$ is the exact remaining cofactor. Admit a fixed, preregistered *bit budget* of residuals, including composites rejected by a two-large-prime rule. Do not individually factor $R_i$.

Compute a gcd-free, pairwise-coprime basis $c_1,\ldots,c_k>1$ with certified exponent decompositions

\[
 R_i=\prod_jc_j^{e_{ij}}.
\]

Detect square $c_j$ by integer square root; their roots are known. Use one parity column for every remaining nonsquare $c_j$, plus the factor-base/sign columns. Peel singleton columns for the *current* batch, then solve the remaining kernel. Preserve raw rows if the batch will grow: a row that is a singleton now can become useful later. Rebuilding on geometrically increasing batch sizes charges all earlier rebuilds.

For a dependency, multiply the $U_i\bmod N$, and construct the other square root from the smooth-prime exponents, square-basis roots, and $c_j^{(\sum_i e_{ij})/2}\bmod N$. Verify the congruence and both gcds. No hidden cofactor factorization is needed.

**Exact invariant, with an elementary proof.** For pairwise-coprime $c_j$, the product of selected $R_i$ is a square iff every nonsquare-basis exponent sum is even. Necessity: a nonsquare $c_j$ has some prime with odd valuation; that prime divides no other basis element. Sufficiency: even exponents have the displayed explicit roots, and square bases already have roots. Therefore the kernel is **exactly the square-product kernel obtained by fully factoring the same residuals**, not merely a subset of it. This preserves dependencies; it cannot create additional ones on a fixed list. This is an informal mathematical observation using an established primitive, not a new factoring theorem or a Lean result.

**Proposed gain and full cost.** If $h$ residuals occupy $S\le hw$ bits, fast coprime refinement is essentially linear in $S$, with arithmetic on up to $S$-bit tree nodes. Store decompositions and provenance, costing $\widetilde O(S)$ bits. After filtering, let the actual matrix parameters be $D,W$. The complete charged proposal is

\[
 T_B=P_B+G_B+C_{\rm smooth}+S^{1+o(1)}+F+
 \widetilde O(DW)+\widetilde O(hw\operatorname{poly}(n));
\]

the last term covers square tests, dependency reconstruction, modular products and gcds. Memory includes the raw residual queue, decomposition output, filtered matrix, and smooth-part metadata. A simple pairwise-gcd implementation costs up to quadratic work in $h$; it cannot claim the fast bound.

The desired saving is the baseline's individual cofactor-splitting work, plus any cost reduction from compressed repeated-support columns, minus refinement, broader admission, and matrix growth. If all residuals are pairwise coprime nonsquares, $k=h$ and they contribute **no** residual dependencies. Merely collecting more partials can therefore make the method worse.

For QS-scale quantities $G_B=L_N[1/2,g]$, $h=L_N[1/2,a]$, and a sparse filtered core $D=L_N[1/2,b_*]$ with polynomial row weight, the conditional full leading exponent is

\[
 L_N[1/2,\max(g,a,2b_*)],
\]

assuming the explicitly listed remaining costs fit that envelope. Admitting all raw QS candidates can make $a\approx1$ and an unfiltered linear-algebra constant near 2, worse than QS's constant 1. With ordinary relation-generation/filtered-core behavior this card offers only a possible practical saving, **no established improvement to QS's $\alpha$ or $c$**. It is not an asymptotic competitor to GNFS as stated.

**Prior art and distinction.** The coprime-basis primitive and its complexity are established: [Bernstein, *Factoring into coprimes in essentially linear time*, institutional primary publication record](https://research.tue.nl/en/publications/factoring-into-coprimes-in-essentially-linear-time/) and [author's paper index](https://cr.yp.to/coprimes.html). Pairing residuals and finding large-prime cycles are also established: [Lenstra–Manasse, *Factoring with two large primes*, primary article repository](https://infoscience.epfl.ch/server/api/core/bitstreams/490ebcc2-36fb-4a5a-80fa-6a8e6f0831fe/content).

The testable delta is **deferred, batch-wide splitting with admission controlled by retained-core yield per input bit**, compared with independently splitting bounded cofactors before filtering. It is not a claim to invent coprime bases or large-prime relations. Whether an existing implementation already makes this exact tradeoff remains to be checked before any novelty claim.

For independent uniform integer samples, there is already a sharp threshold for the existence of any square-product subsequence: [Balister–Bollobás–Morris, *The sharp threshold for making squares*](https://arxiv.org/abs/1608.03857). Faster representation of the same kernel does not move that existence threshold. This theorem is not a lower bound for correlated QS/NFS norm values.

**Assumptions and scope.** The exact lemma applies to integer-square relations for arbitrary $N$; useful splitting probability still needs measurement/proof. Applying a coprime basis only to *integer algebraic norms* does **not** preserve NFS ideal dependencies: different ideals can have the same rational norm. Direct transfer is valid only on NFS's rational side. An algebraic extension must construct suitable ideal decompositions and retain square-class constraints, at charged cost; that extension is not supplied here.

**Cheapest decisive falsifier.** On a fixed prefix of genuine QS norm values, compare exact kernels against a fully factored diagnostic reference, then compare retained-core nullity and total processing against a conventional two-large-prime pipeline under the same residual bit cap. Reject the prototype if extra residuals add no usable nullity and refinement plus extra matrix work costs at least the saved cofactor work. Also count trivial gcd outcomes. **Disposition: first practical survivor; not a disruptive complexity result.**

## Card C — Sieve higher-degree elements after seeking unusually small resultants

**Primitive.** Build a monic base-$m$ NFS polynomial $f$ of degree $d$, with $m\approx N^{1/d}$ and coefficient height of order $N^{1/d}$. Enumerate primitive polynomials

\[
 g(X)=a_0+\cdots+a_{r-1}X^{r-1},\qquad |a_i|\le H,
\]

initially $r=3$, rather than only linear elements. Evaluate $g(m)$ and the exact resultant $\operatorname{Res}(f,g)$. The candidate selector first constructs a coefficient lattice/window that makes $g$ small at selected real embeddings, or at both coordinates of a complex embedding; it then enumerates that window and rejects zero/reducible/duplicate constructions that merely reproduce previously counted products. Construct the embeddings with certified precision; lattice reduction/enumeration and the number of failed windows are charged.

A concrete first selector is the intersection of the coefficient cube with the slab
$|a_0+a_1\alpha_j+a_2\alpha_j^2|\le\epsilon H(1+|\alpha_j|+|\alpha_j|^2)$
for one chosen real root, testing each real root and
$\epsilon=\exp(-\lambda t/d)$ for $\lambda\in\{1,3/2,2\}$.
For a chosen complex root use the corresponding disk, imposing both real
constraints. Enumerate the integer points with certified rational enclosures;
the conservative implementation may simply inspect the entire coefficient cube.
The slab's reduced volume, increased height if the cube is enlarged, and
cost of locating its points are all charged. This particular selector may fail
immediately; it makes the proposed tail question experimentally definite.

The hoped-for mechanism is a *frequent small-resultant tail*, not the extra coefficient alone. Norm factorization must distinguish every relevant prime ideal, including higher-residue-degree ideals that linear elements did not use. For fixed $r$, allowing all factors of $f\bmod p$ of degree at most $r-1$, for rational $p\le B$, enlarges the base by polynomial factors in $d$, not automatically by an $L$-constant. Exceptional ideals and character columns remain.

**Proposed gain and explicit cost model.** Let

\[
 H=L_N[1/3,a],\quad B=L_N[1/3,b],\quad
 d=\delta(t/\log t)^{1/3},
\]

with fixed $r$. Standard coefficient/resultant bounds give

\[
 \log |g(m)|\lesssim (r-1)t/d+\log H,
\]
\[
 \log |\operatorname{Res}(f,g)|
 \lesssim (r-1)t/d+d\log H+O(d\log r+r\log d).
\]

These are upper bounds. Treating their main scales as typical is a stated heuristic, not a norm lower bound. In that model the product-size coefficient at scale $t^{2/3}(\log t)^{1/3}$ is

\[
 C_r=2(r-1)/\delta+a\delta.
\]

The usual two-sided smoothness heuristic yields probability
$L_N[1/3,-C_r/(3b)]$. There are $L_N[1/3,ra]$ coefficient tuples, and roughly $L_N[1/3,b]$ independent relations are required. Hence

\[
 ra\ge b+C_r/(3b),\qquad
 c\ge\max(ra,2b).
\]

Generation, resultant computation, finite-field ideal identification and batch smooth-part extraction cost the number of tuples times polynomial-bit overhead when $r$ is fixed, $d=\operatorname{poly}(n)$, and the displayed widths hold. Polynomial/base construction costs $B\operatorname{poly}(n)$. Store only accepted relations and a bounded batch; memory is approximately $B\operatorname{poly}(n)$, with partials charged separately. Standard sparse linear algebra gives the $2b$ term; rank loss, selector cost, or more expensive algebraic square-root reconstruction adds to this model.

Balancing $ra=2b$ and minimizing over $\delta$ gives, by direct calculation in this report,

\[
 c_r^3=\frac{128(r-1)}{9r}.
\]

For $r=2$ this recovers $64/9$. For $r=3$, $c_3\approx2.117$, **worse** than ordinary GNFS and Coppersmith. Thus simply adding a third coordinate fails its own model.

Now suppose a constructive selector replaces the resultant coefficient penalty $(r-1)t/d$ by $\eta(r-1)t/d$, while retaining the rational bound. Under the optimistic assumption of no $L$-scale selection loss, the recalculated target is

\[
 c_{r,\eta}^{3}=\frac{64(r-1)(1+\eta)}{9r}.
\]

For $r=3$, beating ordinary GNFS requires $\eta<1/2$; beating $c_C$ requires

\[
 \eta<\frac{92+26\sqrt{13}}{128}-1\simeq0.4511.
\]

If qualifying small-resultant elements occupy only fraction $L_N[1/3,-\tau]$ of the enumerated volume, the actual relation condition is instead

\[
 ra\ge b+\tau+
 \frac{(r-1)(1+\eta)/\delta+a\delta}{3b}.
\]

Selector search, correlations with rational smoothness, rank loss, and failed embedding windows can make it still worse. Counting only the accepted small resultants would hide $\tau$. These formulas propose a **conditional leading-constant** improvement; no exponent improvement or polynomial-time route is derived.

**Prior art and distinction.** Higher-degree $g(\alpha)$ norms via resultants are explicitly known: [Stevenhagen, §3](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf). Optimizing the NFS defining polynomial for size/root properties is established: [Bai–Brent–Thomé, *Root optimization of polynomials in the number field sieve*](https://arxiv.org/abs/1212.1958). The proposed delta is a charged selector for the *sieving element* $g$ at fixed $f$, with a quantitative resultant-tail target, not another name for polynomial selection or Coppersmith's smoothness reuse. The bounded search does not establish that this delta is novel.

**Assumptions and scope.** The unproved ingredient is a large enough, uniformly constructible family of $g$'s satisfying the $\eta,\tau$ inequality, whose rational images and ideal vectors retain useful diversity. Exceptional $f$ from special-form $N$ supply only a scoped result. Choosing high-dimensional short vectors is not treated as a free oracle; if $r$ grows, enumeration, resultant sizes, and matrix-base growth must all be reanalyzed. The fixed-$r$ calculation cannot be extrapolated to growing dimension.

**Cheapest decisive falsifier.** Prove or refute the following focused counting target before building a siever: for an explicitly defined $r=3$ embedding-window selector, are there sufficiently many primitive, nonredundant $g$ with

\[
 |\operatorname{Res}(f,g)|\le H^d N^{2\eta/d}\exp(o(t^{2/3}(\log t)^{1/3}))
\]

at $\eta<0.4511$, and with the counted $\tau$ small enough for the preceding inequality to yield $c<c_C$? Showing that this selector's tail loss or enlarged $g(m)$ cancels its gain rejects that selector. **Disposition: second survivor, highest disruptive potential here, but missing its central construction/counting lemma.**

## Card D — Generate relations with block-local parity supports

**Primitive.** Split the explicit factor base into $k$ disjoint groups. After complete relation processing, retain a row only if all its nonzero parity coordinates lie in one group. Maintain separate matrices, collecting enough excess rows to obtain a dependency within a group. For NFS, assign *all* ideal and character coordinates too; ignoring cross-group characters would manufacture false squares. Recover and verify square roots as usual.

The speculative generation variant uses structured norms with prescribed prime-splitting behavior to make rows group-local before testing. Its required output is an explicit generator and distribution guarantee, not a promise that a conveniently structured matrix will arrive.

**Proposed gain and full cost.** If $M$ is total column count and groups/rows are balanced, sparse linear algebra on all groups targets $\widetilde O(M^2/k)$, with total matrix storage $\widetilde O(M)$ for polynomial row weight. Group assignment, relation factorization, membership testing, collection imbalance and dependency reconstruction remain charged. Early termination upon one group's success can help, but a post-filtering generator usually spreads accepted rows over all groups; it cannot assume all accepted rows fill the desired group.

Put $M=L_N[1/3,b]$, $k=L_N[1/3,\kappa]$, and let ordinary generation exponent be $g(b)$. If total locality loss is only $L_N[1/3,\lambda]$, and a generator with exponent $p$ achieves it, the optimistic full bound is

\[
 L_N[1/3,\max\{p,g(b)+\lambda,2b-\kappa\}],
\]

provided all root/filtering costs fit and useful splitting probability is bounded below. This makes explicit the possible route to a smaller $c$: cheaper linear algebra must allow a favorable reoptimization of $b$ after paying $\lambda$ and $p$. There is no $\alpha$ improvement just from a constant $k$.

**Immediate entropy test.** Independently assign each factor-base coordinate a uniform group. A row with $s\ge1$ distinct odd-support coordinates is local with exact probability

\[
 k^{1-s}.
\]

This identity is conditional on the row and averages over assignments; it does not require independence of the integer's prime factors. Zero rows are already dependencies and are handled separately. For $s$ of order $(t/\log t)^{1/3}$, a typical NFS-scale modeling choice, any positive constant $\kappa$ produces a penalty with logarithm of order $t^{2/3}(\log t)^{1/3}$: an $L_N[2/3,\Theta(1)]$ penalty overwhelming the matrix saving. The actual support-size distribution must be measured; this is not asserted for every norm or every input.

A shared small-prime core plus a few outer coordinates can avoid that particular penalty, but then elimination must track the shared core and fill. That construction runs directly into existing large-prime cycle/filtering methods. It does not justify the disjoint-block cost without separately pricing the resulting core matrix.

**Prior art and distinction.** Sparse nullspace methods already exploit sparsity $[Thomé](https://arxiv.org/abs/1604.02277)$; large-prime cycle combinations already eliminate selected columns $[Lenstra–Manasse](https://infoscience.epfl.ch/server/api/core/bitstreams/490ebcc2-36fb-4a5a-80fa-6a8e6f0831fe/content)$. The attempted delta is to **create low-interaction matrix structure during relation generation**. It is not post hoc relabeling or the known elimination of large-prime columns. No primary source located in this pass supplies the required norm generator.

**Assumptions and scope.** An algebraically constrained norm family might have very different support statistics, but its construction, density, degree, coefficient heights and residual factorization must replace the random-label calculation explicitly. Restricting $N$ to fit that family is a special-family claim. Matrix nullity remains different from nontrivial square-root signs modulo unknown factors.

**Cheapest decisive falsifier.** For a fixed relation stream, histogram $s$, calculate the exact predicted acceptance $\sum_s h_s k^{1-s}$, and compare rows per group with required columns/excess. Reject random partitioning before running expensive linear algebra if collection dominates the projected saving. **Disposition: reject random-label post-filtering as a disruptive mechanism; unsupported structured generation remains a different, unresolved problem.**

## Ranking and recommended next action

1. **B, deferred cofactorization:** strongest inexpensive survivor, because the exact integer dependency invariant is clear. Expected opportunity is a practical pipeline saving or a useful negative result, not a better factoring exponent. The algebraic-ideal extension is not assumed.
2. **C, small-resultant element generation:** best conditional route to a leading-constant change in this pass. The $\eta<0.4511$ target with charged tail loss makes the missing lemma concrete. The unmodified higher-degree enumeration is already unfavorable.
3. **A, square-ideal conditioning:** only a specific favorable-shape construction merits reopening; generic determinant accounting loses.
4. **D, block-local supports:** ordinary random partitioning loses; no surviving generator has been supplied.

**Recommended bounded next step:** run one small, fixed-list screen of B, capped at **60 seconds**, using only an explicit QS relation source and a fixed aggregate residual bit cap. Freeze the norm list first; report candidate generation separately and include it in any end-to-end comparison. Compare (i) coprime-basis kernel, (ii) fully factored diagnostic kernel on the same list, and (iii) an ordinary two-large-prime admission/filtering rule. Record raw bits, refinement time/width, rows and columns after peeling, matrix nonzeros, exact nullity, reconstruction cost, and proper versus trivial gcds. The diagnostic's full factorization is a reference cost, never an oracle supplied to the candidate. Stop on the cap and retain censoring.

Concrete screening parameters: four evaluator-generated products of distinct
independently sampled 16-bit primes, evaluator seed 1001; candidate seed 2001;
$B=257$; the first $2^{12}$ distinct values
$Q(x)=x^2-N$ with $x=\lceil\sqrt N\rceil+j$ and
$0\le j<2^{12}$; residual storage cap $2^{18}$ bits per input.
The baseline admits at most two primes above $B$, each at most $B^2$.
Only $N$, the public parameters and candidate seed cross the solver boundary.
Include prime/base construction in the candidate cost; keep evaluator generation
and diagnostic factorization separately identified. At this tiny size the
experiment can falsify bookkeeping and admission economics only. It cannot
establish practical competitiveness with optimized QS or NFS.

Reject B's concrete prototype if kernel equality fails, or if extra admission gives no usable nullity and its total added processing exceeds cofactor work saved. A toy speed win would authorize only a larger matched comparison, not a GNFS or asymptotic claim. If this practical question is outside the parent task's priority, spend the next bounded pass solely on C's stated resultant-tail lemma; do not build a new framework.

All links above were checked through primary publication text, author/institutional records, or primary indexed text during this pass. Some author/AMS PDF endpoints intermittently failed direct retrieval; where applicable a working institutional record or indexed primary text was used instead. This was a targeted prior-art check, not an exhaustive novelty search. No card currently meets the all-input correctness, useful-success, and complete complexity requirements of the project specification.
