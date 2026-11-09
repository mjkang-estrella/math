# W021 C — Frobenius support and folded coefficient gcds

**Disposition: revise the interpretation; no verified algorithmic improvement.**
The unfolded support statement and the Frobenius-permutation equivalence are
correct. The proposed computation is a legitimate, inexpensive fixed-menu
factor filter, but its useful coordinates are cyclotomic recurrence residues,
not preserved locations of the original first support. The missing step is a
paid, uniform guarantee of a coefficient that vanishes modulo exactly one
hidden prime. Neither the support identity nor a primality-test theorem supplies
that guarantee. The finite certificate does exhibit additional factor witnesses
beyond the two requested baselines; it establishes no speed advantage, success
distribution, or asymptotic factoring improvement.

This review owns only this report and
[its evidence directory](W021-frobenius-support-review-evidence/). It reviews
section C only. Section A's separate review is not duplicated. No delegation,
installation, commit, shared solver/Lean/STATE/registry change, or extra candidate
execution was performed. The parent can continue construction independently.

**Frozen scope and provenance.** The full task is in
[brief.txt](W021-frobenius-support-review-evidence/brief.txt). Its SHA-256 is
`8d2c43688b73848ec9378234a3bcc06f09338c80226857cafe9cccfb23407171`.
[input-freeze.json](W021-frobenius-support-review-evidence/input-freeze.json)
records byte counts, complete SHA-256 hashes, snapshots, and read scopes for
AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md, README.md, docs/SPECIFICATION.md,
W021.md, STATE.md, and scripts/check.sh. The five requested governing files were
read in full. W021's substantive review covers lines 115–135, section C; section
A/B headings were inventoried and their source bytes copied for provenance only.
The frozen full W021 hash is
`74eff37c1ce3e4272dbe7f0543b18437667bac196e2f68d4ae62cbbf54bf66d9`;
the separately retained [section C excerpt](W021-frobenius-support-review-evidence/W021-section-C.txt)
hash is `2cf39aec144c7f7661ff1fe205f0dd5f23c3d385f332f8ac6c13d8519ecefe67`.
STATE lines 1–89 supply role/context only. An initially overbroad STATE read
was truncated; no historical mathematical finding from that output is relied
on. Frozen snapshots, not the parent's potentially changing live files, define
this review's inputs.

**1. The first unfolded coefficient really gives the larger factor.** Let
distinct odd primes satisfy $p<q$, with $N=pq$. In
$\mathbb F_p[X]$, Frobenius gives

\[
(1+X)^N=(1+X^p)^q.
\]

For $1\le k<p$, both $p$ and $q$ divide $\binom Nk$: their reductions
have support on multiples of $p$ and $q$, respectively, and neither divides
such a $k$. At degree $p$, the coefficient modulo $p$ is $q\bmod p\ne0$,
whereas modulo $q$ it is zero since $0<p<q$. Consequently

\[
\gcd\!\left(N,\binom Np\right)=q.
\]

This proves the stated first-positive-degree claim. It does not give a way to
locate that degree from an encoding of size polynomial in $\log N$.

**2. Exact folded identity and the repaired permutation statement.** Define
the integer remainder and its correction by

\[
C_{n,r}(X)=\sum_{i=0}^{r-1}c_i(n)X^i,
\quad c_i(n)=\sum_{\substack{0\le k\le n\\k\equiv i\pmod r}}\binom nk,
\qquad D_{n,r}=C_{n,r}-1-X^{n\bmod r}.
\]

Both endpoint subtractions occur, even when their positions coincide.
Computing these in $\mathbb Z/N\mathbb Z$ yields the same coefficient gcds
as computing the enormous integer sums and then reducing. In
$R_p=\mathbb F_p[X]/(X^r-1)$, let $\sigma_p(f)=f(X^p)$. Then

\[
C_{N,r}=\sigma_p(C_{q,r}),\qquad
D_{N,r}=\sigma_p(D_{q,r})\quad\text{in }R_p.
\]

If $\gcd(p,r)=1$, choose $s$ with $ps\equiv1\pmod r$.
Substitution by $X^s$ is the inverse of $\sigma_p$, so

\[
D_{N,r}=0\pmod p
\iff D_{q,r}=0\pmod p
\iff (1+X)^q=1+X^q\pmod{(p,X^r-1)}.
\]

More precisely, the coefficient in position $i$ of $D_{N,r}\bmod p$ is
the coefficient in position $si\bmod r$ of $D_{q,r}\bmod p$.
This is an identity for analysis; the algorithm is not given $p,q,s$.

The phrase “spreads its multiples across all residue classes” needs a guard:
the map $j\mapsto pj\bmod r$ visits all residues over a complete block of
$r$ consecutive indices. If $q\ge r-1$, the available positions $0\le j\le q$
hit all residues, but their coefficients can vanish modulo $p$ or cancel in
the sums. If $q<r-1$, even complete positional coverage is not implied.
What always disappears for coprime $p,r$ is the claim that the *integer
divisibility of exponent positions by $p$* singles out residue classes.

When $p\mid r$, substitution need not be injective; the iff assertion above
must not be used. The public baseline $\gcd(N,r)$ diagnoses this regime.
Every sharing case in the fixed prime menu has $1<r<N$, so this baseline
already splits $N$; obtaining its complementary factor costs one division.
General menus could also have $\gcd(N,r)=N$, which is not a proper factor.

**3. Individual coordinates and whole-polynomial vanishing are different.**
For squarefree $N=pq$, a coefficient $d_i$ yields a proper gcd exactly when
it is zero modulo one prime and nonzero modulo the other. Whole-polynomial
vanishing modulo $p$ requires *all* $r$ coordinates to vanish there.
An individual zero is thus a weaker condition, but collecting individual gcds
can find factors that the whole-vector condition misses. It is incorrect to
identify the two extraction rules or to infer the iff above from one coordinate.

There are strong deterministic correlations:

\[
c_i(n)=c_{n-i\bmod r}(n),\quad
d_i(n)=d_{n-i\bmod r}(n),\quad
\sum_i c_i(n)=2^n,\quad\sum_i d_i(n)=2^n-2.
\]

The symmetry follows by pairing $k$ with $n-k$; the endpoint corrections
respect the same pairing. Thus even within one modulus the coefficients are
not independent random draws. No random-coefficient probability is assumed.

Two useful exact consequences hold for every odd $N$, without knowing its
factors:

\[
\gcd(N,c_0,\ldots,c_{r-1})=1,
\quad
G_r:=\gcd(N,d_0,\ldots,d_{r-1})\mid
F_N:=\gcd(N,2^{N-1}-1).
\]

The first follows from their sum $2^N$; the second from their sum
$2(2^{N-1}-1)$ and oddness of $N$. Hence whole-vector content cannot
produce a factor if the base-2 Fermat gcd is 1. If the Fermat gcd is a proper
factor, it has already supplied a split. If it equals $N$, a stricter
whole-polynomial condition could still separate the primes. Individual
coordinates are not restricted by this content-divisibility statement.

**4. Small $r$: exact scalar reductions and a decisive counterexample.**
For $r=2$ and positive odd $N$, the even and odd binomial sums are both
$2^{N-1}$. Therefore

\[
C_{N,2}=2^{N-1}(1+X),\qquad
D_{N,2}=(2^{N-1}-1)(1+X).
\]

The raw coefficient gcds are always 1 for odd $N$. Each corrected gcd is
exactly the ordinary base-2 Fermat gcd. Computing a polynomial gives no
additional information at $r=2$.

For example, take $N=35=5\cdot7$. The unfolded first exceptional coefficient
is at degree 5 with gcd 7, by part 1. But $2^{12}\equiv1\pmod{35}$, so
$2^{34}\equiv2^{10}\equiv9\pmod{35}$. The folded raw vector is $[9,9]$
and the corrected vector is $[8,8]$; all four gcds are 1. This is an exact
counterexample to inheriting a factor witness merely by folding the first
unfolded support. It does not disprove the four-$r$ menu or other polynomial
congruence algorithms.

There is another collapse worth retaining. For odd $N$ with $3\nmid N$,
put $K=(2^N-2)/3\in\mathbb Z$. In the quotient by
$\Phi_3=X^2+X+1$, $1+X=-X^2$, so
$(1+X)^N=1+X^N$ whenever $N\not\equiv0\pmod3$. It follows that the
degree-at-most-2 remainder $D_{N,3}$ is a scalar multiple of $\Phi_3$.
Evaluation at $X=1$ gives that scalar exactly:

\[
D_{N,3}=K(1+X+X^2),\qquad C_{N,3}=D_{N,3}+1+X^{N\bmod3}.
\]

Thus every corrected gcd is $F_N$. The raw coefficients are $K+1$ at
positions $0,N\bmod3$, and $K$ elsewhere; their two possible gcds are
$\gcd(N,2^N+1)$ and $F_N$. Raw $r=3$ is therefore an additional
explicit scalar filter, not automatically identical to corrected $r=3$.
Division by 3 in these gcd identities requires $3\nmid N$; the sharing
control $N=15,r=3$ is excluded from this reduction.

**5. Exact relation to cyclotomic, Lucas, and primality tests.** The following
algebraic descriptions are derivations for this review, not novelty claims.
For $p\nmid r$, $X^r-1$ is squarefree over $\mathbb F_p$. Splitting it
over a finite extension makes the corrected whole-vector condition equivalent to

\[
(1+\zeta)^N=1+\zeta^N\qquad\text{for every }\zeta^r=1.
\]

Equivalently one can test every cyclotomic factor $\Phi_d$, $d\mid r$,
and its irreducible components. The component $\zeta=1$ is base-2 Fermat;
$\zeta=-1$, when present, is automatic for odd $N$. Other components
are extension-field power congruences and need not reduce to that scalar test.
The Fourier identity, in a splitting field, is

\[
c_i(n)=\frac1r\sum_{\zeta^r=1}\zeta^{-i}(1+\zeta)^n.
\]

These are structured sums of powers. If $S$ is cyclic shift and $T=I+S$,
then $C_{n,r}=T^n e_0$ and $(T-I)^r=I$. Each coordinate therefore obeys
the fixed linear recurrence with characteristic polynomial $(Y-1)^r-1$.
For a conjugate pair $\zeta,\zeta^{-1}$, the numbers
$\alpha=1+\zeta$, $\beta=1+\zeta^{-1}$ have

\[
P=\alpha+\beta=2+\zeta+\zeta^{-1},\qquad Q=\alpha\beta=P.
\]

Their powers are governed by the Lucas recurrence
$U_0=0,U_1=1,U_{m+2}=P U_{m+1}-Q U_m$, with the polynomial identity
$\alpha^m=U_m\alpha-Q U_{m-1}$ for $m\ge1$.
In the order-3 component $P=Q=1$, explaining its periodic degeneracy.
For order 5 or 7 the trace $P$ generally lies in a nontrivial cyclotomic
subalgebra; treating these as a single ordinary integer-parameter Lucas test
would require an additional reduction. No such equivalence is asserted.
This is the precise recurrence relationship; it is not a new factor-selection
theorem and does not grant the unknown component fields to the algorithm.

The relevant primary-art matches are narrow:

* AKS's Lemma 2.1 and equation (2) use the same binomial identity and the same
  reduction modulo $X^r-1$. Our corrected expression is their congruence with
  $a=1$. Their actual primality algorithm selects $r$ using an order
  condition and checks a range of $a$'s, besides other steps. Equations
  (3)–(5) and the “introspective” definition describe the same hidden-prime
  cancellation used above. A fixed small menu with $a=1$, followed by
  coordinate gcd extraction, is not the complete AKS algorithm, and its
  factor-extraction completeness does not follow from AKS primality correctness.
  [Agrawal–Kayal–Saxena, author-hosted manuscript](https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf).
* Grantham defines Lucas tests through quadratic recurrences and describes
  Frobenius tests with distinct factorization, Frobenius, and Jacobi stages.
  His Theorem 4.1 identifies the linear-polynomial case with Fermat
  pseudoprimality, and Theorem 4.9 makes a quadratic Frobenius test imply
  the corresponding Lucas test. Our coordinate gcd scan implements none of
  that full set of stages and must not inherit its test guarantees. In
  particular “Frobenius” is an exact algebraic relationship here, not an
  assertion that this scan equals Grantham's test.
  [Grantham, primary manuscript](https://arxiv.org/pdf/1903.06820).

Exact page/line read scopes and file hashes are retained in
[source-read-scope.json](W021-frobenius-support-review-evidence/source-read-scope.json).
The scope is a targeted comparison, not a complete novelty survey or a review
of every cyclotomic primality method. Two failed PDF retrievals are retained;
the successful sources themselves are frozen. No theorem says that all
polynomial congruence methods fail to factor.

**6. Single frozen certificate and what its outcomes actually show.**
[certificate-freeze.json](W021-frobenius-support-review-evidence/certificate-freeze.json)
was written before execution, after static syntax/JSON parsing only. It binds
the complete [code](W021-frobenius-support-review-evidence/certificate.py),
[protocol](W021-frobenius-support-review-evidence/protocol.json), full brief,
input manifest and section-C excerpt. The code hash is
`1264763524524c5aaaa7e607ce9b7488fcf0d07b00498a7cbf1a32d5356fd7dc`;
the protocol hash is
`7fefc0221b6d5db04ebe4dae7aca8f8356004a51303c33c7f56fe61f6dfbfa80`.
Exactly one invocation ran; an exclusive execution marker prevents reruns.
All six specified $N$'s and all four specified $r$'s were retained in their
preregistered order; there was no post-outcome shrinking or replacement.

The run used 18,668 charged events and 0.008526031975634396 seconds measured
from inside the process, against aggregate caps of 20,000 events and 60 seconds.
All 24 cases completed and matched an independent exact-integer binomial
recurrence followed by folding. There were no failed assertions, execution
errors, censored cases, pending audits, or unstarted cases. Rows whose gcds
find no factor are nevertheless retained in full. Every reported proper factor
passed a separate $1<d<N$ and $N\bmod d=0$ verifier; no claim of primality
testing the returned factors is made. The candidate received no factor labels.

[certificate-result.json](W021-frobenius-support-review-evidence/certificate-result.json)
contains all raw/corrected residues, every gcd vector, baseline outputs,
verified witnesses, exact per-row event vectors, independent verifier results,
platform and timing. The table below reproduces *all* coefficient gcd vectors;
index order is $0,\ldots,r-1$. A vector entry $N$ denotes a full gcd and
is not credited as a proper factor.

The clearest difference from a whole-polynomial test is $N=77,r=5$:
$D=[32,36,32,35,35]$. Neither its mod-7 nor its mod-11 vector is zero,
but individual coefficients 35 have verified gcd 7. The raw vector also
has entries 33 with gcd 11. Here the same-$r$ gcd baseline and Fermat gcd
are 1; however, the *full public menu* already contains $r=7$, which splits
77 by plain gcd. That distinction prevents an inflated baseline comparison.

For 143, 221 and 437, every $\gcd(N,r)$ in the menu and the base-2 Fermat
gcd is 1. The retained polynomial witnesses include 11 for 143 at $r=5,7$,
13 and 17 for 221 at $r=7$, and 23 for 437 at $r=7$. These are exact
examples of additional information over the two requested baselines.
Conversely $N=221,r=5$ and $N=437,r=5$ have only unit gcds, raw and
corrected. Subtracting the endpoints can create or destroy a particular
coordinate witness; neither scan should be silently substituted for the other.
The complete menu happened to yield a proper witness for each listed input,
but this fixed, public toy list supplies no success-rate or all-input theorem.

The event total decomposes as 7,305 for the 24 rows (including their plain-gcd
baselines), 173 for input/base-2 baseline work shared once per $N$, and 11,190
for independent coefficient verification. Exactly 5,568 row events are actual
dense convolution coefficient multiply-adds, including every zero term. Each
such event includes multiply, add, modular reduction and cyclic index work;
it is a composite arithmetic event, not one bit operation. Scalar modular
products, each Euclidean remainder and gcd call, decimal input work,
exponent-loop bits, correction/setup operations, witness checks and integer
binomial arithmetic are also charged explicitly. The run made 234 gcd calls
and 989 Euclidean remainders, and 58 scalar modular multiply events. Full
per-category counts are in the result JSON. The plain-gcd baseline's own
remainders are included in each row's gcd counters, not separately timed.

The maximum recorded operand width was 441 bits, mainly from the independent
integer verifier; candidate coefficients stay reduced modulo $N$. Internal
MAC products can be wider than their recorded input operands. Python control,
comparisons, allocation, metadata hashing, serialization and OS startup are
not arithmetic events; source preparation and report writing are outside the
measured invocation. The verifier is intentionally not a scalable algorithm.
No equality between event types, bit costs, or elapsed times is assumed.
The code was syntax-parsed before freezing and executed once with independent
coefficient verification. Project-wide scripts/check.sh was not run: it would
write shared build/test artifacts outside this child's exclusive paths, while
the changed code is isolated certificate evidence and no shared code changed.

For symbolic cost accounting, the literal powering uses
$r^2(\lfloor\log_2N\rfloor+\operatorname{popcount}(N))$ coefficient MACs,
plus input, setup, loop and $2r+1$ gcd-call work per row. The base-2 baseline
is charged separately once per $N$. A fixed finite $r$ menu is therefore
an efficiently computable filter, with no proof it always splits. Faster
polynomial multiplication could reduce the $r$-dependence at paid bit cost;
the certificate does not implement it, and does not empirically establish
W021's soft-linear multiplication estimate.

**7. Exact failed assumption and a concrete different computation.** The
failed implication is: “the first coefficient not divisible by $N$ occurs
at $p$, therefore folding degree positions modulo a short coprime $r$
retains a recognizable factor-selective coordinate.” Folding is a sum over
many degrees; its Frobenius substitution is an invertible permutation, not a
detector of the integer multiple-of-$p$ positions. A proper coefficient gcd
can arise, but a supply theorem for such asymmetric cancellations is missing.

One genuine way to preserve the useful support is **adaptive degree truncation**:
replace cyclic multiplication by multiplication modulo $X^{B+1}$, with
public precisions $B=1,2,4,\ldots$. At each precision compute $(1+X)^N$
modulo $N$ by binary powering, explicitly discarding products of degree
greater than $B$ and never wrapping them to low degrees. Scan the positive
degree coefficient gcds in increasing order. For every $B<p$, they all
equal $N$. At the first $B\ge p$, the coefficient in position $p$
is unchanged from the full polynomial and has gcd $q$, so the procedure
returns a verifier-checkable split. The first such precision is less than
$2p$, so endpoint $X^N$ never intrudes on that successful prefix.

This is executable ordered-prefix computation, not an assumed coefficient
or first-support oracle. Dense truncated convolution across these doubling
precisions costs $O(p^2\log N)$ modular multiply-add work and $O(p)$
coefficient storage, plus the explicitly scanned gcds. Standard faster
truncated multiplication can improve that work bound only with its own
implementation and bit accounting. Literal $p$-sized arrays remain
exponential in the input bit length for balanced semiprimes; even ordinary
trial division is a stronger simple comparator for the dense version.
Thus truncation removes the specific aliasing error, while exposing the
degree-acquisition cost rather than solving it. No new numerical run of this
alternative was made, and no lower bound for compressed representations is
inferred from the literal-array cost.

The next result that could change the disposition is either a paid compressed
prefix computation/localization method with a better end-to-end bound, or a
theorem giving factor-asymmetric coordinate coverage for an explicit public
cyclotomic menu, including its acquisition and extraction costs. More toy
successes alone do not fill either gap. Acceptance of a complete factoring
algorithm remains unjustified; the support invariant and the exact filter
identities are useful retained facts.

**Complete retained gcd vectors and row costs.** `sharing` means the public
plain-gcd baseline already gives a factor. `MAC` counts actual coefficient
multiply-adds; `row events` includes MACs, that baseline and both gcd scans.

| N | r | Class | gcd(N,r) | Raw coefficient gcds | Corrected coefficient gcds | MAC | Row events |
|---:|---:|:---|---:|:---|:---|---:|---:|
| 15 | 2 | coprime | 1 | [1, 1] | [3, 3] | 28 | 63 |
| 15 | 3 | sharing | 3 | [1, 3, 3] | [15, 3, 3] | 63 | 101 |
| 15 | 5 | sharing | 5 | [1, 5, 5, 5, 5] | [3, 5, 5, 5, 5] | 175 | 238 |
| 15 | 7 | coprime | 1 | [1, 1, 5, 1, 15, 1, 5] | [15, 15, 5, 1, 15, 1, 5] | 343 | 422 |
| 35 | 2 | coprime | 1 | [1, 1] | [1, 1] | 32 | 73 |
| 35 | 3 | coprime | 1 | [1, 1, 1] | [1, 1, 1] | 72 | 120 |
| 35 | 5 | sharing | 5 | [1, 5, 5, 5, 5] | [7, 5, 5, 5, 5] | 200 | 267 |
| 35 | 7 | sharing | 7 | [1, 35, 7, 7, 7, 7, 35] | [5, 35, 7, 7, 7, 7, 35] | 392 | 474 |
| 77 | 2 | coprime | 1 | [1, 1] | [1, 1] | 40 | 86 |
| 77 | 3 | coprime | 1 | [1, 1, 1] | [1, 1, 1] | 90 | 145 |
| 77 | 5 | coprime | 1 | [11, 1, 11, 7, 7] | [1, 1, 1, 7, 7] | 250 | 327 |
| 77 | 7 | sharing | 7 | [1, 7, 7, 7, 7, 7, 7] | [11, 7, 7, 7, 7, 7, 7] | 490 | 582 |
| 143 | 2 | coprime | 1 | [1, 1] | [1, 1] | 48 | 99 |
| 143 | 3 | coprime | 1 | [1, 1, 1] | [1, 1, 1] | 108 | 174 |
| 143 | 5 | coprime | 1 | [1, 1, 1, 1, 11] | [11, 1, 1, 11, 11] | 300 | 383 |
| 143 | 7 | coprime | 1 | [1, 1, 1, 1, 1, 11, 1] | [11, 1, 1, 11, 1, 11, 1] | 588 | 704 |
| 221 | 2 | coprime | 1 | [1, 1] | [1, 1] | 52 | 99 |
| 221 | 3 | coprime | 1 | [1, 1, 1] | [1, 1, 1] | 117 | 165 |
| 221 | 5 | coprime | 1 | [1, 1, 1, 1, 1] | [1, 1, 1, 1, 1] | 325 | 418 |
| 221 | 7 | coprime | 1 | [17, 1, 13, 1, 17, 1, 1] | [1, 1, 13, 1, 1, 1, 1] | 637 | 782 |
| 437 | 2 | coprime | 1 | [1, 1] | [1, 1] | 56 | 110 |
| 437 | 3 | coprime | 1 | [1, 1, 1] | [1, 1, 1] | 126 | 201 |
| 437 | 5 | coprime | 1 | [1, 1, 1, 1, 1] | [1, 1, 1, 1, 1] | 350 | 455 |
| 437 | 7 | coprime | 1 | [1, 1, 1, 1, 23, 1, 23] | [1, 1, 1, 1, 23, 1, 23] | 686 | 817 |

**Shared baseline and independent-audit costs.** Per-N totals include all
four rows, input/base-2 work, and the full independent integer audit.

| N | Base-2 Fermat gcd | Input/base-2 events | Independent audit events | All four row events | Combined events |
|---:|---:|---:|---:|---:|---:|
| 15 | 3 | 20 | 189 | 824 | 1033 |
| 35 | 1 | 24 | 429 | 934 | 1387 |
| 77 | 1 | 28 | 933 | 1140 | 2101 |
| 143 | 1 | 33 | 1725 | 1360 | 3118 |
| 221 | 1 | 33 | 2661 | 1464 | 4158 |
| 437 | 1 | 35 | 5253 | 1583 | 6871 |

All reported proper divisors have their verification records in the result
JSON. A coefficient gcd equal to 1 or N is an unsuccessful extraction at that
coordinate and remains in the table. All rows have status `verified`, which
means their coefficients passed the independent audit; it does **not** mean
each row found a factor.

