# A sharp four-point bound for the Hilbert cube

Formalization packet for MathDB 347753, 20 November 2026.

## Abstract

For the Hilbert cube with side lengths (1,1/2,1/3,\ldots), we prove that
every four-point code has minimum squared distance at most
(q=\alpha^2-\alpha), where (\alpha=\sqrt2\pi/3). For every set of positive
integers (N) satisfying the subset-sum hypothesis in Conjecture 27 of King,
Mixon, Parshall and Wells, their printed four-point configuration attains this
bound. A five-edge weighted quadratic inequality proves the upper bound.
The Lean theorem uses Mathlib's actual `lp` space and metric, and quantifies
over all four-element finite subsets of the cube.

## Source statement and literal definitions

The primary source is Emily J. King, Dustin G. Mixon, Hans Parshall and Chris
Wells, *Uniquely optimal codes of low complexity are symmetric*,
[arXiv:2008.12871v3](https://arxiv.org/abs/2008.12871v3), §4.9, pp. 28–29,
Conjecture 27. The supplied review also identifies the journal statement as
Conjecture 4.21 in *Journal of Experimental Mathematics* 2(1) (2026), 81–113,
DOI 10.56994/JXM.002.001.004. This packet directly reads the cached arXiv PDF
and text, and the supplied MathDB corpus row; it does not acquire MathDB's site.
`source-layout.txt` is a fresh text extraction from that cached PDF.
The final review additionally read arXiv v1 and v2 (where this is Conjecture 26),
v3 (Conjecture 27), and the open journal PDF, pp. 107–109 (Conjecture 4.21).
The cube, metric, sum condition and displayed configuration agree in all four.

The introduction's definition, transcribed verbatim, is:

> In particular, we say an arrangement (C) of points in a compact metric space
> ((M,d)) forms an optimal code if its minimum distance (\delta(C)) is as
> large as possible, and we consider compact metric spaces that enjoy a
> nontrivial isometry group.

Here the comparison is among codes of the same size. Lean expands the
four-point comparison into distinct pairs: for every four-element competitor,
some distinct competitor pair is no farther apart than every distinct printed
pair. Because the two finite sets have at least two points, each has a minimum
pairwise distance, so this is precisely the source's optimization property.

The source's cube and metric definition, transcribed verbatim with mathematical
typesetting restored, is:

> Consider the Hilbert cube (H) of sequences (x) such that
> (x_k\in[0,\frac1k]) for every (k\in\mathbb N). Notice that
> (H\subseteq\ell_2) inherits a metric from the 2-norm.

Its immediately following displayed formula includes
(\|x-y\|_2^2=\sum_{k=1}^{\infty}(x_k-y_k)^2).
The indices here are positive integers. The corresponding Lean definitions are:

```lean
abbrev E := lp (fun _ : ℕ+ => ℝ) 2
def w (k : ℕ+) : ℝ := 1 / (k : ℝ)
def H : Set E := {x | ∀ k : ℕ+, 0 ≤ x k ∧ x k ≤ w k}
def e (k : ℕ+) : E := lp.single 2 k 1
```

No replacement metric is defined. `dist` is Mathlib's metric on `E`.
`hasSum_sq_dist`, derived from `lp.hasSum_norm` and therefore
`lp.norm_rpow_eq_tsum`, proves the exact bridge

```lean
HasSum (fun k : ℕ+ => (x k - y k)^2) (dist x y ^ 2)
```

Conjecture 27, transcribed verbatim with mathematical typesetting restored, is:

> Put (\alpha:=\frac{\sqrt2\pi}{3}), select (N\subseteq\mathbb N) such that
> (\sum_{k\in N}\frac1{k^2}=\alpha-1), and define
> 
> \[
> s:=\sum_{k=2}^{\infty}\frac1k e_k,\qquad
> t:=\sum_{k\in N}\frac1k e_k.
> \]
> 
> Then (\{0,(1-\frac12\alpha)e_1+s,e_1+t,
> \frac12\alpha e_1+s-t\}) is an optimal code in the Hilbert cube.

The Lean constant is `α := Real.sqrt 2 * Real.pi / 3`. The source's (s,t)
are represented by the unique `lp` elements with the following coordinates:

```lean
lemma s_apply (k : ℕ+) : s k = if k = 1 then 0 else w k
lemma t_apply (N : Set ℕ+) (k : ℕ+) : t N k = if k ∈ N then w k else 0
```

Membership in `lp` is proved before constructing these elements, by comparison
with the summable reciprocal squares. The source series specify exactly these
coordinates; the optional equality with a norm-convergent vector `tsum` is not
used or separately formalized. Both spaces have the same coordinate indexing;
there is no unproved reindexing or metric-equivalence assertion.

The complete Lean endpoint is:

```lean
theorem conj27 (N : Set ℕ+)
    (hN : HasSum (fun k : N => 1 / ((k : ℕ+) : ℝ) ^ 2) (α - 1)) :
    let C : Finset E := {0, (1 - α/2) • e 1 + s, e 1 + t N, (α/2) • e 1 + s - t N}
    C.card = 4 ∧ (∀ x ∈ C, x ∈ H) ∧
    ∀ C' : Finset E, C'.card = 4 → (∀ x ∈ C', x ∈ H) →
      ∃ u ∈ C', ∃ v ∈ C', u ≠ v ∧ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → dist u v ≤ dist x y
```

This includes every admissible (N), actual cardinality four, cube membership,
and every four-element competitor in (H). The admissibility hypothesis is the
source hypothesis, not an extra restriction. Source Lemma 28 and its succeeding
paragraph construct such sets (N). That existence result is not reproved in
Lean here and is not assumed as an axiom; the theorem is universally conditional
in (N), exactly as requested. No property of one particular choice of (N)
is used.

For explicit nonvacuity, the source takes
\(r_0=\alpha-1-(1/4+1/9+1/16)\), which lies in \((0,1/9)\),
and repeatedly subtracts \(1/a_j^2\), choosing the smallest positive integer
\(a_j\) with \(1/a_j^2<r_{j-1}\). Then \(a_1=5\), and minimality gives
\(1/a_j^2<r_{j-1}\le 1/(a_j-1)^2\). Since \(a_j\ge4\),
\(r_j\le 1/(a_j-1)^2-1/a_j^2\le1/a_j^2\), so \(a_{j+1}>a_j\).
Thus \(a_j\to\infty\), \(r_j\to0\), and
\(N=\{2,3,4,a_1,a_2,\ldots\}\) has exactly the required sum.
This is an explanation of the source's construction, not an additional Lean claim.

## Constants and elementary summation

Write
\[
 c=1-\alpha/2,\qquad q=\alpha^2-\alpha,\qquad
 T=\pi^2/6-1.
\]
The bounds (3<\pi<4) and (1<\sqrt2<3/2) imply (1<\alpha<2).
Consequently (0<c<1/2) and (0<q<\alpha). Squaring the definition gives
(\alpha^2=2\pi^2/9); elementary algebra yields
\[
 T+c^2=q. \tag{1}
\]
Basel's identity gives (\sum_{k\ge1}k^{-2}=\pi^2/6), and hence
(\sum_{k\ge2}k^{-2}=T). In Lean this is `hasSum_zeta_two`, transported to
positive integers using `hasSum_pnat_iff` and the zero term's vanishing.

If (N) is admissible, then (1\notin N): otherwise the nonnegative sum
(\alpha-1) is at least 1, contradicting (\alpha<2). The sum on the
remaining coordinates outside (N) is (T-(\alpha-1)). All sums below are
sums of nonnegative dominated terms or finite linear combinations of convergent
series; every addition and subtraction of sums is therefore justified.

## The printed configuration

Let (P_0=0), (P_1=ce_1+s), (P_2=e_1+t), and
(P_3=(\alpha/2)e_1+s-t). Their first coordinates are
(0,c,1,\alpha/2). On each coordinate (k\ge2), their coordinates are

| Condition | (P_0(k)) | (P_1(k)) | (P_2(k)) | (P_3(k)) |
|---|---:|---:|---:|---:|
| (k\in N) | 0 | (1/k) | (1/k) | 0 |
| (k\notin N) | 0 | (1/k) | 0 | (1/k) |

All lie in the cube. Their squared distances are computed directly from the
metric bridge and the three convergent sums just established:

| Pair | Squared distance before simplification | Value |
|---|---|---|
| (0,1) | (c^2+T) | (q) |
| (0,2) | (1+(\alpha-1)) | (\alpha) |
| (0,3) | ((\alpha/2)^2+T-(\alpha-1)) | (q) |
| (1,2) | ((c-1)^2+T-(\alpha-1)) | (q) |
| (1,3) | ((c-\alpha/2)^2+(\alpha-1)) | (q) |
| (2,3) | ((1-\alpha/2)^2+T) | (q) |

Since (q>0) and (\alpha>0), these points are pairwise distinct; their
Finset has cardinality four. Since (q<\alpha), its minimum squared distance
is exactly (q). The source sentence after Conjecture 27 says that the exceptional
squared distance is (\alpha^2); the displayed points give (\alpha).
Our theorem retains the source's displayed configuration and does not use that
subsequent erroneous distance description.

As a numerical check, the above greedy set has initial members
\(2,3,4,5,8,25,90,842\); its next member exceeds 10,000.
Using just coordinates 1 through 10,000 gives the six squared distances,
in the table's order,
\[
(0.712184448078,\ 1.480960978410,\ 0.712184449054,\
 0.712184449054,\ 0.712284442102,\ 0.712184448078).
\]
Every omitted squared-distance tail is at most
\(\sum_{k>10000}1/k^2<10^{-4}\). These agree with the exact limits
\(q=0.712284443078\ldots\) and \(\alpha=1.480960979386\ldots\).
The numerical truncation is only a check; the preceding exact sum calculations
supply the proof.

## The sharp upper bound

For real numbers (a,b,d,e), set
\[
 W(a,b,d,e)=(a-b)^2+(a-d)^2+2(b-d)^2+(b-e)^2+(d-e)^2.
\]
These are the five edges other than the edge joining the first and fourth
labels, with the edge joining the second and third labels doubled. The labels
will be ordered by first coordinate when this expression is applied below. The sum of the weights is six.

For (a,b,d,e\in[0,w]), we claim
\[
 W(a,b,d,e)\le4w^2. \tag{2}
\]
The case (w=0) is immediate. For (w>0), the identity
\[
\begin{split}
 w(4w^2-W(a,b,d,e))={}&2(w-b)(w-d)(2w-a-e)+2bd(a+e)\\
 &+2wa(w-a)+4wb(w-b)+4wd(w-d)+2we(w-e)
\end{split}
\]
has a nonnegative right-hand side. This proves (2). It is the exact homogeneous
polynomial certificate formalized in `box_bound`.

Next, if (c\le a\le b\le1-c), then
\[
 W(0,a,b,1)\le W(0,c,1-c,1). \tag{3}
\]
Indeed, putting (A=a-c) and (B=1-c-b), the difference of the right and left
sides equals
\[
 2(1-2c)(A+B)+4(b-a)(A+B)+4AB\ge0.
\]
This proves (3), formalized as `cutoff_bound`. Furthermore, if
(0\le a_0\le a_1\le a_2\le a_3\le1), then pushing the extreme first
coordinates outward gives
\[
 W(a_0,a_1,a_2,a_3)\le W(0,a_1,a_2,1). \tag{4}
\]
Each of the four affected squared differences increases separately, and the
doubled middle edge remains unchanged. `ordered_bound` combines (3) and (4)
when (a_1-a_0>c) and (a_3-a_2>c). Finally, expansion gives
\[
 W(0,c,1-c,1)+4T=6q. \tag{5}
\]

Now let (X_0,X_1,X_2,X_3\in H), ordered by first coordinate
(a_i=X_i(1)). Every single squared distance satisfies
\[
 d(X_i,X_j)^2\le(a_i-a_j)^2+T, \tag{6}
\]
because the squared difference in coordinate (k\ge2) is at most (1/k^2).
If (a_1-a_0\le c), equations (6) and (1) show (d(X_0,X_1)^2\le q).
If (a_3-a_2\le c), the same argument applies to (X_2,X_3).

Otherwise both adjacent extreme gaps exceed (c). From (a_0\ge0) and
(a_3\le1), we get (c<a_1\le a_2<1-c). Summing (2) on all tail
coordinates, and keeping the first coordinate exact, gives
\[
\begin{split}
 &d(X_0,X_1)^2+d(X_0,X_2)^2+2d(X_1,X_2)^2\\
 &\qquad+d(X_1,X_3)^2+d(X_2,X_3)^2\\
 &\le W(a_0,a_1,a_2,a_3)+4T
 \le W(0,c,1-c,1)+4T=6q.
\end{split}
\]
Since the weights total six, one of these five distances has square at most
(q). This proves the upper bound in every case.

For complete Finset fidelity, Lean first obtains an equivalence
`Fin 4 ≃ C'` from the competitor's cardinality. It composes this enumeration
with `Tuple.sort` of the first coordinate. The resulting tuple remains
injective and enumerates exactly `C'`; `Tuple.monotone_sort` supplies the
ordering. Thus the pair of distinct indices supplied by the bound corresponds
to distinct points of the original competitor. The proof covers ties in first
coordinates and does not assume any generic position.

Together with the six printed distances, the competitor bound proves
Conjecture 27. Squared-distance comparisons are converted to comparisons of
Mathlib's `dist` using nonnegativity of distance.

## Formal verification

The four source modules are `HilbertDefinitions`, `HilbertDistances`,
`HilbertScalar`, and `HilbertOptimality`. All Lean source is included, byte
exact and in import order, in `LEAN-SOURCE-APPENDIX.md`. The final declaration
is `HilbertCode.conj27`. All lemmas in DESIGN.md are implemented; no intended
endpoint is replaced by a tuple-only assertion or a handwritten series metric.

The packet uses Lean 4.34.1 and the pinned Mathlib revision recorded in
`PINS.json`. All compilations and standalone kernel checks pass through the
provided 32 GiB address-space runner, with its unchanged CPU, resident-memory,
and wall-clock guards. `REPORT.md` records the actual receipts and axiom
outputs. The endpoint depends only on `propext`, `Classical.choice`, and
`Quot.sound`. These statements concern the completed formalization, and do
not constitute independent final review or campaign acceptance.

## Prior art and significance

The supplied cross-model review checked arXiv v3, the source's continuing open
status, its citations, relevant Hilbert-cube code searches, and the named public
proof registries, and found no public resolution. The source already proves
the two-point and three-point cases and existence of admissible (N). The
present packet relies on that bounded review for its historical context; it
does not claim an exhaustive literature search or a new live refresh. A final
review should refresh these checks before acceptance.

The review's strongest counterweight is retained verbatim:

> The method, a weighted-averaging (LP-dual) certificate plus coordinatewise
> convexity, is the standard tool for small optimal codes. Once the tight edges
> of the conjectured configuration are known, complementary slackness nearly
> forces the weights: λ on the opposite edge, with the vertex values 2+λ and 4
> balancing at λ = 2. A specialist who tried for an afternoon would probably
> find it. I rate the chance that a specialist calls it “an exercise” at about 40%.

This is a short elementary resolution of a specific conjectured code, not a
general theory of optimal codes in infinite-dimensional boxes. The decisive
certificate uses the five-edge weights and the matching first-coordinate
threshold. Ordinary unweighted six-edge averaging does not yield the sharp
value. We do not classify all optimal configurations, prove uniqueness, or
settle the source's broader questions about larger codes or unicorn spaces.
The review regards the result as provisionally significant while explicitly
flagging the short-proof risk; campaign credit remains root's decision.
