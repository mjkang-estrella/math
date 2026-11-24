# Three small triangles from five points in a triangle

**Abstract.** We prove Matthew Kahle's Conjecture 3.1. Any five points in a unit-area triangle give at least three label triples of area at most one quarter. The proof uses the subdivision at the three side midpoints. A signed determinant constraint resolves the case in which all four regions are occupied.

## Statement and area convention

Kahle defines the threshold and states the conjecture in §3 as follows. [Points in a triangle forcing small triangles, arXiv:0811.2449](https://arxiv.org/abs/0811.2449)

> In this section we return to using “small” to refer to triangles of area ≤ 1/4.
>
> **Conjecture 3.1.** Given five points in a triangle of unit area, then they form at least three small triangles.

MathDB 317945 records the statement as follows.

> Call a triangle **small** if its area is at most $1/4$. Given five points in a triangle of unit area, consider the triangles determined by triples of the five points. **Three-small-triangles conjecture.** The five points determine at least three small triangles.

The ordinary area in Kahle's statement is expressed by the unsigned shoelace formula. For three planar points, twice the signed area is
$$
d(P,Q,R)=(Q_x-P_x)(R_y-P_y)-(Q_y-P_y)(R_x-P_x).
$$
Half its absolute value is the usual area, one half of base times height. This also gives area zero for collinear points, so a collinear triple counts as a small triangle; this is the convention under which Soifer's Theorem 1.1, quoted by Kahle without a general-position hypothesis, holds. Membership is in the closed triangle, so a point is a convex combination of the three vertices with nonnegative coefficients summing to one. The Lean definitions corresponding to these conventions are

```lean
def det2 (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

def triArea (p q r : ℝ × ℝ) : ℝ := |det2 p q r| / 2

def InTri (A B C X : ℝ × ℝ) : Prop :=
  ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ X = a • A + b • B + c • C
```

The count runs over three-element subsets of the five labels. For five distinct points this is the count of triples of points. The argument also allows coincident points. In that event a repeated pair and each of the other three labels already give three triples of area zero.

## Proof

For the ambient vertices $A_0,B_0,C_0$, put $D=d(A_0,B_0,C_0)$, so $|D|=2$. The affine map
$$
X\longmapsto \left(\frac{2d(A_0,X,C_0)}{D},\frac{2d(A_0,B_0,X)}{D}\right)
$$
sends $aA_0+bB_0+cC_0$ with $a+b+c=1$ to $(2b,2c)$. It sends the closed ambient triangle to the triangle with vertices $A=(0,0)$, $B=(2,0)$, $C=(0,2)$. Its linear part is twice the inverse of the matrix with columns $B_0-A_0$ and $C_0-A_0$, so it multiplies signed determinants by $4/D$. This also follows by expanding determinants after substituting the barycentric coordinates. Thus in the new coordinates the original area of a triple is $|d(P,Q,R)|/4$. Call a normalized triple small if $|d|\le 1$ and large if $|d|>1$.

Write $M=(1,0)$, $L=(0,1)$, $N=(1,1)$ for the side midpoints. For $x,y\ge 0$ and $x+y\le 2$, the regions $x+y\le 1$, $x\ge 1$, and $y\ge 1$ are the corners $(A,M,L)$, $(B,M,N)$, and $(C,L,N)$, respectively. The region $x,y\le 1$ and $x+y\ge 1$ is the central triangle $(M,L,N)$. Together they cover the normalized triangle. Assign each labelled point to any containing region. All inequalities include the boundary.

The affine map permuting $A,B,C$ permutes the corner regions and fixes the central region as a set. It preserves $|d|$, and preserves $d$ for cyclic permutations. A determinant with a fixed set of other arguments is affine in the remaining point. More generally, if a real function is convex in each of its point arguments separately, an upper bound on all tuples of vertices gives the same bound on the product of the triangles. Apply the convex-combination inequality successively in each argument. We use this for the absolute value of a determinant and for sums of absolute values.

### 1. Possible large triples using a pair in one triangle

If $P,Q$ are central, then $|d(P,Q,X)|\le1$ for every $X=(x,y)$ in the ambient triangle. For the central vertex pairs $(M,L),(M,N),(N,L)$, the functions of $X$ are $1-x-y,1-x,1-y$, respectively, each in $[-1,1]$. Reversing pairs changes the sign, equal vertices give zero, and successive convexity of the absolute value in $P,Q$ gives the bound.

For $P,Q$ in the $A$-corner, compute the following triples of values at the ambient vertices for the three distinct vertex pairs.

| Pair | $d(P,Q,A)$ | $d(P,Q,B)$ | $d(P,Q,C)$ |
|---|---:|---:|---:|
| $(A,M)$ | 0 | 0 | 2 |
| $(A,L)$ | 0 | −2 | 0 |
| $(M,L)$ | 1 | −1 | −1 |

The sum of absolute values in any two columns is at most $2$, also for reversed and equal pairs. Convexity in $P,Q$ extends this to every pair in the $A$-corner. All midpoint values consequently have absolute value at most $1$, since each is the mean of its two vertex values. The absolute value at $A$ is at most $1$ by the first column and convexity. At most one of $B,C$ can have absolute value greater than $1$. Thus a large triple with this pair is possible only if the third point is assigned to the corner of that one vertex. If it is large, the determinant has the same sign as its value at that vertex, since the other two vertices of that corner have values in $[-1,1]$. This proves the corresponding facts for all three corners by relabelling. In particular any triple entirely in one corner is small.

### 2. Three in one corner and one in a different corner

Let $P_i=(x_i,y_i)$ for $i=1,2,3$ be in the $A$-corner and $X$ in the $B$-corner. Some $P_iP_jX$ is small. Set $r_i=2-x_i$ and $t_i=y_i/r_i$. Then $1\le r_i\le2$ and $0\le t_i\le 1/2$ because $y_i\le1-x_i\le (2-x_i)/2$. At $B$,
$$
|d(P_i,P_j,B)|=r_i r_j |t_i-t_j|.
$$
If all three triples with $X$ were large, all three determinants with $B$ would exceed $1$ in absolute value by part 1. Order the $t_i$ increasingly. The two consecutive gaps in this order would each exceed $1/4$, since $r_i r_j\le4$. They sum to at most $1/2$, a contradiction. Relabel the corners to apply this to any two distinct corners.

### 3. Two in each of two corners

Let $P,Q$ be in the $A$-corner and $R,S$ in the $B$-corner, ordered within each pair by increasing $y$ coordinate. Suppose all four triples on these points are large. At the ambient vertices we have
$$
\begin{aligned}
d(P,Q,B)&=(2-x_Q)y_P-(2-x_P)y_Q
          \le(x_P-x_Q)y_P\le1,\\
d(R,S,A)&=x_Ry_S-x_Sy_R
          \ge(x_R-x_S)y_R\ge-1 .
\end{aligned}
$$
The bounds use $0\le y_P,y_R\le1$, $0\le x_P,x_Q\le1$ and $1\le x_R,x_S\le2$. The sign rule in part 1 now gives $d(P,Q,S)<-1$ and $d(R,S,Q)>1$. Let $f(X)=d(Q,S,X)$. Cyclic permutation and reversal give $f(P)<-1$ and $f(R)<-1$.

On the other hand, since $x_S+y_S\le2$ and $0\le y_Q,y_S\le1$,
$$
 f(M)=-\big((1-x_Q)y_S+(x_S-1)y_Q\big)
      \ge -\big(y_S+(1-y_S)y_Q\big)\ge-1.
$$
We also have $f(L)-f(A)=f(N)-f(M)=x_S-x_Q\ge0$. Since $f(M)$ is the mean of $f(A),f(B)$, at least one of the latter is at least $f(M)$. If it is $f(A)$, every vertex of the $A$-corner has value at least $-1$, hence $f(P)\ge-1$. If it is $f(B)$, the corresponding argument in the $B$-corner gives $f(R)\ge-1$. This contradiction proves that at least one of the four triples is small.

### 4. Two in one corner, one in each other corner and one central point

Let $P,Q$ be in the $A$-corner, $R$ in the $B$-corner, $S$ in the $C$-corner and $O$ central. Assuming at most two small triples, part 1 shows that exactly two of $PQR,PQS,PQO$ are small and every other triple is large. Swap $B,C$ if needed so that $PQR$ is large, and order $P,Q$ by increasing height in the resulting coordinates. The bound $d(P,Q,B)\le1$ from part 3 and the sign rule in part 1 then give $d(P,Q,R)<-1$.

For $U=(x,y)$ in the $A$-corner and $W=(u,v)$ in the $B$-corner, we claim $d(U,W,O)\ge-1$. At $M$ its value is
$$
 d(U,W,M)=-\big((u-1)y+(1-x)v\big)\ge-\big((1-v)y+v\big)\ge-1 .
$$
Here $u+v\le2$, $0\le y\le1$, $x\ge0$, and $0\le v\le1$ because $u\ge1$. The values at $N,L$ differ from the value at $M$ by $u-x$ and $u+v-x-y$, respectively, both nonnegative because $u\ge1\ge x+y$. This proves the claim at every central $O$ by affinity. Apply it also to the ordered corner pairs $B,C$ and $C,A$ by cyclic permutation. Since $QRO,QSO,RSO$ are large, we have
$$
 d(Q,R,O)>1,\qquad -d(Q,S,O)>1,\qquad d(R,S,O)>1 .
$$
The identity $d(Q,R,O)-d(Q,S,O)+d(R,S,O)=d(Q,R,S)$ follows by expansion. Summing these inequalities with $-d(P,Q,R)>1$ therefore yields
$$
 4<-d(P,Q,R)+d(Q,R,S)=\det(R-Q,S-P).
$$
But the absolute value of that determinant is at most $4$. Indeed it is convex in each of $P,Q,R,S$ separately after taking absolute value. At the ambient vertices each difference is zero or a signed edge vector. The determinant of any pair of such vectors has absolute value $0$ or $4$ by the coordinates of the ambient vertices. Convexity extends this to all four points. The contradiction proves the assertion for this distribution.

### 5. Count the distinct small triples

If at least two points are central, part 1 gives three triples with the same central pair. If four or more points lie in one corner, four of its points give four small triples. Assume neither situation occurs.

If the largest corner has three points, their own triple is small. If the other two points are in distinct regions, each of the three pairs in the first corner gives at least one small triple upon adjoining one of the other two points, by part 1. These give distinct triples. If the other two points are in the same corner, part 2 supplies a small triple with each of them, distinct from each other and from the triple within the first corner.

If two corners have two points each, denote their pairs by $P,Q$ and $R,S$, and the remaining point by $X$. If $PQX$ is large, then $PQR,PQS$ are small by part 1, since $R,S$ are in a different region from $X$. Among triples consisting of $R,S$ together with one of $P,Q,X$, at least one is small because $P$ and $X$ are in distinct regions. This gives a third triple. The same argument applies if $RSX$ is large. Otherwise $PQX,RSX$ are both small and part 3 gives another small triple from $P,Q,R,S$.

The only remaining distribution has a corner with two points, one point in each of the other corners and one central point. Part 4 handles this case. This exhausts all assignments. ∎

## Sharpness and significance

The bound is attained. In the normalized triangle take $(0,0)$, $(0,1/10)$, $(0,17/10)$, $(7/10,6/10)$ and $(2,0)$ in that order. All five are distinct and lie in the closed triangle. In lexicographic order of increasing label triples, the values of $100|d|$ are $0,7,20,119,340,120,112,320,107,101$. Exactly three are at most $100$. Scaling all coordinates by $1/\sqrt{2}$ gives a unit-area example with the same count. Kahle's Figure 16 also exhibits sharpness.

The one-triple bounds of Soifer and Kahle control the smallest of the ten areas. The conjecture controls the third-smallest and gives the sharp five-point count at the quarter-area threshold. For $n\ge 5$ points, applying it to every five-element subset counts each small triple $\binom{n-3}{2}$ times. The resulting lower bound is $3\binom n5/\binom{n-3}{2}=(3/10)\binom n3$. This is the corollary that Kahle derives by averaging immediately after stating Conjecture 3.1; it now holds unconditionally.

## Prior work

Soifer's Theorem 1.1 yields one triangle at area at most $1/4$, and Kahle's Theorem 2.1 lowers the one-triangle threshold to $6/25$. Both apply to five points, and their statements provide no guarantee of additional distinct triples. De Comité and Delahaye refute Kahle's Conjecture 2.6 (that the five-point threshold is $1/6$) with five points whose smallest triangle has area $3-2\sqrt{2}>1/6$. Versions 1 and 2 of their arXiv paper are titled *A Counterexample to Kahle-Conjecture*; version 3 (March 2010) is retitled *Automated Proofs in Geometry: Computing Upper Bounds for the Heilbronn Problem for Triangles*. No version addresses the count in Conjecture 3.1. The closest citing work surveyed in the independent review concerned Heilbronn numbers for seven or eight points. The review's bounded search of citing works, public registries, and title and phrase variants found no resolution of Conjecture 3.1. We did not read the published version (Geombinatorics 18 (2009), no. 3, 114–128) or the chapter on Kahle's results in Soifer's book *How Does One Cut a Triangle?* (2nd ed., Springer, 2009). We expect both to reproduce the arXiv text, but we have not checked this. A refresh on 19 November 2026 found one arXiv version of the source and no further citing work on Conjecture 3.1. [Kahle](https://arxiv.org/abs/0811.2449) · [De Comité and Delahaye](https://arxiv.org/abs/0911.4375)

## Lean formalization

The endpoint `kahle_conj_3_1` filters the three-element subsets of `Fin 5` by the area predicate on their increasing triples. `Kahle.normalizePoint` is the affine map displayed above, and `Kahle.normalize` proves the closed-triangle membership and the threshold equivalence, including equality and zero area.

The geometry is over the real numbers. Vertex checks evaluate explicit coordinates, bilinear estimates use stated products of nonnegative inequalities, and the edge determinant bound uses four applications of the affine convex-combination argument. The corner-pair exclusivity check uses $|d(P,Q,B) + d(P,Q,C)|\le 2$ and $|d(P,Q,B) - d(P,Q,C)|\le 2$, the two linear combinations corresponding to the absolute-value sum in part 1. The last geometric case certifies a disjunction involving the chosen corner triple and the five triples with the central point and two distinct corners. Its proof uses the four signed determinants in the paper after ordering the duplicated corner by height.

For the finite counting proof, Lean sorts the five region labels and splits on the four adjacent ties and whether the last region is central. Each surviving branch combines the geometric disjunctions to exhibit three distinct triples. The proof maps each sorted label back to its original label and uses increasing indices for the resulting triples. The [Lean source appendix](LEAN-SOURCE-APPENDIX.md) contains the complete certificate.
