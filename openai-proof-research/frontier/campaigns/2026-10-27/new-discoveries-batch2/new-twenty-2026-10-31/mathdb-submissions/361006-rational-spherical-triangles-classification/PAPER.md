# Classification of proper rational spherical triangles

## Abstract

We prove Conjecture 1.6 of Haiyang Wang, *Rational Spherical Triangles* (arXiv:2312.01633v1): the measurements $(E,a,b,c)$ of proper rational spherical triangles are exactly the two-right-side family and eight sporadic tuples, namely Wang's sets $\Lambda_1\cup\Lambda_2$. The proof classifies affine lines through the proper tangent simplex, uses that classification to bound the conductor of every remaining solution by $2^5 3^2 5^2 7^2$, and finishes with an exact finite search over roots of unity. The proof is computer-assisted, and the search is replayed in the Lean kernel: the Lean theorem `Wang.wang_conj_1_6_Omega2 : Wang.Conjecture16` has no hypotheses and states that a rational quadruple lies in Wang's solution set $\Omega_2$ of L'Huilier's equation exactly when it lies in $\Lambda_1\cup\Lambda_2$. The one link outside Lean is Wang's own Proposition 2.2, $\Omega_1=\Omega_2$, which identifies $\Omega_2$ with the set $\Omega_1$ of measurements of proper rational spherical triangles; it is printed and proved in the source from L'Huilier's theorem and the converse of the spherical triangle inequality. Dvornicich, Lombardo, Veneziano and Zannier (arXiv:2404.02559, §0.5) had written that the main conjecture of Wang's paper should be amenable to their methods for trigonometric-diophantine equations; the present proof uses the same family of methods (vanishing sums of roots of unity and an exhaustive torsion search). The proof, the Lean code and this paper were written by GPT-6.2 Sol lanes and reviewed by Claude Opus 5.5 lanes. All of it is AI-generated, and no human has checked it.

*[Status note for the coordinating lane: when this revision was written, the full kernel rebuild of the 7,688-module packet was still running. Remove this note when it has succeeded; if it fails, the sentence about the Lean kernel must be withdrawn.]*

## Source definitions and conjecture

Wang’s §1.1 reads:

> A spherical triangle is a triangle on the unit sphere such that each side of the triangle is an arc on a great circle of the unit sphere. We call a spherical triangle proper if the length of each side of the triangle is less than $\pi$ and the area of the triangle is less than $2\pi$.

The source defines the ambient set, rationality, and measurements as follows.

> Let $G:=\mathbb Q\pi=\{r\cdot\pi\mid r\in\mathbb Q\}$. For a nonzero element $g$ in $G$, we define the numerator and denominator of $g$ to be that of $g/\pi$ in reduced form, respectively. We denote the numerator and denominator of $g$ by $\operatorname{num}(g)$ and $\operatorname{den}(g)$, respectively.
>

> Definition 1.3. A spherical triangle on the unit sphere is called rational if the lengths of its sides and its area are in $G$.
>
> Definition 1.4. Let $\Delta$ be a proper spherical triangle on the unit sphere. Assume that $\Delta$ has side lengths $a\le b\le c$ and area $E$. We associate the tuple $(E,a,b,c)$ to $\Delta$ and call this tuple the measurement of $\Delta$. Note that $a$, $b$ and $c$ determine $E$ by Theorem 1.2. We include $E$ in the tuple for completeness. Two spherical triangles are called congruent if they have the same measurement. Attached to a tuple $(E,a,b,c)$ is its lcm, defined to be the least common multiple of the denominators of the entries in the tuple.

The displayed sets in §1.5, transcribed in their printed order, are

$$
\begin{aligned}
\Lambda_2 := \{&
(\tfrac12,\tfrac25,\tfrac12,\tfrac45)\pi,
(\tfrac14,\tfrac14,\tfrac12,\tfrac23)\pi,
(\tfrac12,\tfrac14,\tfrac23,\tfrac34)\pi,
(\tfrac54,\tfrac12,\tfrac23,\tfrac34)\pi,\\
&(1,\tfrac25,\tfrac23,\tfrac45)\pi,
(\tfrac32,\tfrac12,\tfrac23,\tfrac45)\pi,
(\tfrac12,\tfrac25,\tfrac12,\tfrac23)\pi\},\\[2mm]
\Lambda_1 := \{&
(1,\tfrac12,\tfrac23,\tfrac23)\pi\}
\cup \{(\tfrac md,\tfrac md,\tfrac12,\tfrac12)\pi\mid m,d\in\mathbb N\text{ and }0<\tfrac md\le\tfrac12\}\\
&\cup\{(\tfrac md,\tfrac12,\tfrac12,\tfrac md)\pi\mid m,d\in\mathbb N\text{ and }\tfrac12<\tfrac md<1\}.
\end{aligned}
$$

> Conjecture 1.6. The tuples in the set $\Lambda_1\cup\Lambda_2$ defined in 1.5 are the only measurements of proper rational spherical triangles. In particular, there are only finitely many measurements of proper rational spherical triangles with mutually distinct side lengths, namely, the seven measurements found by Little and Coxeter.

Section 2 gives the following definitions.

$$
\begin{aligned}
\Omega_1 &:= \{(E,a,b,c) \mid
\text{there is a rational spherical triangle with side lengths }
0<a\le b\le c<\pi,\ \text{and area }0<E<2\pi\}.\\
\Omega_2 &:= \{(E,a,b,c) \mid
\text{$(E,a,b,c)$ is a solution to L’Huilier’s Equation(1) in $G$}\\
&\hspace{35mm}\text{such that }0<a\le b\le c<\pi,\ \text{and }0<E<2\pi\}.
\end{aligned}
$$

Wang’s Equation (1) in §1.8 is

$$
\tan^2\!\left(\tfrac14 E\right)
=\tan\!\left[\tfrac14(-a+b+c)\right]\tan\!\left[\tfrac14(a-b+c)\right]
 \tan\!\left[\tfrac14(a+b-c)\right]\tan\!\left[\tfrac14(a+b+c)\right].
\tag{1, Wang}
$$

The printed proposition and proof read

> Proposition 2.2. Ω₁ = Ω₂.
>
> Proof. If (E, a, b, c) ∈ Ω₁, then (E, a, b, c) is a solution to L’Huilier’s Equation (1) by Theorem 1.2. So (E, a, b, c) ∈ Ω₂.
>
> Assume that (E, a, b, c) ∈ Ω₂. Then a + b > c, a + c > b, and b + c > a by Lemma 2.1. So there is a rational spherical triangle with side lengths a, b, c and area E by the converse of triangle inequality for spherical triangles. Thus (E, a, b, c) ∈ Ω₁. □

Lean uses rational coordinates measured in units of $\pi$. Thus the fractions $m/d$ in the two family clauses range directly over positive rationals. The conversion of units is explicit in `Omega2`. The statement `Conjecture16` expresses the biconditional for every rational quadruple. The final theorem, in module `WangMFinal`, is

```lean
theorem Wang.wang_conj_1_6_Omega2 : Wang.Conjecture16
```

It has no hypotheses. It is obtained from the merge theorem `Wang.wang_conj_1_6_Omega2_of_replay`, whose only hypothesis is the closed Boolean equality `global_filtered_replay`, and that equality is itself proved in `WangMFinal` by kernel evaluation of the generated certificates.

**From the Lean statement to Conjecture 1.6 as printed.** The map $q\mapsto q\pi$ is a bijection from $\mathbb Q$ onto $G$, so `Omega2` is exactly Wang's $\Omega_2$, with Wang's ranges $0<a\le b\le c<\pi$ and $0<E<2\pi$ and his Equation (1). `Lambda1` and `Lambda2` are his displayed sets, entry by entry, in printed order. Wang notes, just before Proposition 2.2, that $\Omega_1$ is the set of measurements of proper rational spherical triangles (Definition 1.4 sorts the sides, and properness is sides $<\pi$ and area $<2\pi$). Proposition 2.2 then gives $\Omega_1=\Omega_2$, and `Conjecture16` gives $\Omega_2=\Lambda_1\cup\Lambda_2$. Hence the set of measurements equals $\Lambda_1\cup\Lambda_2$, which is Conjecture 1.6 read as an equality; the inclusion that the conjecture asserts (every measurement lies in $\Lambda_1\cup\Lambda_2$) uses only the direction $\Omega_1\subseteq\Omega_2$, which is L'Huilier's theorem. The "in particular" clause follows because every element of $\Lambda_1$ has $a=b$ or $b=c$, while the seven elements of $\Lambda_2$ have mutually distinct sides. Lean's `Real.tan` is total and takes the value $0$ where the cosine vanishes. In the ranges of `Omega2` the only argument that can reach a pole is $(a+b+c)\pi/4$, at $a+b+c=2$. There the Lean right side is $0$ while the left side is positive, so no tuple is admitted, which agrees with Wang's reading that his equation has no solution there (proof of Lemma 2.1).

```lean
noncomputable def LHuilier (E a b c : ℝ) : Prop :=
  Real.tan (E / 4) ^ 2 =
    Real.tan ((-a + b + c) / 4) * Real.tan ((a - b + c) / 4) *
      Real.tan ((a + b - c) / 4) * Real.tan ((a + b + c) / 4)

/-- Wang's Ω₂ with all four measurements expressed in units of π. -/
def Omega2 (E a b c : ℚ) : Prop :=
  0 < a ∧ a ≤ b ∧ b ≤ c ∧ c < 1 ∧ 0 < E ∧ E < 2 ∧
    LHuilier ((E : ℝ) * Real.pi) ((a : ℝ) * Real.pi)
      ((b : ℝ) * Real.pi) ((c : ℝ) * Real.pi)

def Lambda1 (E a b c : ℚ) : Prop :=
  (E, a, b, c) = (1, 1 / 2, 2 / 3, 2 / 3) ∨
  (0 < E ∧ E ≤ 1 / 2 ∧ a = E ∧ b = 1 / 2 ∧ c = 1 / 2) ∨
  (1 / 2 < E ∧ E < 1 ∧ a = 1 / 2 ∧ b = 1 / 2 ∧ c = E)

def Lambda2 (E a b c : ℚ) : Prop :=
  (E, a, b, c) ∈
    [(1 / 2, 2 / 5, 1 / 2, 4 / 5), (1 / 4, 1 / 4, 1 / 2, 2 / 3),
     (1 / 2, 1 / 4, 2 / 3, 3 / 4), (5 / 4, 1 / 2, 2 / 3, 3 / 4),
     (1, 2 / 5, 2 / 3, 4 / 5), (3 / 2, 1 / 2, 2 / 3, 4 / 5),
     (1 / 2, 2 / 5, 1 / 2, 2 / 3)]

/-- The intended classification statement. -/
def Conjecture16 : Prop :=
  ∀ E a b c : ℚ, Omega2 E a b c ↔ Lambda1 E a b c ∨ Lambda2 E a b c
```

## 1. Trigonometric coordinates and the finite support

Apply Wang's Proposition 2.2 to pass from geometric measurements to Ω₂. The following coordinate change is Wang's Proposition 2.4. Write
$$
x_0=E/4,\qquad x_1=(a+b-c)/4,\quad x_2=(a-b+c)/4,\quad
x_3=(-a+b+c)/4,\quad s=x_1+x_2+x_3.
$$
For the proof the indices 1, 2, 3 may be permuted. The necessary and sufficient conditions in these coordinates are $x_i>0$, $s<\pi/2$, $0<x_0<\pi/2$, and
$$
\tan^2 x_0=\tan x_1\tan x_2\tan x_3\tan s. \tag{1}
$$
The inverse map with $x_1\le  x_2\le  x_3$ is $E=4x_0$, $a=2(x_1+x_2)$, $b=2(x_1+x_3)$, $c=2(x_2+x_3)$. This use of the geometric equivalence is important. The broader tangent conjecture in the same source does not impose the equality $s=x_1+x_2+x_3$.

Let $C=\cos x_1\cos x_2\cos x_3\cos s$ and $S=\sin x_1\sin x_2\sin x_3\sin s$. Equation (1) is equivalent in this range to $(C+S)\cos(2x_0)=C-S$. The identities used to expand it are
$$
\begin{aligned}
4(C+S)&=\cos(2s)+\cos(2x_1)+\cos(2x_2)+\cos(2x_3),\\
4(C-S)&=1+\cos(2x_1+2x_2)+\cos(2x_1+2x_3)+\cos(2x_2+2x_3).
\end{aligned}
$$
For verification, put $A=\cos(x_1+x_2)$, $B=\cos(x_1-x_2)$, $D=\cos(s+x_3)$. Product-to-sum gives $4C=(A+B)(D+A)$ and $4S=(B-A)(A-D)$. Their difference gives $4(C-S)=2(A^2+BD)$. A second product-to-sum gives the displayed identities.

For $y_j=e^{2ix_j}$ and $z=e^{2ix_0}$ the resulting Laurent polynomial equation is
$$
(z+z^{-1})\left(y_1y_2y_3+(y_1y_2y_3)^{-1}
+\sum_{j=1}^3(y_j+y_j^{-1})\right)
-4-2\sum_{1\le  i<j\le 3}(y_i y_j+(y_i y_j)^{-1})=0. \tag{2}
$$
Let $\mathcal R\subset\mathbb Z^4$ be its 23 exponent rows in the order $(x_1,x_2,x_3,x_0)$. Thus there are 16 rows of coefficient $+1$, six rows of coefficient $-2$, and the zero row of coefficient $-4$. The support and each coefficient are invariant under negating the rows.

## 2. Any affine line through the proper region gives the known family

Suppose (2) holds on a nonconstant real affine line through a point satisfying the proper ranges above. If all three side coordinates are constant then (1) and strict monotonicity of tangent on $(0,\pi/2)$ force $x_0$ to be constant as well. The projection to the side coordinates thus meets their open simplex in a bounded open segment.

Put $L=\pi/2$ and $b_1=x_1,b_2=x_2,b_3=x_3,b_4=L-s$. Then $\sum b_i=L$, all $b_i$ are positive on the open segment, and the right side of (1) is
$$
\frac{\tan b_1\tan b_2\tan b_3}{\tan b_4}.
$$
The coordinate $x_0$, which starts in $(0,L)$, stays in this interval while the side coordinates stay inside their simplex. Indeed, approaching $0$ or $L$ from inside would make the left side tend to zero or infinity while the right side stays finite and positive.

At either endpoint of the simplex segment, some $b_i$ vanish. There cannot be exactly one. If exactly one vanishes, the other three tend to values in $(0,L)$, so the right side has a simple zero or pole. In contrast the left side has order zero, two, or minus two, according to the endpoint value of the affine function $x_0$. The affine slope of any vanishing $b_i$ is nonzero, so these orders are literal. Each endpoint therefore has at least two vanishing coordinates. No barycentric coordinate vanishes at both endpoints, since that would make it zero throughout the segment. There are four coordinates, so the two endpoints have exactly two distinct vanishing coordinates each.

Up to permuting the first three coordinates and reversing the segment parameter, there are positive numbers $a,b,c,d$ with $a+b=c+d=L$ for which
$$
(b_1,b_2,b_3,b_4)=(at,bt,c(1-t),d(1-t)),\qquad 0<t<1.
$$
At $t=0$ the quotient has a double zero, so $x_0(0)=0$. At $t=1$ it has a finite positive limit, so $x_0(t)=et$ with $0<e<L$. The limit at $t=1$ gives $\tan^2 e=c/d$ because $\tan a\tan b=1$. Divide the identity by $t^2$ and take the logarithmic right derivative at $0$. The logarithmic derivatives of $\tan^2(et)/t^2$, $\tan(at)/t$, and $\tan(bt)/t$ vanish, by $\tan h=h+O(h^3)$. The remaining derivative is
$$
-\frac{2c}{\sin(2c)}+\frac{2d}{\sin(2d)}
=\frac{2(d-c)}{\sin(2c)}.
$$
It follows that $c=d=\pi/4$, and then $e=\pi/4$. The limit of the identity divided by $t^2$ at $0$ gives $e^2=ab$, since $\tan c/\tan d=1$. With $a+b=2e$ this implies $a=b=e$.

Thus through any such point two of $x_1,x_2,x_3$ equal $x_0$, and the remaining coordinate plus $x_0$ equals $\pi/4$. Equivalently the measurement, after sorting its sides, is $(4x_0;4x_0,\pi/2,\pi/2)$ with $0<4x_0<\pi$. Conversely every such tuple solves (1), since the other two tangent factors are complementary. This proves the affine-family assertion.

One consequence used below is a rank test. If the terms of (2) can be partitioned into vanishing subsums, consider the integral differences $r-r'$ of exponent rows in the same part. If their real span has dimension less than four, choose a nonzero real vector $w$ orthogonal to all those differences. On the line through $x$ in the direction $w$, each subsum is multiplied by a single phase $e^{2it(r\cdot w)}$. It remains zero. Thus at a nonfamily point these differences must span dimension four for every such partition.

## 3. Eliminate large primes from the conductor

Assume the coordinates $x_j/\pi$ are rational. Let $N$ be their least common denominator. For $p^k\Vert N$, decompose the four phases into $p^k$-part and prime-to-$p$ part. Write the former as powers with exponent tuple $v\pmod{p^k}$ of a primitive $p^k$-th root. At least one coordinate of $v$ is a unit. If $k\ge2$, put $q=p^{k-1}$. Group a term belonging to row $r$ by $r\cdot v\bmod q$. Each group vanishes separately: after taking out its common power of the primitive $p^k$-th root, its remaining phases belong to the field of conductor $N/q$, and the $q$ powers with exponents $0,\ldots,q-1$ are independent over this subfield by the cyclotomic degree ratio. In particular groups modulo $p$ also vanish. For $k=1$, the residues modulo $p$ have coefficients $A_j$ in the prime-to-$p$ field, and (2) is equivalent to all $A_j$ being equal, by the minimal polynomial $1+X+\cdots+X^{p-1}$ over that field.

For a partition into zero groups, the necessary polygon inequality in every nonempty group is
$$
2\max |c_r|\le\sum |c_r|.
\tag{3}
$$
Outside the known family it must also satisfy the rank test of §2. The full-rank determinant of four within-group differences is divisible by $p$ when the groups are modulo $p$, since their rows annihilate the nonzero $v\bmod p$. Primitive differences can replace the raw differences for this test at odd primes, since each raw difference has content 1 or 2.

The 64 primitive directions obtained from pairs of support rows, identifying a direction with its negative, have the following absolute $4\times4$ determinants:
$$
0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,22,24,26,28,30,32,34.
$$
This is a small exact computation. Form all pair differences, divide each by the gcd of its entries, retain one sign, and take the determinant of every four distinct directions by expanding in the last row. The independent implementation in `scripts/my_conductor_bound.py` computes the same spectrum with rational elimination and integer determinants. Hence outside the family only $11,13,17$ can be primes at least 11 in a zero-group case. For these three primes the following finite tests rule out that case.

All projective directions $\bmod p$ are represented uniquely by taking their first nonzero coordinate to be 1. Directly grouping the 23 rows, testing (3), and row-reducing the within-group differences gives:

| $p$ | Directions satisfying (3) | Also of rank four |
|---:|---:|---:|
| 11 | 235 | 0 |
| 13 | 279 | 0 |
| 17 | 367 | 0 |

It remains to exclude $A_0=\cdots=A_{p-1}\ne0$ when $k=1$. For $p>23$ a residue is empty. For $17\le p\le23$, if no residue is empty there are at least $2p-23\ge11$ singleton residues and hence at least one singleton of coefficient $+1$. The common coefficient is then an algebraic unit. Every bucket must contain a unit-weight term, since otherwise its value lies in $2$ times the ring of algebraic integers and cannot be a unit. But there are only 16 unit-weight terms.

For $p=11,13$ use the same projective directions. If every residue occurs, test that their polygon-inequality intervals for the magnitude of the common coefficient intersect. These intervals are $[\max(0,2\max |c_r|-\sum |c_r|),\sum |c_r|]$. For directions with no singleton, none pass. For a singleton the required magnitude is its weight. Two singleton weights must agree. In addition, when that magnitude is 1 every bucket must contain a weight-1 term. When it is 2 or 4 no bucket can contain exactly one weight-1 term, by reduction modulo 2. To justify the latter, the common coefficient is $2$ or $4$ times a root of unity, whereas a root of unity is a unit modulo any prime above 2.

After these tests 72 directions survive for 11 and 24 for 13. In every survivor the singleton weight is 2, the central bucket consists of the rows $0,h,-h$ with weights $4,2,2$, and some other bucket consists of two weight-1 rows whose difference is $h$ or $-h$. This assertion is verified by iterating exactly the projective tuples and comparing row lists in `scripts/my_conductor_bound.py`. For these patterns the central coefficient is the real number $-4-2\eta^h-2\eta^{-h}\le 0$, where $\eta$ is the tuple of prime-to-$p$ phases. Its magnitude 2 forces the common coefficient to be $-2$. The two unit-weight phases in the indicated bucket must then both be $-1$. This forces $\eta^h=1$, which makes the central coefficient $-8$, a contradiction. Therefore the conductor of every nonfamily point has prime factors among $2,3,5,7$.

## 4. Bound the powers and evaluate all remaining torsion orbits

For a given prime and $k\ge2$, test the zero partition modulo $q=p^{k-1}$ from §3. Normalize $v$ by multiplying by a unit so that its first unit coordinate is 1. Starting modulo $p$, any surviving tuple can be lifted to the next modulus by the $p^3$ choices of a new digit in the other three coordinates. A failed rank or polygon test cannot become a pass when the partition is refined. In the rank test all within-class differences upstairs already belonged to the coarser classes. For the polygon test, a large term in a finer class has no more competing mass than in its coarser class.

Exact counts of lifts surviving both tests are:

| Prime | $q=p$ | $q=p^2$ | $q=p^3$ | $q=p^4$ | $q=p^5$ |
|---:|---:|---:|---:|---:|---:|
| 2 | 15 | 104 | 50 | 48 | 0 |
| 3 | 27 | 0 | — | — | — |
| 5 | 42 | 0 | — | — | — |
| 7 | 24 | 0 | — | — | — |

The independent program `scripts/my_conductor_bound.py` also checks the terminating moduli by direct enumeration. In particular
$N\mid 2^5 3^2 5^2 7^2=352800$.
For each prime the final test enumerates the trivial component, every normalized nonzero direction modulo $p$, and every normalized lift modulo $p^k$ of its surviving modulo $p^{k-1}$ directions. This enumerates all possibilities needed for nonfamily points. It can omit some points already covered by §2.

Here is the exact zero test used for the product of the four candidate lists. Represent an expression by the two signed subsets of its original 23 terms. When processing a prime power $p^k=pq$, within each fixed residue $r\bmod q$, partition the terms by exponent $r+jq\bmod pq$, $j=0,\ldots,p-1$. The group is zero over the remaining prime fields if and only if the $p$ coefficients within it are equal. The field-degree facts are the same as in §3, applied first to the independent $q$ powers and then to the single relation in $p$ powers. Thus replace that group by the $p-1$ signed differences from any one reference coefficient. Terms from distinct buckets are disjoint before subtraction, so every new equation still uses a signed subset of the original rows, even if the same original row occurs in other equations. Drop a branch whenever any new equation violates (3). This is a necessary test and costs no possible zero. At the end all remaining phases are 1. The condition is exactly equality of the total positive and negative weights in every retained equation.

Normalized local vectors describe Galois orbits: the four normalizing multipliers can be chosen independently by the Chinese remainder theorem. For each exact surviving local tuple, of total order $N=\prod p^k$, combine coordinate exponents by
$$
v_{\mathrm{global}}=\sum_{p^k\Vert N}(N/p^k)v_{p^k}\pmod N.
$$
Try all common multipliers $a\in (\mathbb Z/N\mathbb Z)^\times$. With residues lying in $0,\ldots,N-1$, retain the conjugate precisely when its first three residues are positive with sum $<N/2$ and its last residue is positive and $<N/2$. This is exactly the proper coordinate domain. Sort the first three coordinates, and remove the family of §2.

The entire search is in `scripts/spherical_torsion.js`. It uses just integer operations on vectors, 23-bit masks, signs and residues. In the order 7, 5, 3, 2 it visits 394, 2,315, 27,984 and 2,522,928 nodes surviving the conflict test after the successive primes, and 427,586 terminal orbits meet the exact Laurent equation, most outside the proper region. It retains exactly these eight sporadic normalized tangent tuples $(N;r,u,v,w)$, with $(x_0,x_1,x_2,x_3)/\pi=(r,u,v,w)/N$:

| $N$ | $r$ | $u$ | $v$ | $w$ | $(E/\pi,a/\pi,b/\pi,c/\pi)$ |
|---:|---:|---:|---:|---:|---|
| 24 | 3 | 1 | 2 | 7 | $(1/2,1/4,2/3,3/4)$ |
| 24 | 6 | 3 | 3 | 5 | $(1,1/2,2/3,2/3)$ |
| 40 | 5 | 1 | 7 | 9 | $(1/2,2/5,1/2,4/5)$ |
| 48 | 3 | 1 | 5 | 11 | $(1/4,1/4,1/2,2/3)$ |
| 48 | 15 | 5 | 7 | 11 | $(5/4,1/2,2/3,3/4)$ |
| 60 | 15 | 4 | 8 | 16 | $(1,2/5,2/3,4/5)$ |
| 120 | 15 | 7 | 17 | 23 | $(1/2,2/5,1/2,2/3)$ |
| 120 | 45 | 11 | 19 | 29 | $(3/2,1/2,2/3,4/5)$ |

Each tuple obeys the inequalities in §1 and the exact equation. Consequently the inverse geometric equivalence proves existence as well as exhaustiveness. Every exhaustive test in this argument uses exact integer or rational arithmetic.

### Faster exact replay using a characteristic-two constraint

For an optional filter, the first parenthesis in (2) factors as
$$
(y_1y_2y_3)^{-1}(1+y_1y_2)(1+y_1y_3)(1+y_2y_3).
$$
Reduce (2) modulo any prime above 2 in the cyclotomic integers. The coefficients on the right vanish, so either $1+z^2$ or one of the three factors $1+y_i y_j$ vanishes there. A root of unity reduces to 1 in characteristic two exactly when its order is a power of 2. Indeed the 2-primary part reduces to 1 by the Frobenius identity. For an odd-order root not equal to 1, an alleged reduction to 1 contradicts the geometric sum identity after reduction, since its odd order reduces to 1. Thus at least one of $z,y_1y_2,y_1y_3,y_2y_3$ has trivial odd part. In the proper region each of those four roots has argument strictly between 0 and $\pi$, so the relevant 2-primary order is at least 4.

The option `--mod-two --terminal-cache` uses this exact filter. Its independent final-axis check compares the signed weights in the two buckets of each block directly and caches the list of passing directions per residual expression. It needed 4,439 cached expressions, and reproduced the same 1,300 proper conjugates and eight sporadic tuples. The option `--alternate` repeats the full unfiltered proof using a different prime order and fixed last-bucket references, also obtaining the same answer. The separate tangent-polynomial check verifies the eight tuples by division by $\Phi_N$.


## Significance, relationship to earlier work, and provenance

Wang’s argument proves cases with restricted denominators and explains the obstacle posed by mixed denominators in Remark 1.10. The conductor bound here applies to mixed denominators after the affine-line classification removes the family. The affine-line lemma is the structural step specific to this proof. The rest uses the established strategy of vanishing sums of roots of unity and exhaustive torsion search. Dvornicich, Lombardo, Veneziano and Zannier wrote in §0.5 of arXiv:2404.02559 (Math. Ann. 2025) that they planned to apply their strategy to other trigonometric-diophantine equations and that “the main conjecture of [Wan23] should be amenable to our methods.” Wang's abstract introduces a single conjecture, on a trigonometric Diophantine equation (his Conjecture 3.2, on the generalized L'Huilier equation), and presents the classification of triangles as its implication (Proposition 3.6), so their remark most likely refers to Conjecture 3.2. That conjecture is not proved here. The method used here is the one their remark anticipates, and the credit for pointing to it is theirs. The enumeration makes this proof computer-assisted.

The independent literature review found no prior classification in the sources it examined. Conway and Jones, Mann, Poonen and Rubinstein, and Myerson supply general tools for vanishing sums or trigonometric relations. Kedlaya, Kolpakov, Poonen and Rubinstein classify configurations with rational angles, including tetrahedra. Their paper gives a general torsion-point algorithm but does not apply it to Wang’s side-and-area equation. The study of spherical quadrilaterals by Liang, Liao and Wang has a different scope. The journal version of *Rational Spherical Triangles* appeared in *International Journal of Number Theory* 21(05) (2025), 1051–1073, DOI 10.1142/S179304212550054X. Its abstract describes partial results. The journal text was not read: the publisher refuses automated access. It is 23 pages against 54 on arXiv, so its numbering may differ, and this paper cites the arXiv numbering throughout. This manuscript uses arXiv:2312.01633v1.

GPT-6.2 Sol lanes found and wrote the proof, wrote the Lean formalization and wrote this paper. Claude Opus 5.5 lanes did the adversarial review before formalization (with the independent replays in `scripts/my_conductor_bound.py` and `scripts/my_torsion_search_cached.js`) and the final check of definitions, paper and prior art. All these contributions are AI-generated. No human has checked the proof, the formalization or this paper.

## Exact computation

The companion programs are included with this manuscript. `scripts/my_conductor_bound.py` checks the determinant spectrum, the large-prime patterns, and the prime-power exclusions using exact arithmetic. `scripts/spherical_torsion.js` checks the torsion search and accepts `--mod-two --terminal-cache` for the faster equivalent calculation. The unfiltered run gives the counts stated in §4. The formal replay uses the 7, 5, 3, 2 axis order with fixed last-column references.
Each raw chart is partitioned into batches with a checked concatenation. A rejected axis
has an overweight coefficient difference, while each retained axis carries a checked table
of column masks. An odd-primary frontier verifies the explicit successor list of each
batch. On the final axis each residual equation is coded as a signed linear combination
of column differences. Bounded lanes in a common integer allow the kernel to check the
necessary zero test for thousands of options using binary arithmetic. The checked
cache and parity masks bound the survivors of every frontier. The generation run gives
38,247 odd-primary survivors and 4,706 normalized leaves for the orbit verifier.
These counts describe the generated search. The Lean coverage proof does not depend on them. See the status note under the abstract for the full kernel build.
`REPORT.md` records the replay status, including the verified mixed-primary pilot.

## References

- Haiyang Wang, *Rational Spherical Triangles*, arXiv:2312.01633v1. [Preprint](https://arxiv.org/abs/2312.01633)
- Roberto Dvornicich, Davide Lombardo, Francesco Veneziano and Umberto Zannier, arXiv:2404.02559, §0.5. [Preprint](https://arxiv.org/abs/2404.02559)
- Kiran S. Kedlaya, Alexander Kolpakov, Bjorn Poonen and Michael Rubinstein, arXiv:2011.14232, §7. [Preprint](https://arxiv.org/abs/2011.14232)
- Liang, Liao and Wang, arXiv:2512.19071. [Preprint](https://arxiv.org/abs/2512.19071)
