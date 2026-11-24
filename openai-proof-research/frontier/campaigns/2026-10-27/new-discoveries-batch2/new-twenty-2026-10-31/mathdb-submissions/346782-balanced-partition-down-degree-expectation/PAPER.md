# The weighted down-degree expectation of a balanced partition

**Abstract.** We prove Conjecture A.2 of Kim, Schlosser and Yoo for balanced partitions of every slope. A corner sum telescopes on each diagram in the lower interval. Balance gives zero weight to additions outside the interval. Pairing the remaining additions and removals gives a polynomial identity, which lifts to the two-parameter expectation over $\mathbb Q(\mathsf a,q)$.

## Statement

The conjecture is Kim, Schlosser and Yoo [1, Appendix A, (A.3)]. The following is the MathDB statement verbatim. Its equations reproduce the source formulas (A.1a), (A.1b), Definition A.1 and (A.2). The last sentence records the status in the source. [MathDB 346782](https://mathdb.com/p/346782)

Let $\mathsf a$ and $q$ be indeterminates. For a balanced partition $\lambda$, write $w=\lambda_1$ for its width, $\ell=\ell(\lambda)$ for its length, and $d=\gcd(w,\ell)$. Define

$$
W_{\mathsf a;q}(n)=\frac{1-\mathsf a q^{1+2n}}{1-\mathsf a q}q^{-n},\qquad [n]_{\mathsf a;q}=\frac{(1-q^n)(1-\mathsf a q^n)}{(1-q)(1-\mathsf a q)}q^{1-n}.
$$

For $x,y\in[\emptyset,\lambda]$ with $y\lessdot x$, if $y$ is obtained by deleting a cell in row $s$, set

$$
\operatorname{wt}(x,y)=W_{\mathsf a q^{\frac{w+\ell}{d}};q}\left(\frac{w(s-1)+\ell(|x|-1)}{d}\right).
$$

Define

$$
\operatorname{ddeg}_{\mathsf a;q}(x)=\sum_{y\lessdot x}\operatorname{wt}(x,y),
$$

with the sum over $y\in[\emptyset,\lambda]$, and

$$
R(\lambda\mid\mathsf a;q)=\sum_{x\in[\emptyset,\lambda]}W_{\mathsf a q^{\frac{w\ell}{d}};q}\left(\frac{\ell|x|}{d}\right),
$$

so that

$$
\mathbb E_{\mathsf a;q}(X)=\frac{\sum_{x\in[\emptyset,\lambda]}\operatorname{ddeg}_{\mathsf a;q}(x)}{R(\lambda\mid\mathsf a;q)}.
$$

**Balanced-partition product conjecture.** If $\lambda$ is balanced, then

$$
\mathbb E_{\mathsf a;q}(X)=\frac{\left[\frac{w\ell}{d}\right]_{\mathsf a q^{\frac{w+\ell}{d}};q}}{\left[\frac{w+\ell}{d}\right]_{\mathsf a q^{\frac{w\ell}{d}};q}}.
$$

This is an $\mathsf a;q$-analogue of the down-degree expectation formula. The source presents it as a conjecture for balanced partitions of arbitrary slope; no resolution is supplied.

Definition A.1 specifies the down-degree sum as follows. “Define $\operatorname{ddeg}_{\mathsf a;q}(x)$ to be the sum of the weights $\operatorname{wt}(x,y)$ for all $y\in[\emptyset,\lambda]$ satisfying $y\lessdot x$.” Its individual weight and normalization formulas are the two displays for $\operatorname{wt}(x,y)$ and $R(\lambda\mid\mathsf a;q)$ above.

Conjecture A.2 states that (A.3) holds for a balanced partition “of any slope.” We use the balance convention in the journal version of [1, §1]. The arXiv version phrases the same condition as “the left cell of every inner corner of $\mu$ lies on the line”; the journal text names the point that must lie on the line, the upper left corner of each addable cell. An addable cell is one whose addition leaves a Young diagram. A removable cell is one whose deletion leaves a Young diagram. For a balanced shape, the upper left corner of every addable cell lies on the line from the top right of the first row to the bottom left of the first column. Measure horizontal distance leftward from the right edge and vertical distance downward from the top. At a drop $\lambda_s>\lambda_{s+1}$, the addable cell in row $s+1$ has upper left corner $(w-\lambda_{s+1},s)$. The addable cells at the upper and lower ends give the diagonal endpoints $(0,0)$ and $(w,\ell)$. Thus balance requires
$$
\ell(w-\lambda_{s+1})=ws
\qquad (1\le s<\ell,\ \lambda_s>\lambda_{s+1}).
$$

The Lean transcription of the source definitions uses zero-based row indices, so `i.val` is $s-1$. The field `K` is `FractionRing (MvPolynomial (Fin 2) ℚ)`, and `a` and `q` are the images of the two indeterminates. The definitions `height`, `perimeter` and `area` give $\ell$, $(w+\ell)/d$ and $w\ell/d$.

```lean
def Waq (b t : K) (n : ℕ) : K :=
  (1 - b * t ^ (1 + 2 * n)) / (1 - b * t) * t ^ (-(n : ℤ))

def aqInt (b t : K) (n : ℕ) : K :=
  (1 - t ^ n) * (1 - b * t ^ n) / ((1 - t) * (1 - b * t)) * t ^ (1 - (n : ℤ))

/-- The weight of the cover marked by row i+1, with i zero-based. -/
def wt {lam : List ℕ} (x : Rows lam) (i : Fin (height lam)) : K :=
  Waq (a * q ^ perimeter lam) q
    ((width lam * i.val + height lam * (size x - 1)) / gcd lam)

def ddeg {lam : List ℕ} (x : Rows lam) : K :=
  ∑ i ∈ removals x, wt x i

def R (lam : List ℕ) : K :=
  ∑ x ∈ interval lam, Waq (a * q ^ area lam) q (height lam * size x / gcd lam)

def Eaq (lam : List ℕ) : K :=
  (∑ x ∈ interval lam, ddeg x) / R lam
```

The Lean lemmas `mem_interval_iff_antitone` and `interval_represents_rows` identify the enumerated rows with the weakly decreasing row vectors bounded by $\lambda$. Padding with zero rows gives the lower interval, including its empty diagram. The lemma `balanced_iff_diagonal` gives the coordinate balance equation above. The lemmas `covers_iff_removal` and `ddeg_eq_sum_covers` identify the removable-row sum with the sum over all lower covers $y\lessdot x$, counting each cover once.

## Proof

Put $u=w/d$, $v=\ell/d$, $A=vw=u\ell=w\ell/d$ and $B=u+v=(w+\ell)/d$. Because $d$ divides both $w$ and $\ell$, the source's exponents are $u(s-1)+v(|x|-1)$ on covers and $v|x|$ on diagrams. In a subpartition $x\subseteq\lambda$, keep $\ell$ rows by padding with zeros. Define two polynomials in $t$ by
$$
T(t)=\sum_{x\subseteq\lambda}t^{v|x|},\qquad
S(t)=\sum_{x\subseteq\lambda}\ \sum_{s\ {\rm removable\ in}\ x}
  t^{u(s-1)+v(|x|-1)}.
$$
We prove
$$
(1-t^B)S(t)=(1-t^A)T(t). \tag{1}
$$

For a fixed $x$, let $h_s=w-x_s$ for $1\le s\le\ell$, with $h_0=0$ and $h_{\ell+1}=w$. Define $F(h,s)=t^{us}-t^{vh}$. Then
$$
\sum_{s=0}^{\ell}\bigl(F(h_{s+1},s)-F(h_s,s)\bigr)
=\sum_{s=0}^{\ell}(t^{vh_s}-t^{vh_{s+1}})=1-t^A. \tag{2}
$$
At a seam with $h_s=h_{s+1}$ the contributions cancel. At a strict seam $s\ge1$, the term $-F(h_s,s)$ corresponds to removing the last cell in row $s$. The negative contribution at $s=0$ vanishes since $F(0,0)=0$.

At a strict seam $s<\ell$, the term $F(h_{s+1},s)$ corresponds to adding a cell to row $s+1$ in the bounding rectangle. This includes $s=0$, where strictness says $x_1<w$. The addition lies outside $\lambda$ precisely if $x_{s+1}=\lambda_{s+1}$. At $s=0$ this is impossible because $\lambda_1=w$. At a strict interior seam it implies $\lambda_s\ge x_s>x_{s+1}=\lambda_{s+1}$. Balance gives $us=v(w-\lambda_{s+1})=vh_{s+1}$, so the term is zero. The final positive term is also zero, since $F(w,\ell)=0$ by $u\ell=vw$. The positive terms that remain therefore correspond to additions inside $\lambda$.

Multiply (2) by $t^{v|x|}$ and sum over $x\subseteq\lambda$. Every addition pairs with its reverse removal. For a cover $y\lessdot x$ whose cell lies in row $s$ and column $c=x_s$, the paired term is
$$
t^{v|y|}F(w-c+1,s-1)-t^{v|x|}F(w-c,s)
=t^{u(s-1)+v(|x|-1)}(1-t^B).
$$
The terms involving the first argument of $F$ cancel because $|x|=|y|+1$. The remaining two monomials differ in exponent by $u+v$. Summing over covers gives (1).

For the two-parameter lift, work in $\mathbb Q(\mathsf a,q)$ and abbreviate $S_\pm=S(q^{\pm1})$ and $T_\pm=T(q^{\pm1})$. The source weight satisfies
$$
W_{\mathsf a q^j;q}(n)
=\frac{q^{-n}-\mathsf a q^{j+1}q^n}{1-\mathsf a q^{j+1}} .
$$
Let $D_j=1-\mathsf a q^{j+1}$, $N_0=S_- -\mathsf a q^{B+1}S_+$ and $R_0=T_- -\mathsf a q^{A+1}T_+$. The numerator of the expectation is $N_0/D_B$, and its denominator is $R=R_0/D_A$. Applying (1) at $t=q$ gives $(1-q^B)S_+=(1-q^A)T_+$. Applying it at $t=q^{-1}$ and multiplying by $-q^{A+B}$ gives
$$
q^A(1-q^B)S_-=q^B(1-q^A)T_-.
$$
Subtract $\mathsf a q^{A+B+1}$ times the first equality from the second to obtain
$$
q^A(1-q^B)N_0=q^B(1-q^A)R_0. \tag{3}
$$
For nonnegative $j,n$, the source's $\mathsf a;q$-integer formula gives
$$
[n]_{\mathsf a q^j;q}
=\frac{(1-q^n)(1-\mathsf a q^{j+n})q}{(1-q)D_j q^n}.
$$

All factors needed for division are nonzero. We have $A,B>0$ since $w,\ell>0$, and $q$, $1-q$, $1-q^A$, $1-q^B$, $D_A$, $D_B$ and $1-\mathsf a q^{A+B}$ are nonzero polynomials in independent indeterminates. For $R_0$, choose $M$ at least $v|x|$ for every $x\subseteq\lambda$. Then $q^M R_0$ is a polynomial. Evaluating it at $\mathsf a=0,\ q=1$ gives the number of subpartitions, which is positive because the empty diagram belongs to the interval. Hence $R_0$ and $R$ are nonzero. The ratio of the two $\mathsf a;q$-integers now gives
$$
\frac{[A]_{\mathsf a q^B;q}}{[B]_{\mathsf a q^A;q}}
=\frac{D_A}{D_B}\,\frac{q^B(1-q^A)}{q^A(1-q^B)}
=\frac{D_A}{D_B}\frac{N_0}{R_0}
=\mathbb E_{\mathsf a;q}(X),
$$
where the second equality uses (3). This proves (A.3). $\square$

## Relation to earlier work

Chan, Haddadan, Hopkins and Moci [3, Corollary 3.8] prove the ordinary balanced-shape down-degree result using rooks. Kim, Schlosser and Yoo state the two-parameter formula as Conjecture A.2 and verify special cases in Appendix A. Hopkins, Lazar and Linusson [2, Remark 6.6] discuss that conjecture alongside their $q$-enumeration results and say that its connection to their work was unclear. Kim, Schlosser and Yoo also note the unclear connection in the journal version [1, Remark A.6]. Remark 6.7 of [2] concerns the $q$-toggle expansion of the ordinary down-degree. The statistic here assigns specific monomials to the removable rows before the two-parameter lift.

The proof establishes the stated rational-function identity for every balanced shape. Equation (1) explains why the weighted answer depends only on the two bounding dimensions. The same argument accounts for boundary additions and for all interior additions blocked by the particular shape.

## Lean certificate

The theorem is `BalancedPartition.ksy_conjA2`. The [source appendix](LEAN-SOURCE-APPENDIX.md) gives all three modules in import order.

## References

1. Jang Soo Kim, Michael J. Schlosser and Meesue Yoo, “Enumeration of standard barely set-valued tableaux of shifted shapes,” *European Journal of Combinatorics* **112** (2023), 103727. [Journal](https://doi.org/10.1016/j.ejc.2023.103727) · [arXiv:2006.03253v2](https://arxiv.org/abs/2006.03253v2)
2. Sam Hopkins, Alexander Lazar and Svante Linusson, “On the $q$-enumeration of barely set-valued tableaux and plane partitions,” *European Journal of Combinatorics* **113** (2023), 103760. [Journal](https://doi.org/10.1016/j.ejc.2023.103760) · [arXiv:2106.07418v2](https://arxiv.org/abs/2106.07418v2)
3. Melody Chan, Shahrzad Haddadan, Sam Hopkins and Luca Moci, “The expected jaggedness of order ideals,” *Forum of Mathematics, Sigma* **5** (2017). [Journal](https://doi.org/10.1017/fms.2017.5) · [arXiv:1507.00249](https://arxiv.org/abs/1507.00249)
