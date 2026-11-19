# Counterexamples to the Ilinca–Kahn rectangular matching bound

## Abstract

Ilinca and Kahn's Conjecture 3.1 upper-bounds the number of matchings saturating the smaller part of a bipartite graph by an expression in its left degrees. For each integer $m\ge 3$, the graph $K_{m,m+1}\sqcup K_{1,1}$ violates the bound. Its matching count is $(m+1)!$. We use tangents to the convex function $\ln\Gamma$ for $m\ge4$ and a shifted secant with an exact integer comparison for $m=3$. Exact upper estimates show that $m=1,2$ satisfy the inequality within this family. Lean 4 and Mathlib certify the matching count, the violation for all $m\ge3$, and the negation of the source conjecture.

## 1. The conjecture

Conjecture 3.1, equation (20) on printed page 9 of Liviu Ilinca and Jeff Kahn's *Asymptotics of the Upper Matching Conjecture* [1], reads

> **Conjecture 3.1.** Let $G$ be bipartite on $X\cup Y$ with $|X|=\ell$ and $|Y|=M\ge\ell$, and for $x\in X$, let $t_x=\ell d_x/M$. Then
> $$
> \log\Phi_\ell(G)\le \sum_{x\in X}\psi(d_x,t_x).
> \tag{20}
> $$

The standing convention in §1 is that $G$ has no isolated vertices. This applies to both parts. Here $d_x=|N_G(x)|$ is the degree of $x$, $\mathcal M_\ell(G)$ is the set of size-$\ell$ matchings, and $\Phi_\ell(G)=|\mathcal M_\ell(G)|$. The source uses base-two logarithms throughout. Its definition for integer $d\ge t>0$ is
$$
\psi(d,t)=t^{-1}\big[\log d!-\log\Gamma(d-t+1)\big],
$$
where $\Gamma$ is the usual gamma function. The graph is simple, as in the equivalent rectangular zero–one matrix formulation given in §3. For a nonempty admissible graph, $0<\ell\le M$ and $d_x>0$ give $0<t_x\le d_x$, hence $d_x-t_x+1\ge1$. A graph with no size-$\ell$ matching satisfies (20) under the extended-real convention $\log 0=-\infty$. In the empty graph the count is one and the sum is empty. Multiplying (20) by $\ln 2>0$ changes the logarithms to natural logarithms and preserves the comparison. Below $\ln$ always denotes the natural logarithm.

For integer $t$, the Gamma recurrence gives $d!/\Gamma(d-t+1)=d(d-1)\cdots(d-t+1)$. In the square case $M=\ell$, $t_x=d_x$ and (20) is Brégman's theorem [2]. Ilinca and Kahn identify equality for unions of complete bipartite blocks with a common part ratio $\ell/M$. In a block of size $p\times q$ with that ratio, $d_x=q,\ t_x=p$, and the $p$ equal row terms sum to the logarithm of the falling factorial $q(q-1)\cdots(q-p+1)$, the block's injection count. The authors report a proof in the constant-left-degree case when every right degree equals $t=\ell d/M$. Their special case with all $d_x=d$ and integral $t$, allowing unequal right degrees, remains open in the scope of this work and the literature checked. The counterexamples below have two distinct left degrees and fractional $t_x$. The regular Upper Matching Conjecture (Conjecture 1.1 of [1], studied in [3–5]) concerns a different bound.

## 2. The family and its gap

**Theorem.** For each integer $m\ge1$, let $G_m=K_{m,m+1}\sqcup K_{1,1}$, with the $m$-vertex side of the first component and one endpoint of the other component in $X$. Then $|X|=m+1,\ |Y|=m+2$, both parts have positive degrees, and $\Phi_{m+1}(G_m)=(m+1)!$. With $t_x=(m+1)d_x/(m+2)$, the strict inequality
$$
\log_2\Phi_{m+1}(G_m)>\sum_{x\in X}
  \frac{\log_2(d_x!)-\log_2\Gamma(d_x-t_x+1)}{t_x}
$$
holds for every $m\ge3$. For $m=1,2$ the inequality is strictly reversed. Thus $K_{3,4}\sqcup K_{1,1}$ is the first violating member of this family.

Label the vertices of the edge component $x_0,y_0$, with $x_0\in X$. A matching of size $|X|$ uses distinct vertices of $X$ and therefore uses each of them exactly once. Its edges determine an injective function $X\to Y$ taking each row to a neighbour. Conversely, such a function determines a matching of size $|X|$, since its values are distinct. In $G_m$, the edge $x_0y_0$ is forced and all remaining choices use the first component. In a fixed order of its $m$ rows, the successive numbers of available columns are $m+1,m,\ldots,2$, so the count is $(m+1)!$. Every vertex of the first component has a neighbour because $m\ge1$, and the forced edge gives a neighbour to each of its endpoints.

Write $d=m+1,\ q=m+2,\ \delta=1/q$ and $F(u)=\ln\Gamma(u)$ for $u>0$. For a row in the large block, the degree is $d$ and $t_x=d^2/q=m+\delta$, by $d^2=mq+1$. Its Gamma argument is $2-\delta$. For the forced row, the degree is one and $t_x=d/q=1-\delta$, so its Gamma argument is $1+\delta$. In particular both $t_x$ and both Gamma arguments are positive. Let $D_m$ denote the left side of (20) minus the right side in natural logarithms. With $L=\ln(d!)$, substitution gives
$$
\begin{aligned}
D_m
 &=L-\frac{m}{d^2/q}\big[L-F(2-\delta)\big]
       +\frac{F(1+\delta)}{d/q},\\
d^2D_m
 &= L+mq\,F(2-\delta)+dq\,F(1+\delta).
\tag{1}
\end{aligned}
$$
In the second line the coefficient of $L$ is $d^2-mq=1$, and the forced row's factorial contributes $\ln(1!)=0$.

## 3. Gamma estimates and the proof for $m\ge4$

The integral $\Gamma(u)=\int_0^\infty t^{u-1}e^{-t}\,dt$ is positive and convergent for $u>0$. Integration by parts gives $\Gamma(u+1)=u\Gamma(u)$, since $t^u e^{-t}$ vanishes at both boundaries. Direct integration gives $\Gamma(1)=1$, so induction gives $\Gamma(n+1)=n!$ for $n\ge0$. Consequently $F(1)=F(2)=0$ and $F(u+1)=F(u)+\ln u$.

For $x,y>0$ and $0\le\lambda\le1$, normalize each of $t^{x-1}e^{-t}$ and $t^{y-1}e^{-t}$ by its positive integral to get functions $A$ and $B$ of integral one. Pointwise, $A^\lambda B^{1-\lambda}\le\lambda A+(1-\lambda)B$ by concavity of $\ln$ on the positive reals. Integration bounds the integral of the product by one. Undoing normalization yields
$$
\Gamma(\lambda x+(1-\lambda)y)\le\Gamma(x)^\lambda\Gamma(y)^{1-\lambda},
$$
so $F$ is convex on $(0,\infty)$. It is differentiable there. On a compact interval $[a,b]\subset(0,\infty)$, the derivative integrand for $\Gamma$ has absolute value bounded by $t^{a-1}|\ln t|$ for $0<t\le1$ and $t^{b-1}e^{-t}\ln t$ for $t\ge1$. These are integrable by the substitution $s=-\ln t$ near zero and exponential decay at infinity. Applying dominated convergence to difference quotients and using $\Gamma>0$ proves differentiability of $F$.

For a convex function $f$, write $S(x,y)=(f(y)-f(x))/(y-x)$ for $x<y$. Convexity at $y$ between $x<y<z$, followed by multiplication by positive denominators, gives $S(x,y)\le S(x,z)\le S(y,z)$. If $f$ is differentiable, taking interior points to $x$ and to $y$ in this comparison gives $f'(x)\le S(x,y)\le f'(y)$.

Here $F'(u+1)=F'(u)+1/u$, by differentiating the recurrence. Put $H_n=\sum_{j=1}^n 1/j$. For $n\ge1$, iteration gives $F'(n+1)=F'(1)+H_n$. The slopes on the unit intervals to the left and right of $n+1$ are $\ln n$ and $\ln(n+1)$, by the recurrence. Thus
$$
H_n-\ln(n+1)\le -F'(1)\le H_n-\ln n.
$$
The sequence $H_n-\ln n$ is decreasing since $\ln(n+1)-\ln n=\int_n^{n+1}1/t\,dt>1/(n+1)$. It is bounded below by zero since $\ln(n+1)\le H_n$, by integrating $1/t$ over each interval $[j,j+1]$. Its limit $\gamma$ is the Euler–Mascheroni constant. The two bounds on $-F'(1)$ differ by $\ln(1+1/n)\to0$, so $F'(1)=-\gamma$ and $F'(2)=1-\gamma$.

Taking $x=2-\delta,\ y=2$ in the upper slope inequality and $x=1,\ y=1+\delta$ in the lower one is valid because $0<\delta<1$. Since $F(1)=F(2)=0$, these inequalities give
$$
F(2-\delta)\ge-(1-\gamma)\delta,\qquad
F(1+\delta)\ge-\gamma\delta.
\tag{2}
$$
The coefficients $mq,dq$ in (1) are positive for $m\ge1$. Inserting (2) and using $q\delta=1,\ d-m=1$ gives
$$
d^2D_m\ge \ln((m+1)!)-m(1-\gamma)-d\gamma
       = \ln((m+1)!)-m-\gamma.
\tag{3}
$$

For the strict sign in (3), first bound $e=\exp(1)<68/25$. In the series $\sum_{j\ge0}1/j!$, all ratios in the tail starting at $j=7$ are at most $1/8$, so the sum is at most $\sum_{j=0}^6 1/j!+8/(7\cdot 7!)<68/25$. The integer comparison $68^{107}<6^{60}25^{107}$ gives $e^{107}<6^{60}$, so $\ln 6>107/60$. As $H_6=49/20$ and $H_n-\ln n$ is decreasing, $\gamma\le H_6-\ln6<49/20-107/60=2/3$. For the factorial bound, $e<68/25<11/4$ and $11^{14}<120^3\,4^{14}$ give $e^{14}<120^3$. Taking logarithms yields $\ln120>14/3=4+2/3$. For every $m\ge4$, passing from $m$ to $m+1$ adds $\ln(m+2)\ge\ln6>1$ to $\ln((m+1)!)$ and adds $1$ to $m+2/3$. Therefore $\ln((m+1)!)>m+2/3$ by induction. The right side of (3) is positive for every $m\ge4$, and $d^2>0$, so $D_m>0$.

## 4. Integer certificates at $m=1,2,3$

Fix $n\ge1$ and $0<a<1$. The slopes of the unit secants of $F$ from $n$ to $n+1$ and from $n+1$ to $n+2$ are $\ln n$ and $\ln(n+1)$. By the slope comparison of §3, the secant from $n+1$ to $n+1+a$ has slope between the two. Multiplying by $a>0$ and using $F(n+1)=\ln(n!)$ bounds $F(n+1+a)$ between $\ln(n!)+a\ln n$ and $\ln(n!)+a\ln(n+1)$. The recurrence gives
$$
F(n+1+a)=F(1+a)+\sum_{j=1}^n\ln(j+a).
$$
For $a=k/q$ with integers $0<k<q$, put $C=n!\,q^n$ and $P_k=\prod_{j=1}^n(qj+k)$. Then $\sum_{j=1}^n\ln(j+a)=\ln P_k-n\ln q$, since $j+a=(qj+k)/q>0$. Hence
$$
\ln C+\frac{k}{q}\ln n-\ln P_k\le F(1+k/q)\le
\ln C+\frac{k}{q}\ln(n+1)-\ln P_k.
\tag{4}
$$
Use the two bounds for $k=q-1$ and $k=1$ in (1). Since $2-\delta=1+(q-1)/q$, the positive weights in (1) are $A=mq$ and $B=dq$, and the power of the secant integer is $A(q-1)/q+B/q=mq+1$. The resulting lower bound for $d^2D_m$ is $\ln R(n)$ and the upper bound is $\ln R(n+1)$, where
$$
R(s)=\frac{d!\, C^{A+B}s^{mq+1}}{P_{q-1}^{A}P_1^{B}}.
\tag{5}
$$
Every factor is positive. The order of the numerator and denominator determines the sign of $\ln R(s)$.

For $m=3$, take $n=64,\ q=5,\ A=15,\ B=20$. The numerator $24(64!\,5^{64})^{35}64^{16}$ strictly exceeds the denominator $P_4^{15}P_1^{20}$. This proves $D_3>0$. For $m=1,2$, take $n=256,\ s=257$. In both cases the numerator in (5) is strictly smaller than the denominator, giving $D_m<0$. The three comparisons in (5), the exponential-series fraction comparison, and the two power comparisons of §3 can be reproduced by the exact arithmetic below. The loops multiply the factors in $n!$, $P_{q-1}$, and $P_1$, and each asserted comparison is between integers or exact fractions.

```python
from fractions import Fraction
from math import factorial

assert sum(Fraction(1, factorial(j)) for j in range(7)) + Fraction(8, 7 * factorial(7)) < Fraction(68, 25)
assert 68**107 < 6**60 * 25**107
assert 11**14 < 120**3 * 4**14

for m, n, s in [(1, 256, 257), (2, 256, 257), (3, 64, 64)]:
    q = m + 2
    A, B = m*q, (m+1)*q
    C = factorial(n)*q**n
    P, Q = 1, 1
    for j in range(1, n+1):
        P *= q*j + q-1
        Q *= q*j + 1
    numerator = factorial(m+1)*C**(A+B)*s**(m*q+1)
    denominator = P**A*Q**B
    assert (numerator > denominator) if m == 3 else (numerator < denominator)
```

Equations (1)–(5) and the matching count prove the theorem. This locates the first violation only within the stated family.

## 5. Numerical values

The table gives the natural-log gap $D_m$. The decimal values come from evaluating the defining expression at 85 and 145 decimal digits in the independent review and rounding the agreeing digits. The proof of the signs uses the exact comparisons above.

| $m$ | $\ell$ | $M$ | $\Phi_\ell(G_m)$ | $D_m$, approximate |
|---:|---:|---:|---:|---:|
| 1 | 2 | 3 | 2 | −0.073236792191 |
| 2 | 3 | 4 | 6 | −0.006967948444 |
| 3 | 4 | 5 | 24 | 0.025269621035 |
| 4 | 5 | 6 | 120 | 0.042737620287 |
| 5 | 6 | 7 | 720 | 0.052770424115 |
| 6 | 7 | 8 | 5040 | 0.058685186752 |
| 7 | 8 | 9 | 40320 | 0.062163542776 |
| 8 | 9 | 10 | 362880 | 0.064130440652 |

## 6. Lean correspondence

Finite Boolean matrices on `Fin ell × Fin M` encode the incidence relation after bijectively labelling each part. The conjunction `IKNoIsolates` requires a neighbour for each row and each column. `IKMatchings` implements the injection interpretation in §2, and `IKCount` takes its cardinality. `IKConjecture` quantifies over both sizes and every such matrix, requires the size inequality and no isolated vertices, and states the base-two inequality when the count is positive. This expresses the extended-real zero-count convention of §1 by vacuity. `IKPsi₂` has the source's inverse factor, factorial, and `Real.Gamma` argument. `IKPsi` and `IKRhs` use natural logs. `ik_rhs_base_two` proves the rescaling algebraically, with positivity of $\ln 2$ used in the inequality endpoints.

| Manuscript step | Lean declaration |
|---|---|
| Graph, no isolated vertices and degrees | `IKFamily`, `ik_family_edge`, `ik_family_no_isolates`, `ik_family_deg_zero`, `ik_family_deg_succ` |
| Force the special edge and count the injections | `ik_matching_equiv`, `ik_family_count`, `ik_witness_three_count` |
| Evaluate the row sum and prove (1) | `ik_family_rhs`, `ik_scaled_gap` |
| Derivatives and convex tangent bounds (2) | `ik_gamma_tangents` |
| Factorial induction and positivity from (3) | `ik_log_factorial_bound`, `ik_family_violation_ge_four` |
| Recurrence, lower secant bound (4) and integer product (5) for $m=3$ | `ik_log_gamma_rec`, `ik_gamma_chord_fifths`, `ik_chord_integer_comparison`, `ik_family_violation_three` |
| All $m\ge3$, including the source logarithm base | `ik_family_violation`, `ik_family_violation_base_two` |
| Positive-count witness and literal negation | `ilinca_kahn_conj31_false`, `ilinca_kahn_conj31_not` |

Lean adjoins the forced edge by giving the inverse to restriction and then uses Mathlib's `Fintype.card_embedding_eq`, which counts embeddings by induction through a newly assigned domain element. The natural-number falling factorial in that lemma simplifies to $(m+1)!/1!$. There is no enumeration of matchings. Lean imports the already proved Gamma recurrence, integer evaluations, convexity and derivatives from Mathlib. It gets the derivative at two from the integer derivative formula and the logarithm chain rule. It imports Mathlib's bound $\gamma<2/3$ and its bound on $\exp(1)$ in place of the manuscript's separate series and harmonic-sequence estimates of those constants. For $m=3$ it invokes the convex secant estimate and iterated recurrence from Mathlib's Bohr–Mollerup file. The integer comparison is reduced in the kernel using ordinary `decide`. The strict signs for $m=1,2$ in §4 have exact arithmetic certificates in the written proof. Lean formalizes the violations for $m\ge3$ and the count for all $m$, with the two small nonviolations outside its theorem set.

The following `#check` and `#print axioms` output is from the clean Lean 4.34.1 build with Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. The accompanying Lean source appendix records every module.

```text
IKConjecture : Prop
IKRefutation : Prop
ik_family_no_isolates {m : ℕ} (hm : 0 < m) : IKNoIsolates (IKFamily m)
ik_family_count (m : ℕ) : IKCount (IKFamily m) = (m + 1).factorial
ik_witness_three_count : IKCount (IKFamily 3) = 24
ik_family_violation_three : IKRhs (IKFamily 3) < log ↑(IKCount (IKFamily 3))
ik_family_violation_ge_four {m : ℕ} (hm : 4 ≤ m) : IKRhs (IKFamily m) < log ↑(IKCount (IKFamily m))
ik_family_violation {m : ℕ} (hm : 3 ≤ m) : IKRhs (IKFamily m) < log ↑(IKCount (IKFamily m))
ik_family_violation_base_two {m : ℕ} (hm : 3 ≤ m) :
  ∑ x, IKPsi₂ (IKDeg (IKFamily m) x) (↑(m + 1) * ↑(IKDeg (IKFamily m) x) / ↑(m + 2)) < IKLog₂ ↑(IKCount (IKFamily m))
ilinca_kahn_conj31_false : IKRefutation
ilinca_kahn_conj31_not : ¬IKConjecture
'IKConjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
'IKRefutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ik_family_no_isolates' depends on axioms: [propext, Quot.sound]
'ik_family_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'ik_witness_three_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'ik_family_violation_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'ik_family_violation_ge_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'ik_family_violation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ik_family_violation_base_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'ilinca_kahn_conj31_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'ilinca_kahn_conj31_not' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 7. Literature and limits

The source was read on arXiv, including its definitions, §2 context and §3 statement. The discovery and independent review searched the exact conjecture, the paper title and authors, and related phrases involving rectangular permanents, Gamma bounds, and Brégman's theorem through 18 November 2026. They identified no earlier public counterexample to (20). The reviewer checked the relevant arXiv passages of [3–5] on regular graphs and [6] on the square and regular comparisons. The review also read selected text in [7] on perfect matchings and in [8] on a different rectangular permanent bound. The bounded search leaves open the possibility of prior results in sources it missed. The journal version of [1] and separate journal versions of [2–7] were unread for this work. Reading of related preprints was limited to the passages described above. In particular, the open status of the constant-left-degree integral-$t$ case is reported within this search scope.

This manuscript and formalization were produced by AI from an AI discovery and a separate AI mathematical review. The $m=3$ integer certificate is from that review. The formal statements were checked with Lean's kernel and inspected against the arXiv text. There has been no human peer review. The graph-family minimality statement makes no assertion about the smallest counterexample over all bipartite graphs.

## References

1. Liviu Ilinca and Jeff Kahn. “Asymptotics of the Upper Matching Conjecture.” *Journal of Combinatorial Theory, Series A* **120** (2013), 976–983. [arXiv:1205.4342v1](https://arxiv.org/abs/1205.4342v1).
2. Lev M. Brégman. “Some properties of nonnegative matrices and their permanents.” *Soviet Mathematics Doklady* **14** (1973), 945–949. Bibliographic details as cited in [1].
3. Ewan Davies, Matthew Jenssen, Will Perkins, and Barnaby Roberts. “Independent Sets, Matchings, and Occupancy Fractions.” [arXiv:1508.04675](https://arxiv.org/abs/1508.04675).
4. Ewan Davies, Matthew Jenssen, Will Perkins, and Barnaby Roberts. “Tight bounds on the coefficients of partition functions via stability.” [arXiv:1704.07784](https://arxiv.org/abs/1704.07784).
5. Ewan Davies, Matthew Jenssen, and Will Perkins. “A proof of the Upper Matching Conjecture for large graphs.” [arXiv:2004.06695](https://arxiv.org/abs/2004.06695).
6. David Galvin. “Three tutorial lectures on entropy and counting.” [arXiv:1406.7872](https://arxiv.org/abs/1406.7872).
7. Mohsen Aliabadi and Elliot Krop. “Odd-cycle defects in the Alon-Friedland bound.” [arXiv:2607.14134](https://arxiv.org/abs/2607.14134).
8. Suvrit Sra. “A sharp Brégman–Minc bound for permanents.” 31 October 2026. [Author's preprint page](https://suvrit.github.io/papers/gurvits/).
