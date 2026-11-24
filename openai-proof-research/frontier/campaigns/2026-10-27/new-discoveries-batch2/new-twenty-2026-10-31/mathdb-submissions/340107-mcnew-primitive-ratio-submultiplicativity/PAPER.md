# McNew’s conjecture on ratios of primitive-set counts

**Abstract.** We prove both inequalities in McNew’s Conjecture 1. The proof uses positive association on the lattice of lower sets to compare the fractions of antichains that avoid a specified lower set. Applying that comparison inside blocks of multiples gives the coprime inequality and the stronger bound $g(ab)\le g(b)$ for all positive $a,b$, which implies the prime-power inequality.

## Definitions and statement

McNew defines a primitive set in §1.

> A set of integers is called a primitive set if no integer in the set is a divisor of another.

The abstract gives the counting definition.

> Let $Q(n)$ denote the count of the primitive subsets of the integers $\{1,2\ldots,n\}$.

In §5 McNew writes

> We define $g(1)=1$ and for $k>1$
>
> $$
> g(k)=\frac{Q(k)}{Q(k-1)}-1=
> \frac{\#\text{Primitive subsets of }[1,k]\text{ that include }k}
> {\#\text{Primitive subsets of }[1,k-1]}.
> $$

The source gives $g(1)=1$ explicitly and uses the quotient definition for $k>1$. It gives no separate value for $Q(0)$. Taking $\{1,\ldots,0\}=\varnothing$ in the counting definition gives $Q(0)=1$, since the empty set is primitive and is the sole subset of that interval. The empty set is counted: McNew identifies $Q(n)$ with OEIS A051026 (§1), whose terms $1,2,3,5,7,13,\ldots$ for $n=0,1,2,\ldots$ include it, and with this convention the quotient formula at $k=1$ gives $Q(1)/Q(0)-1=2/1-1=1$, in agreement with the stated value $g(1)=1$. Each $Q(k)$ is positive because the empty set is always counted. [McNew, arXiv v2, pp. 1, 9–10](https://arxiv.org/pdf/1808.04923v2) · [Author-hosted journal text](https://www.nathanmcnew.com/PrimitiveSets2.pdf)

The Lean definitions are as follows.

```lean
def IsPrimitive (S : Finset ℕ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b

noncomputable def Q (k : ℕ) : ℕ := ((Finset.Icc 1 k).powerset.filter IsPrimitive).card

noncomputable def g (k : ℕ) : ℚ :=
  if k ≤ 1 then 1 else (Q k : ℚ) / (Q (k - 1) : ℚ) - 1
```

The implication in `IsPrimitive` expresses that a divisibility relation within the set can only involve equal elements. The branch $k\le1$ also assigns a value at zero to make `g` total on the naturals. The endpoint uses only positive arguments.

> **Conjecture 1.** The function $g(n)$ is submultiplicative. If $(n,m)=1$ then
> $$
> g(nm)\le g(n)g(m).
> $$
> Furthermore, for any prime $p$, $g(p^{i+1})\le g(p^i)$.

Here $n,m$ are positive integers and $i$ is a nonnegative integer. We prove Conjecture 1 in this full range. [McNew, §5, Conjecture 1](https://www.nathanmcnew.com/PrimitiveSets2.pdf#page=10)

## Antichain avoidance in a finite poset

Write $\mathcal J(P)$ for the lower sets of a finite poset $P$, ordered by inclusion, and $N(S)$ for the number of antichains of an induced subposet $S$. Taking maximal elements gives a bijection between $\mathcal J(P)$ and the antichains of $P$. Indeed, every point of a lower set lies below some maximal element of that lower set by finiteness. The maximal elements of the lower closure of an antichain are exactly the original antichain, since its distinct points are incomparable. These maps also account for the empty lower set and empty antichain.

**Lemma.** For lower sets $A\subseteq C\subseteq P$ of $P$,
$$
\frac{N(C\setminus A)}{N(C)}\le\frac{N(P\setminus A)}{N(P)}.
\tag{1}
$$

Set $R=P\setminus A$ with the induced order. For $J\in\mathcal J(R)$, a lower set $I$ of $P$ with $I\cap R=J$ is determined by a lower set of $A$ containing $A\cap\downarrow_P J$, where $\downarrow_P J$ is the lower closure in $P$. Each such choice gives a lower set of $P$ because $J$ is lower in $R$ and every predecessor of a point of $A$ stays in $A$. Let $w(J)$ count the possible choices. It is positive because the full set $A$ is always a choice, and it decreases with $J$ because the forced set grows.

The event $F=\{J\in\mathcal J(R):J\subseteq C\setminus A\}$ is decreasing and nonempty. Since $C\setminus A$ is lower in $R$, these $J$ are the lower sets of $C\setminus A$. All completions of such $J$ lie in $C$ since $A\subseteq C$. Thus the bijection with antichains gives
$$
N(P\setminus A)=|\mathcal J(R)|,\qquad N(P)=\sum_{J\in\mathcal J(R)}w(J),
\qquad N(C\setminus A)=|F|,\qquad N(C)=\sum_{J\in F}w(J).
$$
The lattice $\mathcal J(R)$ is distributive, with union and intersection as join and meet. Its uniform weight satisfies the FKG lattice condition with equality. Applying FKG to the decreasing functions $w$ and $\mathbf 1_F$ yields
$$
\left(\sum_J w(J)\right)|F|\le |\mathcal J(R)|\sum_{J\in F}w(J).
$$
The decreasing form follows from the increasing form by reversing the lattice order. Substituting the four counts and dividing by the positive denominators proves (1). [Fortuin, Kasteleyn and Ginibre, Proposition 1](https://doi.org/10.1007/BF01651330)

## The divisor poset and a block estimate

For $k\ge1$, let $P_k=[1,k-1]$ ordered by divisibility and let $A_k\subseteq P_k$ be the positive proper divisors of $k$. Then $A_k$ is lower. Removing $k$ from a primitive subset of $[1,k]$ containing $k$ gives an antichain of $P_k\setminus A_k$, and adjoining $k$ gives the inverse. Any conflicting smaller point would divide $k$. The primitive subsets that omit $k$ are the antichains of $P_k$. Thus
$$
g(k)=\frac{N(P_k\setminus A_k)}{N(P_k)}.
\tag{2}
$$
This includes $k=1$ since $P_1=A_1=\varnothing$ and $N(\varnothing)=1$.

Fix positive $a,b$ and write $P=P_{ab}$. The block $B=\{aj:1\le j<b\}$ consists exactly of the multiples of $a$ in $P$, and $j\mapsto aj$ gives a divisibility isomorphism from $P_b$ to $B$. Suppose $V\subseteq P$ satisfies the following two conditions.

1. Its intersection with $B$ is the image of $A_b$.
2. No point of $P\setminus(B\cup V)$ divides a point in that image.

Then
$$
N(P\setminus V)\le g(b)\,N\bigl(P\setminus(V\setminus B)\bigr).
\tag{3}
$$
To prove this, partition each family of antichains by its part $T$ outside $B$. In both counts the outside choices are exactly the antichains in $P\setminus(B\cup V)$, because $T$ itself is an admissible completion with empty intersection with $B$. For fixed $T$, let $C_T\subseteq P_b$ consist of the indices $j$ for which $aj$ is incomparable with every point of $T$. No $aj$ divides a point of $T$, as that point would be a multiple of $a$. Hence the compatibility condition is that no point of $T$ divides $aj$. If $u\mid j$, a point dividing $au$ also divides $aj$. This proves that $C_T$ is lower. The second condition on $V$ gives $A_b\subseteq C_T$.

The compatible choices inside $B$ are in bijection with the antichains in $C_T\setminus A_b$ for the left side of (3) and with the antichains in $C_T$ for the count on the right. The bijection adjoins the scaled antichain to $T$, and its inverse restricts to the block and divides by $a$. By (1) and (2),
$$
N(C_T\setminus A_b)\le g(b)\,N(C_T).
$$
Summing the inequality over $T$ proves (3).

## Applying the block estimate

First set $V=A_{ab}$. By cancellation of $a$, $aj\mid ab$ is equivalent to $j\mid b$, giving the first condition of (3). Any point of $P$ dividing such an $aj$ divides $ab$ and belongs to $V$, giving the second condition. Since $N(P\setminus(A_{ab}\setminus B))\le N(P)$, equations (2) and (3) give $g(ab)\le g(b)$. Setting $a=p$, $b=p^i$ proves the prime-power inequality for every prime $p$ and $i\ge0$.

Now assume $(a,b)=1$. Let $B'$ be the block of multiples of $b$ in $P$. No point of $P$ is a common multiple of $a,b$, since such a point would be a positive multiple of $ab$. Moreover a point in one block cannot divide a point in the other, because the divisible point would be a common multiple. Thus $B,B'$ are disjoint and every pair drawn from different blocks is incomparable.

The first application of (3) removes the avoidance requirement inside $B$. Apply (3) again with the roles of $a,b$ reversed and $V=A_{ab}\setminus B$. Its intersection with $B'$ consists of the images of $A_a$, since $B'$ is disjoint from $B$ and divisibility cancels the factor $b$. If a point of $P$ outside $V$ divided one of those images, it would divide $ab$ and therefore lie in $B$. This contradicts incomparability, so the second condition holds as well. The resulting bounds are
$$
\begin{aligned}
N(P\setminus A_{ab})
&\le g(b)\,N(P\setminus(A_{ab}\setminus B))\\
&\le g(b)g(a)\,N(P).
\end{aligned}
$$
The second line uses $g(b)\ge0$ and that the family remaining after the second application is contained in the family of all antichains of $P$. Dividing by $N(P)>0$ and using (2) proves $g(ab)\le g(a)g(b)$. If one factor is 1 the asserted inequality is equality by $g(1)=1$.

## Significance and prior work

The theorem supplies the hypothesis for McNew’s conditional upper-bound computation for the exponential growth constant $\alpha=\lim_{n\to\infty}Q(n)^{1/n}$. Section 5 reports $\alpha<1.573487$ using the conjecture and the computed ratios for $n<899$. Our proof establishes the inequalities for every admissible input. The numerical value comes from McNew’s computation. The one-block estimate also supplies monotonicity of $g$ along divisibility for all positive integers. [McNew, §5](https://www.nathanmcnew.com/PrimitiveSets2.pdf#page=10)

The prior-art review found the source’s finite verification and conditional application, Angelo’s earlier existence proof for the growth constant, and related work on divisor graphs and primitive sets. It found neither a proof of these two universal inequalities in the inspected citing papers nor a relevant match in the inspected proof archives. The closest general result is FKG. Here the needed constructions are the extension count for each outside lower set, which turns the avoidance fraction into the reciprocal of a mean, and the arithmetic partition into blocks with compatible lower sets. The review and its cited-paper search bound this assessment. [Angelo’s existence proof](https://arxiv.org/abs/1711.08107) · [Prior-art audit](../fresh-shard034-discovery-sol62-20261119-r1/PRIOR-340107.md) · [Independent review](../candidates-review-R3-opus-20261119-r1/REVIEW-340107.md)

## Formal verification

`PrimitiveRatio.mcnew_conj1` proves the conjunction as a single Lean theorem. The lower-set bijections and FKG application prove the cross-multiplied form of (1) in `PrimitiveAvoidance.lean`. The literal definitions, the divisor-order bridge, the empty-interval convention and (2) appear in `PrimitiveCounts.lean`. The explicit finite-set bijection in each block fiber, the summation, and the two applications of (3) appear in `PrimitiveBlocks.lean`. The final divisions take place over the rationals with positive denominators. [Lean source appendix](LEAN-SOURCE-APPENDIX.md)
