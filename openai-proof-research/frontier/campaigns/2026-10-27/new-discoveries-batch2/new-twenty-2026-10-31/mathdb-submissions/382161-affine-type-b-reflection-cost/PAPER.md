# The reflection cost of affine signed permutations of type B

**MathDB 382161.** Resolution of Lewis–Tenner, Conjecture 4.2.

**Abstract.** The minimum cost of a reflection factorization in the affine type-B integer permutation realization of Lewis and Tenner is half the disarray plus the number of good cuts with odd sign parity. A lower bound charges new odd cuts to slack in crossing counts. An attaining factorization follows from a greedy rule that changes its choice of partner when the first swap would create an odd good cut.

## 1. Statement and source definitions

Lewis and Tenner state the following in §4.2 of the accepted manuscript. [Lewis–Tenner, *Bargain hunting in a Coxeter group*, arXiv:2302.04404v2](https://arxiv.org/pdf/2302.04404v2)

> **Conjecture 4.2.** If $w\in\widetilde S_n^B$, then
> $$
> \$(w)=\frac12\operatorname{dis}(w)+\operatorname{bl}^{\widetilde C}(w)-\operatorname{bl}^{\widetilde B}(w).
> $$

**The integer action.** The source takes $n$ to be an arbitrary positive integer. Its definition in §2.1 reads

> The Coxeter group $\widetilde S_n^C$ of affine type $\widetilde C$ consists of the affine signed permutations. In the language of [4] (which differs from that in [2]—see Section 4.1), these are the bijections $w:\mathbb Z\to\mathbb Z$ such that
>
> - $w(-i)=-w(i)$ for all $i\in\mathbb Z$, and
> - $w(i+(2n+2))=w(i)+(2n+2)$ for all $i\in\mathbb Z$.

Section 4.2 specifies the subgroup as “the group of affine signed permutations $w$ such that $\#\{i>0:w(i)<0\}$ is even.” Lean uses `PermZ := Equiv.Perm ℤ`, `period n := 2 * (n : ℤ) + 2`, and the two displayed identities as `AffSigned n w`. Its `AffB n w` conjoins this predicate with `Even (negCrossing w).ncard`, where `negCrossing w := {i | 0 < i ∧ w i < 0}`. Finiteness of that set is proved in `AffSigned.negCrossing_finite`. The finite even-signed condition quoted in §2.1 is “$\#\{i\in[n]:w(i)<0\}$ is even.”

**Transpositions and cost.** Definition 2.1 reads

> Given a George group $W$, a pair $\{i,j\}$ of different positions in $\mathbb Z$ is transposable if there exists at least one element $w$ in $W$ for which $w(i)=j$ and $w(j)=i$. If $\{i,j\}$ is a transposable pair, then the transposition $\langle(i\ j)\rangle$ is the extension of the transposition $(i\ j)$ under the symmetry conditions of the group; this is always an element of $W$ of multiplicative order 2.

Immediately after this definition the authors write, “The transpositions in a George group $W$ are precisely the reflections (when $W$ is viewed as a Coxeter group).” In §1 the cost is defined as a minimum over products of generators of $W$, and equation (3) specializes this to transpositions. We use symmetry extensions that belong to $\widetilde S_n^B$. The source’s membership requirement is essential. For $n=2$ the element $[-1,-2]$ interchanges both $1,-1$ and $2,-2$, so both pairs pass the existential test in Definition 2.1. Each orbit extension by itself has one positive-to-negative crossing. The pair test alone therefore admits swaps outside $\widetilde S_n^B$. Eriksson and Eriksson describe the exclusion at a locally even mirror in §4.2 and identify the class transpositions in the subgroup with Coxeter reflections in Lemma 17. Their standard affine type-B presentation is for $n\ge3$. We use Lewis and Tenner’s positive-$n$ convention and the same permutation and orbit definitions at $n=1,2$. [Eriksson–Eriksson, §§4.2 and 5.2.2 and Lemma 17](https://doi.org/10.37236/1356)

Lean’s `swapCopy n x y a b` prescribes the ordered pair $(a,b)$ by translating $(x,y)$, $(y,x)$, $(-x,-y)$ or $(-y,-x)$ by a common multiple of $2n+2$. The predicate `BRefl n t` requires `AffB n t`, distinct $x,y$, every prescribed swap, and the identity at every position outside the copies.

Definition 2.3 gives the disarray as
> $$\operatorname{dis}(w):=\sum_{i=1}^n |w(i)-i|.$$

Section 2.2 gives reflection cost as half the disarray of the reflection, with the displayed numerator printed as $\operatorname{dis}(w)$ in the definition of $\$(t)$ and specified by the following concrete explanation.

> Concretely, the first condition means that $\$(\langle(i\ j)\rangle)=|i-j|$ if $i$ and $j$ belong to different symmetry classes, while $\$(\langle(i\ j)\rangle)=\frac12|i-j|$ if $i$ and $j$ belong to the same symmetry class.

Its equation (3) is
> $$\$(w)=\min_{\substack{t_1\cdots t_k=w\\t_1,\ldots,t_k\in T}}\left\{\$(t_1)+\cdots+\$(t_k)\right\}.$$

Lean’s `dis` sums `Int.natAbs (w i - i)` over the integer images of $1,\ldots,n$. The set `Costs2 n w` contains the sums of `dis n` over lists of `BRefl n` whose product is $w$. Each element is twice the source’s cost of the corresponding list. The attainment argument in §4 makes this set nonempty for every $w$ in affine B, so its least element is twice the source’s minimum.

**Block counts.** Section 4.2 defines both cuts.

> Given an affine signed permutation $w$, say that an integer $j\in[n-1]$ is good if $w$ restricts to a bijection on $\pm[j]$ to itself.

> Suppose that $j$ is a good value for $w$. Say that $j$ is (further) very good if the restriction of $w$ to $\pm[j]$ is an even-signed permutation.

The two defining displays read
> $$\operatorname{bl}^{\widetilde C}(w)=1+\#\{\text{good values for }w\},$$
> $$\operatorname{bl}^{\widetilde B}(w)=1+\#\{\text{very good values for }w\}.$$

Lean’s `Good w j` expresses preservation of the integer interval $[-j,j]$. The extra point 0 is fixed by oddness. `VeryGood w j` adds evenness of `negPrefix w j`, the number of negative values in positions $1,\ldots,j$. `blC` and `blB` count the corresponding cuts in the half-open natural interval $[1,n)$ and add one. In the proof we write $\nu_j(w)$ for `negPrefix w j`, call a good cut with odd $\nu_j(w)$ an *odd good cut*, and let $\delta(w)$ count such cuts with $1\le j<n$. Every very good cut is good, giving `blB_le_blC`. Lean’s `block_difference` identifies the natural-number difference with the number of odd good cuts, so $\delta=\operatorname{bl}^{\widetilde C}-\operatorname{bl}^{\widetilde B}$. Put $F(w)=\operatorname{dis}(w)/2+\delta(w)$.

## 2. Window arithmetic and reflections

Write $N=2n+2$. Every affine signed permutation fixes 0 and $N/2$. The latter follows from $w(N-i)=N-w(i)$. Translation gives the other fixed mirror points. All remaining positions are uniquely $i+kN$ or $-i+kN$ with $1\le i\le n$ and $k\in\mathbb Z$. The integer $i$ is the class of the position. These identities determine $w$ from its window. They also give a uniform displacement bound by taking the maximum displacement on one period. Translation preserves the sign of the displacement, while negation reverses it.

Define $\chi(w)=\#\{p>0:w(p)<0\}$. For a window position $i$, write $w(i)=QN+r$ with $0<r<N$. The residue is nonzero since every multiple of $N$ is already fixed. In the positive progression $i+kN$ with $k\ge0$, a sign crossing occurs exactly when $k+Q<0$. In $-i+kN$ with $k\ge1$, it occurs exactly when $k\le Q$. Together these progressions contribute $|Q|$, so
$$
\chi(w)=\sum_{i=1}^n \kappa(w(i)),\qquad \kappa(x)=\left|\left\lfloor x/N\right\rfloor\right|.
$$
When $|x|\le n$, $\kappa(x)$ is the indicator of $x<0$. In particular, if $w$ preserves $[-j,j]$ with $j\le n$, then the part of $\chi(w)$ from classes $1,\ldots,j$ equals $\nu_j(w)$.

Parity of $\chi$ is additive under composition. For $p>0$, the negativity of $u(t(p))$ is the exclusive-or of the negativity of $t(p)$ and that of $u(|t(p)|)$. The map $p\mapsto |t(p)|$ is a bijection on the positive integers by oddness and bijectivity of $t$. Thus the two sets in the exclusive-or are finite and their symmetric difference has cardinality congruent to the sum of their cardinalities modulo two. The same proof works for $\nu_j$ if $t$ preserves $[-j,j]$, because the absolute-value map restricts to a bijection of $[1,j]$. In particular the affine B membership condition survives every step below.

Consider two distinct endpoints outside the fixed mirror positions. For different classes, the copies of the pair uniquely specify an involution, since the four residues of the two endpoints and their negatives are distinct. For a same-class pair, an endpoint cannot be a nonzero translate of the other: a swap would contradict translation equivariance. The remaining possibility is $y=kN-x$. This pair has compatible copies. If $x=\sigma a+hN$ with $1\le a\le n$ and $\sigma\in\{1,-1\}$, its window entry at $a$ becomes $-a+\sigma(k-2h)N$. The quotient by $N$ is $\sigma(k-2h)-1$. Its absolute value is even precisely for odd $k$. For a different-class pair write $x=\sigma a+hN$ and $y=\tau b+\ell N$. The two changed window entries are $\sigma\tau b+\sigma(\ell-h)N$ and $\sigma\tau a+\tau(h-\ell)N$. The sum of their quotients is even, since $\sigma$ and $\tau$ are congruent modulo two and the contribution of the common sign $\sigma\tau$ is twice an integer. Thus all different-class orbit swaps and the same-class swaps with odd $k$ belong to affine B. In particular the signed window swaps and both forms of the mirror swap at $N/2$ used below belong to the subgroup.

If $t$ is a reflection with endpoints $x<y$ satisfying $w(x)\ge y>x\ge w(y)$, right multiplication by $t$ decreases the sum of the absolute displacements at those two positions by $2(y-x)$. Each decreases by $y-x$, as is seen by subtracting the two absolute values at each position. The displacements at symmetry copies have the same absolute values. For different classes use one representative from each class, giving a disarray decrease of $2(y-x)=\operatorname{dis}(t)$. For a same-class swap use one representative, giving a decrease of $y-x=\operatorname{dis}(t)$. We call these swaps *efficient*. This is the crossing-pair calculation of Lewis–Tenner, Lemma 3.5.

## 3. Lower bound by crossing counts

For an integer $j$, let $R_j(w)=\{p:p\le j<w(p)\}$ and $L_j(w)=\{p:w(p)\le j<p\}$, the positions crossing the cut $j+1/2$ to the right and left. These sets are finite by the displacement bound. Write $f_j(w)=|R_j(w)|$.

First, right and left counts are equal. Their difference is the finite-support sum of $\mathbf 1_{p\le j}-\mathbf 1_{w(p)\le j}$ over the integers. On increasing $j$ by one the sum changes by $1-\# w^{-1}(\{j+1\})=0$. At $j=0$ negation bijects the right and left crossers because $w$ is odd and fixes 0. This fixes the value of the difference for all cuts. Negation exchanges directions and sends $j$ to $-j-1$. It follows by balance and translation that
$$
f_j(w)=f_{-j-1}(w)=f_{j+N}(w).
$$

Next, count the pairs $(p,j)$ in which the displacement from $p$ to $w(p)$ crosses the cut $j+1/2$. Simultaneous translation of both coordinates by $N$ preserves this relation. Taking $p$ in $[0,N)$ gives $\sum_{0\le p<N}|w(p)-p|=2\operatorname{dis}(w)$ by reflection about $N/2$ and the two fixed points. Taking $j$ in $[0,N)$ gives $2\sum_{0\le j<N}f_j(w)$ by balance. Each normalization chooses one pair per orbit, so the two counts agree. Pairing the cuts $j$ and $N-j-1$ now gives
$$
\operatorname{dis}(w)=2\sum_{j=0}^n f_j(w).
$$

For affine signed $u,t$, there is an injection from $R_j(ut)$ to the disjoint union $R_j(t)\sqcup R_j(u)$. If $t(p)>j$, send $p$ to $p$ in the first summand. Otherwise send it to $t(p)$ in the second summand. This is injective by bijectivity of $t$. Let $s_j=f_j(u)+f_j(t)-f_j(ut)\ge0$.

**Charge for a new odd cut.** Suppose $1\le j<n$, $t$ is an affine B reflection and $j$ is odd good for $v=ut$. If $t$ fails to preserve $[-j,j]$, finiteness and injectivity give a point in the interval that leaves it. By oddness of $t$ we can take that point $p$ with $t(p)>j$. The point $p$ belongs to $R_j(t)$ and the corresponding element of the first summand of the injection is missed, since $v$ preserves the interval. Hence $s_j\ge1$.

If $t$ preserves the interval, its restriction is even-signed. Indeed, if it moves an interior point, rebase its copies at that point and its image, both in $[-j,j]$. Every point in a positive translate by $kN$ with $k\ge1$ of those central signed copies has positive image. Each central copy stays inside the interval and each negative translate stays negative. Thus every sign crossing of $t$ lies inside the interval, and $\nu_j(t)=\chi(t)$ is even. If it moves no point of the interval then $\nu_j(t)=0$. Since both $v$ and $t$ preserve the interval, $u$ also preserves it, and prefix parity implies $\nu_j(u)$ is odd. This proves $s_j\ge1$ at every odd good cut of $v$ that was absent for $u$.

The increase in the number of odd good cuts is at most the number of new ones. The corresponding indices are distinct, so
$$
\delta(ut)-\delta(u)\le\sum_{j=0}^n s_j
 =\frac{\operatorname{dis}(u)+\operatorname{dis}(t)-\operatorname{dis}(ut)}2.
$$
Equivalently $F(ut)\le F(u)+\$(t)$. Iterating over a reflection list, with $F(1)=0$, bounds $F(w)$ above by the sum of the reflection costs in every factorization of $w$.

## 4. Attainment by greedy steps

We show that every $w\ne1$ in affine B admits a reflection $t$ such that $F(wt)+\$(t)=F(w)$. Let $q$ be the largest moved window position. If $j\ge q$ is good with $j\le n$, then $w$ preserves $[-n,n]$ because the higher positions are fixed. Thus $\nu_j(w)=\nu_n(w)=\chi(w)$ is even.

**Adjacent parity fix.** If the largest odd good cut $j_0$ exists and $w(j_0+1)<0$, swap $j_0,j_0+1$ with the same signs. Their images are both at most $j_0$, since $w(j_0)\in[-j_0,j_0]$ and $w(j_0+1)<-j_0$. Swapping them leaves disarray unchanged. Smaller cuts see the same window values, and $j_0$ ceases to be good. Higher cuts have unchanged goodness and parity because the swap preserves their intervals and its restriction is even-signed. Exactly one odd good cut is removed, paying the cost one.

In the remaining cases let $g$ be the greatest good cut below $q$, allowing $g=0$. There are no good cuts in $(g,q)$. Position $s=g+1$ is moved: if it were fixed, then it would extend the good interval up to $s$, contradicting maximality of $g$ if $s<q$, or the definition of $q$ if $s=q$. Also, if $\nu_g(w)$ is odd, then $g$ is the largest odd good cut, and the failure of the adjacent parity fix implies $w(s)>0$.

All subsequent swaps move only window classes in $(g,q]$. For $v=wt$, cuts at most $g$ keep their goodness and parity, and cuts at least $q$ that are good for $v$ have even parity because positions above $q$ remain fixed. Consequently an efficient swap is a step of the required cost if every good cut of $v$ in $(g,q)$ has even parity.

### 4.1. Rightmost exceedance

If $w(q)>q$, all positions strictly between $q$ and $N-q$ are fixed by maximality of $q$ and reflection about $N/2$. Injectivity forces $w(q)\ge N-q$. Now $w(N-q)=N-w(q)\le q$, so $(q,N-q)$ is an efficient mirror pair. It fixes the window below $q$ and therefore creates no good cuts in $(g,q)$.

### 4.2. Last transition to an anti-exceedance

Suppose $w(q)<q$, and some position in $(g,q]$ has $w(i)>i$. Take $a$ to be the last such position and $b$ the first moved position after it. Then $g<a<b\le q$. Positions strictly between $a$ and $b$ are fixed. Since $a$ is the last exceedance and $b$ is moved, $w(b)<b$, and $w(i)\le i$ for $b<i\le n$. The fixed positions own their values, giving $w(a)\ge b$ and $w(b)\le a$. So the positive swap $t_1=(a,b)$ is efficient, using orbit extension throughout. Set $v_1=wt_1$.

If $j\in(g,q)$ is good for $v_1$, then $a\le j<b$. Indeed the swap leaves smaller windows unchanged and preserves every interval containing both classes. Positions from $a+1$ to $j$ are fixed. Removing these fixed positions and their negatives from the invariant interval shows that $a$ is good for $v_1$ with $\nu_a(v_1)=\nu_j(v_1)$. Thus $t_1$ works unless $a$ is odd good for $v_1$. Assume this exception, and write $\pi=\nu_a(v_1)$, an odd integer. In particular $w(b)=v_1(a)\in[-a,a]$. The exact preimage of $[-a,a]$ under $w$ is $[-a+1,a-1]\cup\{-b,b\}$, by applying $t_1$ to $[-a,a]$.

A second window partner is an index $c>b$ with $c\le n$, $c\le w(a)$ and $w(c)\le a$. If one exists take the smallest. Its image is negative by the preimage description, and $c\le q$ since a position above $q$ is fixed. Use the efficient positive swap $(a,c)$ to get $v$. Any new good cut in $(g,q)$ lies in $[a,c)$. It must include $b$ because $v(b)=w(b)\in[-a,a]$. Before $a$ the values agree with those of $v_1$. At $a$ the new value is negative, and at $b$ the value is the one at $a$ in $v_1$. Every position strictly between $a$ and the cut, other than $b$, carries a positive value. For positions between $a$ and $b$ this is fixedness. For positions beyond $b$ and before $c$, it follows from the minimality of $c$, since those positions are at most $w(a)$. Therefore the new prefix has parity $\pi+1$, which is even.

If no second window partner exists, consider $C=w(a)$. For every $b<i\le\min(C,n)$ one has $a<w(i)\le i$. If $C\le n$, then $b\le C\le q$ since positions above $q$ own their values. The permutation $v_1$ maps all positive positions in $(a,C]$ into $(a,C]$. This uses fixedness up to $b$, $v_1(b)=C$, and the preceding inequalities thereafter. Thus $v_1$ preserves $[-C,C]$, and so does $w$, because $t_1$ preserves the interval. If $C<q$ this is a forbidden good cut. If $C=q$ then $\nu_C(v_1)=\pi$ is odd, contrary to the even parity of a good cut at or beyond the last moved position. Thus $C>n$.

Now all window positions of $v_1$ beyond $a$, apart from $b$, have positive values at most $n$. The crossing formula gives $\chi(v_1)=\pi+\kappa(C)$. Since $\chi(v_1)$ is even, $\kappa(C)$ is odd. Positive $C$ therefore satisfies $C\ge N$, and $C\ne N$ because $N$ is fixed. Use the mirror partner $N-a$. The pair $(a,N-a)$ is efficient as $N-a\le C$ and $w(N-a)=N-C<0$. It changes only class $a$. Every good cut of the new $v$ in $(g,q)$ must include $a$ and then $b$, as $v(b)=w(b)\in[-a,a]$. The value at $a$ is $N-C<0$. All other positions in the cut beyond $a$, except $b$, carry the positive values bounded above in the preceding argument. The same parity count gives $\nu_j(v)=\pi+1$.

### 4.3. All outer window positions at or below the diagonal

Suppose $w(i)\le i$ throughout $(g,q]$, and therefore throughout the window beyond $g$. Set $s=g+1$. Its value is strictly below $s$ since it is moved, and it cannot lie in $[-g,g]$ because that interval is preserved. Hence $w(s)<0$. The failure of the adjacent parity fix forces $\nu_g(w)$ even. If $w(s)=-s$, then $s$ is good by extending the interval at $g$. This contradicts maximality if $s<q$. If $s=q$, the cut would have even parity, contradicting $\nu_s(w)=\nu_g(w)+1$. Put $d=-w(s)>s$.

If $d\le n$ there must be a position $i\in(s,d]$ with $w(i)<0$. Otherwise every position in $(s,d]$ has value between $0$ and its position, while $w(s)=-d$. Together with the good interval at $g$ this shows $w([-d,d])\subseteq[-d,d]$, hence equality by finiteness and injectivity. The cut at $d$ contradicts maximality if $d<q$ and has impossible odd parity if $d\ge q$.

If there is any negative value in window positions beyond $s$, let $r$ be the first. Then $r\le d$, by the preceding argument for $d\le n$ and by $r\le n$ otherwise. Its value is at most $-s$ since the values in $[-g,g]$ are taken. The pair $(-s,r)$ is efficient since $w(-s)=d\ge r$ and $w(r)\le-s$. Both classes are at most $q$. A good cut of $v=wt$ in $(g,q)$ satisfies $j<r$ since a cut containing both classes would also be good for $w$. The swap replaces $w(s)$ by $-w(r)>0$, and the unchanged positions in $(s,j]$ are positive by the choice of $r$. Thus $\nu_j(v)=\nu_g(w)$ is even.

Finally suppose all window positions beyond $s$ are positive. The finite argument implies $d>n$. Those outer positive values are at most $n$, so $\chi(w)=\nu_g(w)+\kappa(-d)$. Evenness forces $d>N$ since $0<d\le N$ gives $\kappa(-d)=1$. Moreover $d\ge N+s$. If $N<d<N+s$, the position $N+s$ outside $[-g,g]$ would have image $N-d$ inside that interval, a contradiction. Use the mirror pair $(-s,N+s)$. It is efficient since $w(-s)=d\ge N+s$ and $w(N+s)=N-d\le-s$. Only the window class $s$ changes, to $d-N>0$. The prefix at every new good cut again has parity $\nu_g(w)$.

### 4.4. Termination

Each step has $2F(wt)+\operatorname{dis}(t)=2F(w)$ with $\operatorname{dis}(t)>0$. Thus strong induction on the natural number $2F(w)$ gives a list attaining the cost. At the identity take the empty list. Otherwise factor $wt$ by induction and append the involution $t$ to get $w$. The lower bound proves optimality. This establishes Conjecture 4.2 in the period-$2n+2$ realization for all positive $n$.

## 5. Context, verification and credit

The closest prior work is Lewis–Tenner’s unbranched result, Theorem 3.1, with the displacement lower bound in Proposition 3.2 and the sorting step in Lemmas 3.4–3.5. Their finite type-D formula in Theorem 3.7 uses Bagno–Biagioli–Novick–Woo’s finite depth formula, Corollary 2.10. The unbranched argument supplies the basic efficient crossing, and the finite formula supplies the form of the correction. Here the cut count pays for each new odd good cut, while partner switching makes the greedy descent work across odd preserved intervals and unbounded lifts. The proof concerns reflection cost in the stated realization. [Lewis–Tenner, §§3–4](https://arxiv.org/pdf/2302.04404v2)

The formal endpoint in `AffineBCost.lean` is

```lean
theorem lewis_tenner_4_2 (n : ℕ) (_hn : 0 < n) (w : PermZ) (hw : AffB n w) :
    IsLeast (Costs2 n w) (dis n w + 2 * (blC n w - blB n w))
```

It combines the abstract lower bound over every list with a separate attainment theorem. The lower bound uses the evenness of an interval-preserving reflection directly, and the upper bound constructs the needed different-class and mirror swaps from the literal orbit predicate. Example 4.1 has good cuts $\{1,2,4,6,7,8\}$ and very good cuts $\{1,6,7\}$. The independent rank-one and rank-two witnesses give doubled minima 2 for $[3]$ and 8 for $[-1,-2]$. The Lean examples verify the windows and concrete arithmetic with kernel reduction and the minima by specialization.

The lower-bound crossing lemma is due to the Claude Opus 5.5 proof in lane `t1-pool199-proof-opus55-20261122-r1`. The pool 199 lane also supplied the adjacent parity step. Claude Opus 5.5 completed the attaining step rule in lane `c-382161-affine-b-cost-opus55-20261123-r1`. Claude Opus 5.5 performed the first review. The GPT-6.2 Sol cross-model review fixed the subgroup interpretation of the reflection set and the proof’s use of signs under negation and oddness for cut balance. The GPT-6.2 Sol packaging lane wrote the Lean formalization and the original exposition. A separate GPT-6.2 Sol lane performed the final check and edited the exposition.
