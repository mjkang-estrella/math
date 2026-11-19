# A positive proportion of partitions of an interval into k MSTD sets

## Abstract

A finite set $A$ of integers is MSTD (more sums than differences) if $|A+A|>|A-A|$. Chu, Luntzlara, Miller and Shao conjectured that for every fixed $k\ge2$ the proportion of partitions of $\{1,\dots,r\}$ into $k$ MSTD sets is bounded below by a positive constant. Asada, Manski, Miller and Suh proved the case $k=2$. We prove the bound for every $k\ge2$, for both ordered and unordered partitions.

The counting is done for labelled colourings $\{1,\dots,r\}\to\{1,\dots,k\}$: for all large $r$, at least a fraction $1/(2k^{2T})$ of the $k^r$ colourings have every colour class MSTD, where $T=T(k)$. The same lower bound up to a factor $k^{k}$ holds for unordered partitions into exactly $k$ blocks.

The proof constructs a $k$-colouring of $\mathbb Z/2h\mathbb Z$, with $h$ odd, in which antipodal residues get different colours and every colour class has full modular sumset. Laid periodically on both ends of the interval, it makes every colour class miss many extreme differences and only few extreme sums. The rest of the argument uses the fringe method of Martin–O'Bryant and Zhao.

The whole argument, including the existence of the modular colouring for every $k$, is formalized in Lean 4 with Mathlib and kernel-checked. It uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## 1. The conjecture

**Source.** Hùng Viê.t Chu, Noah Luntzlara, Steven J. Miller and Lily Shao, *Infinite families of partitions into MSTD subsets*, arXiv:1808.05460 (v1 16 August 2018, v2 22 October 2019). The v2 text carries the header "INTEGERS: 19 (2019)". I read v1 and v2 from arxiv.org; the statement of Conjecture 1.5 is the same in both.

**Definitions, quoted from §1 of the source.**

* "Given a set $A$ of integers, define $A+A=\{a_i+a_j\mid a_i,a_j\in A\}$ and $A-A=\{a_i-a_j\mid a_i,a_j\in A\}$. Then $A$ is said to be sum-dominant or MSTD (more-sums-than-differences) if $|A+A|>|A-A|$."
* "Let $[a,b]$ denote $\{\ell\in\mathbb Z\mid a\le\ell\le b\}$ and $I_r$ denote $[1,r]$."
* "a 2-decomposition of a set $S$ is $A_1\cup A_2=S$, where $A_1,A_2$ are nonempty and $A_1\cap A_2=\emptyset$. We use the words decomposition and partition interchangeably."

A $k$-decomposition is accordingly a partition into $k$ nonempty, pairwise disjoint sets.

**The conjecture, quoted from §1.2 of the source.**

> **Conjecture 1.5.** For any finite $k\ge 2$, the proportion of $k$-decompositions into MSTD subsets is bounded below by a positive constant.

**Reading of the quantifiers.** The constant may depend on $k$. The bound is asymptotic in $r$. The abstract says the source gives "a sufficient condition on when there exists a positive constant lower bound for the proportion of decompositions of $\{1,2,\dots,r\}$ into $k$ MSTD subsets as $r\to\infty$". Theorem B.4 says "as $m\to\infty$". For small $r$ the proportion is $0$: by Theorem 1.4 of the source, $R(k)\ge 8k$.

The proportion is taken among all partitions of $I_r$ into exactly $k$ nonempty blocks. Giving the blocks distinct labels multiplies the numerator and denominator by $k!$, so the ratio is identical for labelled partitions. We also prove a bound among all maps $I_r\to\{1,\dots,k\}$, allowing unused colours in the denominator. The setup of Theorem B.4 of the source uses labelled choices for the middle conditional on fixed fringes.

## 2. What was known

All results in this section are due to the cited authors.

* Martin and O'Bryant [MO] proved that a positive proportion of the subsets of $\{1,\dots,r\}$ are MSTD.
* Zhao [Z2] proved that this proportion converges and that the limit is at least $4.28\cdot10^{-4}$.
* Hegarty and Miller [HM] showed that in sparse random models almost all sets are difference-dominated.
* Zhao [Z1] counted MSTD subsets of finite abelian groups. He used the pairing of group elements by an element of order two, which is the precedent for the antipodal pairing in Lemma 5.
* **The case $k=2$.** Asada, Manski, Miller and Suh [AMMS, Theorem 1.4] proved that for a uniformly random $A\subseteq[0,n]$ with $n\ge19$, the probability that both $A$ and its complement are MSTD ("bi-MSTD") is bounded below by a positive number. They also showed that there are no bi-MSTD sets for $n<19$. Their proof uses a fringe pair found by computer.
* **The source's own results for $k\ge2$.**
  * Explicit 2-decompositions (Theorem 1.1).
  * Existence of $k$-decompositions into MSTD sets of $I_r$ for every $k\ge 2$ and every $r\ge R(k)$, with bounds on $R(k)$ (Theorem 1.4).
  * Theorem B.4 of arXiv v2 (Theorem 4.4 in the journal) states a sufficient condition for a positive proportion. It asks for a partition of $[0,2n-1]$ into MSTD $P_n$ sets whose fringe pairs satisfy $\sum_i f(L_i,R_i)<1$. Its estimates for each middle subset use density $1/2$. The proof below works directly at the density $1/k$ of a colour class.
  * A new proof of the case $k=2$ from an explicit fringe pair with $n=20$ (Corollary B.5).
* Section 4 ("Future Work") of the source asks whether the proportion is positive for $k\ge3$. That is Conjecture 1.5.

## 3. Results

Write $[k]=\{1,\dots,k\}$. A *colouring* of a finite set $X$ is a map $X\to[k]$, and its colour classes are the fibres.

**Theorem A (labelled form).** For every integer $k\ge2$ there are integers $D\ge1$ and $R$ such that for every $r\ge R$,
$$k^r\ \le\ D\cdot\#\{c:\{1,\dots,r\}\to[k] \;:\; \text{every colour class of } c \text{ is MSTD}\}.$$
One can take $D=2k^{2T}$ and $R=4T+1$, where $T=T(k)$ is constructed in the proof.

**Theorem B (Conjecture 1.5).** For every integer $k\ge 2$ there are $D'\ge1$ and $R$ such that for every $r\ge R$:
* the number of partitions of $\{1,\dots,r\}$ into exactly $k$ nonempty blocks is at most $D'$ times the number of such partitions in which every block is MSTD;
* in particular, the proportion of $k$-decompositions of $I_r$ into MSTD subsets is at least $1/D'$.

One can take $D'=Dk^k$.

Both theorems hold for every $k\ge 2$. Nothing is left to small cases or to computation.

## 4. Counting lemmas

Let $I$ and $B$ be finite sets, and let $S$ be a set of maps $I\to B$. We say $S$ is *free at* $x\in I$ if, whenever $\omega\in S$ and $b\in B$, the map $\omega[x\mapsto b]$ (that is, $\omega$ with its value at $x$ replaced by $b$) is again in $S$. These lemmas replace probabilistic independence by exact counts.

**Lemma 1 (one coordinate).** If $S$ is free at $x$ and $G\subseteq B$, then
$$|\{\omega\in S:\omega(x)\in G\}|\cdot|B|=|S|\cdot|G|.$$

*Proof.* If $B=\emptyset$, both sides are zero. Otherwise, for $a\in B$ let $S_a=\{\omega\in S:\omega(x)=a\}$. For $a,b\in B$, the map $\omega\mapsto\omega[x\mapsto b]$ sends $S_a$ to $S_b$, by freeness. Its inverse is $\omega\mapsto\omega[x\mapsto a]$, because $\omega[x\mapsto b][x\mapsto a]=\omega[x\mapsto a]=\omega$ when $\omega(x)=a$. Hence all fibres have the same size $f$. So $|S|=\sum_a|S_a|=|B|f$ and $|\{\omega\in S:\omega(x)\in G\}|=\sum_{a\in G}|S_a|=|G|f$. ∎

**Lemma 2 (one pair).** Let $x\ne y$, let $S$ be free at $x$ and at $y$, and let $G,G'\subseteq B$. Then
$$|\{\omega\in S:\neg(\omega(x)\in G\wedge\omega(y)\in G')\}|\cdot|B|^2+|S|\,|G|\,|G'|=|S|\,|B|^2 .$$

*Proof.* Let $S_1=\{\omega\in S:\omega(x)\in G\}$ and $S_2=\{\omega\in S_1:\omega(y)\in G'\}$. Changing $\omega(y)$ preserves membership in $S_1$, so $S_1$ is free at $y$. Lemma 1 gives $|S_1|\,|B|=|S|\,|G|$ and $|S_2|\,|B|=|S_1|\,|G'|$. Multiplying the second identity by $|B|$ and using the first gives $|S_2|\,|B|^2=|S|\,|G|\,|G'|$. The complementary set has cardinality $|S|-|S_2|$, which gives the asserted identity. ∎

**Lemma 3 (disjoint pairs).** Suppose $|B|=kc$ with $k,c\ge1$. Let $X_j,Y_j\in I$ for $j<n$ be $2n$ distinct coordinates, with $S$ free at each of them. Let $G_j,G'_j\subseteq B$ with $|G_j|=|G'_j|=c$. Then
$$T_n=\{\omega\in S:\ \forall j<n,\ \neg(\omega(X_j)\in G_j\wedge\omega(Y_j)\in G'_j)\}\quad\text{satisfies}\quad |T_n|\,k^{2n}=|S|\,(k^2-1)^n .$$

*Proof.* Induct on $m\le n$, proving the analogous identity for $T_m$. At $m=0$ it follows from $T_0=S$. For the step from $m$ to $m+1$ take $m<n$.
* $T_m$ is free at $X_m$ and at $Y_m$. Membership in $T_m$ depends, beyond membership in $S$, only on the coordinates $X_j,Y_j$ with $j<m$, and these differ from $X_m$ and $Y_m$.
* Lemma 2 applied to $T_m$ gives $|T_{m+1}|(kc)^2+|T_m|c^2=|T_m|(kc)^2$.
* Dividing by $c^2>0$ gives $|T_{m+1}|k^2=|T_m|(k^2-1)$.
* Multiplying by $k^{2m}$ and using the induction hypothesis gives $|T_{m+1}|\,k^{2(m+1)}=|S|\,(k^2-1)^{m+1}$. ∎

**Lemma 4 (distinct single coordinates).** Suppose $|B|=q$. Let $X_j$ for $j<n$ be distinct coordinates, with $S$ free at each, and let $|G_j|=g$. Then
$$|\{\omega\in S:\forall j<n,\ \omega(X_j)\in G_j\}|\,q^n=|S|\,g^n .$$

*Proof.* The same induction, using Lemma 1. ∎

## 5. The modular colouring

**Lemma 5.** For every $k\ge2$ there exist an odd $h\ge1$ and a map $F:\mathbb Z\to[k]$ with the following properties.
* (M0) $F(x)=F(y)$ whenever $x\equiv y\pmod{2h}$.
* (M1) $F(x+h)\ne F(x)$ for every $x$.
* (M2) For every colour $i$ and every $s\in\mathbb Z$ there is $u$ with $F(u)=F(s-u)=i$.

**Lemma 6.** For every $k\ge2$ there is $m\ge1$ with $(4m+2)\,k\,(k^2-1)^m<k^{2m}$.

*Proof of Lemma 6.*
* Put $b=(k^2-1)/k^2\in[0,1)$. Then $n b^n\to0$ as $n\to\infty$ (Mathlib `tendsto_self_mul_const_pow_of_lt_one`).
* Choose $m\ge1$ with $m b^m<1/(6k)$.
* Since $4m+2\le6m$, we get $(4m+2)k b^m\le 6k\,m b^m<1$.
* Multiply by $k^{2m}$. ∎

*Proof of Lemma 5.*

*Setup.*
* Take $m$ from Lemma 6 and put $h=2m+1$.
* Let $\Pi$ be the set of ordered pairs $(a,b)$ of distinct colours, so $|\Pi|=k(k-1)$.
* Let $\Omega$ be the set of all maps $\omega:\mathbb Z/h\mathbb Z\to\Pi$.
* For $\omega\in\Omega$ define $F_\omega(x)$ to be the first component of $\omega(x\bmod h)$ if $x$ is even, and the second component if $x$ is odd.

*Properties (M0) and (M1) hold for every $\omega$.*
* If $x\equiv y\pmod{2h}$, then $x\equiv y\pmod h$ and $x\equiv y\pmod 2$. This gives (M0).
* Since $h$ is odd, $x+h$ has the same residue mod $h$ as $x$ and the opposite parity. So $F_\omega(x+h)$ and $F_\omega(x)$ are the two components of the same pair $\omega(x\bmod h)$, and these differ. This gives (M1).

*Pairs of coordinates for a fixed sum.* Fix $s\in\mathbb Z$ and a colour $i$. Put $t_0=s(m+1)$. Then $2t_0-s=s(2m+1)=sh\equiv0\pmod h$.

For $d=0,\dots,m-1$ put
$$u_d=t_0+d+1,\qquad X_d=u_d\bmod h,\qquad Y_d=(s-u_d)\bmod h .$$
These $2m$ residues are distinct.
* If $X_d=Y_{d'}$, then $h$ divides $(s-u_{d'})-u_d=-(d+d'+2)-(2t_0-s)$. Hence $h$ divides $d+d'+2\in[2,2m]$, which is impossible since $h=2m+1$.
* If $X_d=X_{d'}$, then $h\mid d'-d$ with $|d'-d|<m<h$, so $d=d'$. The same argument applies to $Y_d=Y_{d'}$.

*The event for one pair.* Let $G_d$ be the set of $\pi\in\Pi$ whose component selected by the parity of $u_d$ equals $i$. Define $G'_d$ in the same way using the parity of $s-u_d$. Each of these sets has exactly $k-1$ elements:
* the pairs with first component $i$ are $(i,b)$ with $b\ne i$;
* the pairs with second component $i$ are $(a,i)$ with $a\ne i$.

By definition of $F_\omega$, the condition "$F_\omega(u_d)=i$ and $F_\omega(s-u_d)=i$" is the condition "$\omega(X_d)\in G_d$ and $\omega(Y_d)\in G'_d$".

*Bounding the bad colourings.* Let $\mathrm{Bad}(s,i)$ be the set of $\omega\in\Omega$ for which there is no $u$ with $F_\omega(u)=F_\omega(s-u)=i$. Every $\omega$ in $\mathrm{Bad}(s,i)$ fails the condition for each $u_d$. The set $\Omega$ is free at every coordinate. Lemma 3, with $B=\Pi$ and $c=k-1$, gives
$$|\mathrm{Bad}(s,i)|\,k^{2m}\le|\Omega|\,(k^2-1)^m.$$

*Union bound.* Sum over the $2hk$ pairs $(s,i)$ with $s\in\{0,\dots,2h-1\}$:
$$\sum|\mathrm{Bad}(s,i)|\,k^{2m}\ \le\ (4m+2)\,k\,(k^2-1)^m\,|\Omega|\ <\ k^{2m}\,|\Omega|,$$
by Lemma 6. So some $\omega$ lies in no $\mathrm{Bad}(s,i)$. For this $\omega$, (M2) holds whenever $0\le s<2h$.

*Extending (M2) to all $s$.* For an arbitrary $s$, let $s'=s\bmod 2h$ and take $u$ for $s'$. By (M0), $F(s-u)=F(s'-u)$, since $s-u\equiv s'-u\pmod{2h}$. ∎

## 6. The interval

**Fixed data.** For the rest of the proof fix:
* $k\ge2$, and $h$, $F$ from Lemma 5, with $p=2h$;
* an integer $Q$ with $Q\ge p$, and $T=Qp$;
* an integer $N\ge4T$.

**Colourings and the fringe set.**
* A colouring is a map $\omega:\{0,\dots,N\}\to[k]$, and $A_i=A_i(\omega)=\omega^{-1}(i)\subseteq\mathbb Z$ is its class of colour $i$.
* The *left fringe* is $[0,T-1]$ and the *right fringe* is $[N-T+1,N]$. The *middle* is $[T,N-T]$.
* $\Omega_F$ is the set of colourings that agree with $F$ on both fringes.

**Lemma 7.** $|\Omega_F|\,k^{2T}=k^{N+1}$, and $\Omega_F$ is free at every point of the middle.

*Proof.* The count is Lemma 4 applied to the set of all colourings, the $2T$ fringe positions, and $G_j=\{F(\text{position } j)\}$, with $g=1$ and $q=k$. Changing a middle value does not affect the fringe conditions, which gives freeness. ∎

**Lemma 8.** For every integer $\ell$, every $p\ge1$ and every $u$, the interval $[\ell,\ell+p-1]$ contains an $x$ with $x\equiv u\pmod p$.

*Proof.* Take $x=\ell+((u-\ell)\bmod p)$. ∎

**Lemma 9 (deterministic small sums).** Suppose:
* $G:\mathbb Z\to[k]$ satisfies (M0) with modulus $p$ and (M2);
* $1\le p\le T\le N$;
* $\omega(n)=G(n)$ for $0\le n<T$.

Then every $s$ with $p-1\le s\le 2T-p-1$ lies in $A_i+A_i$, for every colour $i$.

*Proof.*
* By (M2) for $G$ there is $u$ with $G(u)=G(s-u)=i$.
* Put $\ell=0$ if $s+1\le T$, and $\ell=s-T+1$ otherwise. In both cases $0\le\ell$, $s-T+1\le\ell$, $\ell+p\le s+1$ and $\ell+p\le T$. The last two use $p\le T$ and $s\le 2T-p-1$.
* By Lemma 8 pick $x\in[\ell,\ell+p-1]$ with $x\equiv u\pmod p$. Then $0\le x\le s$, $x\le T-1$ and $s-x\le T-1$.
* So $\omega(x)=G(x)=G(u)=i$, and $\omega(s-x)=G(s-x)=G(s-u)=i$, where the middle equalities use (M0) and $s-x\equiv s-u$.
* Hence $s=x+(s-x)\in A_i+A_i$. ∎

**Lemma 10 (many missing differences).** If $\omega\in\Omega_F$ and $2T\le N$, then $|A_i-A_i|+2Q\le 2N+1$ for every $i$.

*Proof.*

*The candidate differences.* Let $e=(N-h)\bmod p\in[0,p-1]$, and for $j<Q$ put $d_j=N-e-jp$. Then $d_j\equiv h\pmod p$, and since $e\le p-1$ and $jp\le(Q-1)p=T-p$, we have $N-T+1\le d_j\le N$.

*Claim.* If $a,b\in A_i$ and $a-b\ge N-T+1$, then $a-b\not\equiv h\pmod p$.
* Since $b\ge0$ we get $a\ge N-T+1$, and $b\le N-(N-T+1)=T-1$. So $a$ lies in the right fringe and $b$ in the left fringe, and $\omega(a)=F(a)$, $\omega(b)=F(b)$.
* If $a\equiv b+h\pmod p$, then $F(a)=F(b+h)\ne F(b)$ by (M0) and (M1).
* This contradicts $\omega(a)=\omega(b)=i$.

*Counting.*
* By the claim, no $d_j$ lies in $A_i-A_i$, and neither does any $-d_j$, since $b-a=d_j$ is the same situation with $a$ and $b$ exchanged.
* The $d_j$ are distinct, and they are positive while the $-d_j$ are negative. So $D=\{\pm d_j:j<Q\}$ has exactly $2Q$ elements.
* $D\subseteq[-N,N]$ and $A_i-A_i\subseteq[-N,N]\setminus D$. Hence $|A_i-A_i|\le 2N+1-2Q$. ∎

**Lemma 11.** If $1\le p\le N$ and $[p-1,2N-p+1]\subseteq A+A$, then $|A+A|\ge 2N-2p+3$.

*Proof.* The interval has $2N-2p+3$ elements. ∎

If both lemmas apply and $Q\ge p$, then
$$|A_i-A_i|\le 2N+1-2Q\le 2N+1-2p<2N-2p+3\le|A_i+A_i|,$$
so $A_i$ is MSTD.

### 6.1 The lower end with a random middle

In Lemmas 12, 13 and 15, $S$ is a set of colourings with two properties:
* every member of $S$ agrees on the left fringe with a map $G$ that satisfies (M0) with modulus $p$ and (M2);
* $S$ is free at every point of the middle.

**Lemma 12 (transition range).** For $2T-p\le s<3T$ and every colour $i$,
$$|\{\omega\in S: s\notin A_i+A_i\}|\cdot k^{Q-1}\ \le\ |S|\,(k-1)^{Q-1}.$$

*Proof.*
* *Fringe points of colour $i$.* By (M2) there is $u$ with $G(u)=i$. Put $e=u\bmod p\in[0,p-1]$, so $G(e)=i$. For $j<Q-1$ put $x_j=jp+e$. Then $x_j+p+1\le T$, because $(j+1)p\le(Q-1)p=T-p$ and $e\le p-1$. Also $G(x_j)=G(e)=i$, so $\omega(x_j)=i$ for every $\omega\in S$.
* *Their partners lie in the middle.* Put $y_j=s-x_j$. Then $y_j\ge (2T-p)-(T-p-1)=T+1$ and $y_j\le s\le 3T-1\le N-T$, so each $y_j$ is in the middle. The $y_j$ are distinct.
* *The event.* If $s\notin A_i+A_i$, then $\omega(y_j)\ne i$ for every $j$, since otherwise $s=x_j+y_j\in A_i+A_i$.
* *Count.* Apply Lemma 4 with $G_j=[k]\setminus\{i\}$, $g=k-1$ and $q=k$. ∎

**Lemma 13 (middle range).** For $3T\le s\le N$ and every colour $i$, with $n=\lfloor(s-2T)/2\rfloor$,
$$|\{\omega\in S: s\notin A_i+A_i\}|\cdot k^{2n}\ \le\ |S|\,(k^2-1)^n.$$

*Proof.*
* *The pairs.* Use the pairs $(T+j,\ s-T-j)$ for $j<n$.
* *They are distinct.* For $j,j'<n$ we have $(T+j)+(T+j')\le 2T+2n-2<s$, so $T+j<s-T-j'$. Hence all $2n$ points are distinct.
* *They lie in the middle.*
  * $T\le T+j\le T+n-1\le N-T$, since $2n\le s-2T\le N-2T$.
  * $s-T-j\le s-T\le N-T$.
  * $s-T-j\ge s-T-n+1>T$, since $2n\le s-2T$.
* *The event.* If $s\notin A_i+A_i$, then no pair has both points of colour $i$.
* *Count.* Apply Lemma 3 with $B=[k]$, $c=1$ and $G_j=G'_j=\{i\}$. ∎

### 6.2 Reflection

**Lemma 14.** For a colouring $\omega$ put $\omega'(x)=\omega(N-x)$.
* (a) $A_i(\omega')=N-A_i(\omega)$, hence $s\in A_i(\omega')+A_i(\omega')$ if and only if $2N-s\in A_i(\omega)+A_i(\omega)$.
* (b) The map $\omega\mapsto\omega'$ is injective.
* (c) Put $F'(x)=F(N-x)$. If $\omega\in\Omega_F$, then $\omega'\in\Omega_{F'}$.
* (d) $F'$ satisfies (M0) with modulus $p$, and (M2).

*Proof.*
* (a) and (b) are immediate.
* (c): reflection exchanges the two fringes.
* (d), property (M0): if $x\equiv y\pmod p$ then $N-x\equiv N-y\pmod p$.
* (d), property (M2): given $i$ and $s$, take $u_0$ with $F(u_0)=F(2N-s-u_0)=i$ and put $u=N-u_0$. Then $F'(u)=F(u_0)=i$, and $F'(s-u)=F(N-s+N-u_0)=i$. ∎

### 6.3 The weights and the half lemma

**The constant $\rho$.** Put $\rho=1-1/(2k^2)$. Then:
* $0\le\rho<1$;
* $(k-1)/k\le\rho$, because $1/(2k^2)\le1/k$;
* $(k^2-1)/k^2\le\rho^2$, because $\rho^2=1-1/k^2+1/(4k^4)$;
* $1/(1-\rho)=2k^2$.

**The weights.** Define $W(s)=\rho^{Q-1}$ if $s<3T$, and $W(s)=\rho^{\,s-2T-1}$ if $s\ge3T$.

**Lemma 15.** For $S$ as in §6.1 and $2T-p\le s\le N$, we have $|\{\omega\in S:s\notin A_i+A_i\}|\le|S|\,W(s)$.

*Proof.*
* *Case $s<3T$.* Lemma 12 gives the bound $|S|((k-1)/k)^{Q-1}\le|S|\rho^{Q-1}$.
* *Case $s\ge 3T$.* Lemma 13 gives the bound $|S|((k^2-1)/k^2)^n\le|S|\rho^{2n}$. Since $2n\ge s-2T-1$ and $\rho\le1$, this is at most $|S|\rho^{s-2T-1}$. ∎

**Lemma 16.** $\displaystyle\sum_{s=2T-p}^{N}W(s)\le (T+p)\rho^{Q-1}+2k^2\rho^{T-1}$.

*Proof.*
* At most $T+p$ values of $s$ in the range satisfy $s<3T$, and each contributes $\rho^{Q-1}$.
* The remaining values contribute at most
$$\sum_{s=3T}^{N}\rho^{s-2T-1}=\sum_{j=T-1}^{N-2T-1}\rho^j\le\frac{\rho^{T-1}}{1-\rho}=2k^2\rho^{T-1}.\ ∎$$

**Proposition 17.** Suppose
$$2k\big((T+p)\rho^{Q-1}+2k^2\rho^{T-1}\big)\le\tfrac12. \tag{★}$$
Then at least half of the colourings in $\Omega_F$ have every colour class MSTD.

*Proof.*

*Step 1: a colouring with a non-MSTD class has a missing sum in a controlled place.* Let $\omega\in\Omega_F$ and suppose $A_i$ is not MSTD. We show that there is $s\in[2T-p,N]$ with $s\notin A_i+A_i$ or $2N-s\notin A_i+A_i$.

Suppose not. We show that every $t\in[p-1,2N-p+1]$ then lies in $A_i+A_i$:
* if $t\le 2T-p-1$: Lemma 9 with $G=F$;
* if $2T-p\le t\le N$: the assumption with $s=t$;
* if $N<t\le 2N+p-2T$: the assumption with $s=2N-t$, which lies in $[2T-p,N)$;
* if $t\ge 2N+p+1-2T$: then $2N-t\in[p-1,2T-p-1]$. Apply Lemma 9 to $\omega'$, which agrees with $F'$ on its left fringe by Lemma 14(c), and use Lemma 14(d). Then Lemma 14(a) returns $t\in A_i+A_i$.

Now Lemmas 10 and 11, together with $Q\ge p$, show that $A_i$ is MSTD, which is a contradiction.

*Step 2: the bad set is covered by few events.* Let $\mathrm{Bad}$ be the set of $\omega\in\Omega_F$ with some class not MSTD. By Step 1,
$$\mathrm{Bad}\subseteq\bigcup_{i}\ \bigcup_{s=2T-p}^{N}\big(\mathrm{Low}(i,s)\cup\mathrm{Up}(i,s)\big),$$
where
* $\mathrm{Low}(i,s)=\{\omega\in\Omega_F:s\notin A_i+A_i\}$;
* $\mathrm{Up}(i,s)=\{\omega\in\Omega_F:2N-s\notin A_i+A_i\}$.

*Step 3: each event is small.*
* By Lemma 14, reflection maps $\mathrm{Up}(i,s)$ injectively into $\mathrm{Low}'(i,s)=\{\omega\in\Omega_{F'}:s\notin A_i+A_i\}$.
* By Lemma 7, $|\Omega_{F'}|=|\Omega_F|$, since both equal $k^{N+1-2T}$.
* Lemma 15 applies to $S=\Omega_F$ with $G=F$ and to $S=\Omega_{F'}$ with $G=F'$. Both sets are free in the middle by Lemma 7, and both maps satisfy (M0) and (M2) by Lemmas 5 and 14.

*Step 4: summing.* By Lemma 16 and (★),
$$|\mathrm{Bad}|\le\sum_i\sum_s 2|\Omega_F|W(s)\le 2k|\Omega_F|\big((T+p)\rho^{Q-1}+2k^2\rho^{T-1}\big)\le\tfrac12|\Omega_F|.\ ∎$$

**Lemma 18.** For every $p\ge1$ there is $Q$ with $Q\ge p$, $Q\ge1$, and (★) for $T=Qp$.

*Proof.*
* Let $C=4k(3p+2k^2)$. Since $M\rho^M\to0$ and $\rho^M\to0$, there is $M\ge p$ with $M\rho^M<1/C$ and $\rho^M<1/C$. Put $Q=M+1$.
* Then $T-1=(M+1)p-1\ge M$, so $\rho^{T-1}\le\rho^M$. Also $T+p=(M+2)p$.
* Hence the left side of (★) is at most $2k\big(p\cdot M\rho^M+2p\rho^M+2k^2\rho^M\big)$.
* This is less than $2k(3p+2k^2)/C=\tfrac12$. ∎

## 7. Proofs of the theorems

**Proof of Theorem A.** Fix $k\ge2$ and take $h,F$ from Lemma 5, $p=2h$, and $Q$ from Lemma 18. Put $T=Qp$, $D=2k^{2T}$ and $R=4T+1$. Let $r\ge R$ and $N=r-1\ge4T$.

By Lemma 7 and Proposition 17,
$$k^{r}=|\Omega_F|\,k^{2T}\le 2\,|\{\omega\in\Omega_F:\text{all classes MSTD}\}|\,k^{2T}.$$

Shifting positions by $1$ identifies colourings of $\{0,\dots,N\}$ with colourings of $\{1,\dots,r\}$ and translates each colour class by $1$. Translation preserves both $|A-A|$ and $|A+A|$, since $(A+1)+(A+1)=(A+A)+2$. So every colouring counted on the right is good for $\{1,\dots,r\}$, which gives $k^r\le D\cdot\#\text{good colourings}$. ∎

**Proof of Theorem B.**

*Ranks of blocks.* Order the blocks of a partition $P$ of $\{1,\dots,r\}$ by their least elements. Let $\mathrm{rank}_P(t)$ be the number of blocks whose least element is smaller than that of $t$.
* Two distinct blocks have distinct least elements, because blocks are disjoint.
* So $\mathrm{rank}_P$ is injective on the blocks.
* Its values are smaller than the number of blocks.

*(i) There are at most $k^r$ partitions into exactly $k$ blocks.* Map $P$ to the colouring $x\mapsto\mathrm{rank}_P(\text{block of }x)\in\{0,\dots,k-1\}$. Two elements get the same colour exactly when they are in the same block, so $P$ is recovered from its colouring. The map is injective into the $k^r$ colourings.

*(ii) There are at most $k^k$ times as many good colourings as good partitions.*
* A good colouring $c$ is surjective, because the empty set is not MSTD: $0<0$ fails.
* So its colour classes form a partition $P_c$ into exactly $k$ nonempty blocks, all MSTD. That is, $P_c$ is a good partition.
* The map $c\mapsto(P_c,(\mathrm{rank}_{P_c}(c^{-1}(i)))_{i\in[k]})$ goes into (good partitions) $\times\{0,\dots,k-1\}^k$.
* It is injective. The pair determines each colour class $c^{-1}(i)$, as the unique block of $P_c$ with the given rank, and hence determines $c$.

*Combining.* With $D$ and $R$ from Theorem A, for $r\ge R$:
$$\#\text{partitions}\le k^r\le D\cdot\#\text{good colourings}\le Dk^k\cdot\#\text{good partitions}.$$
Theorem A also gives at least one good colouring, so at least one good partition, and the proportion is at least $1/(Dk^k)$. ∎

## 8. Numerical checks

All scripts are in [scripts/](scripts/) with logs. None of them is a premise of any proof.

**Counting lemmas before formalization.** [check_counting.py](../shard007-formal-paper-331690-340121-opus-20261119-r1/340121/scripts/check_counting.py) ([log](../shard007-formal-paper-331690-340121-opus-20261119-r1/340121/scripts/check_counting.log)) checked the following by brute force.
* Lemmas 1–2 on 200 random free sets.
* Lemma 3 for $(k,c)\in\{(2,1),(3,1),(2,2),(3,2)\}$ and $n\le2$.
* Lemma 4 for four $(q,g)$ and $n\le3$.
* The fringe count of Lemma 7.
* The exact bad fraction in Lemma 5's model for tiny $(k,h)$, against $b^m$:

| $k$ | $h$ | worst bad fraction | bound $(1-1/k^2)^m$ |
|---|---:|---:|---:|
| 2 | 3 | 1/2 | 3/4 |
| 2 | 5 | 1/4 | 9/16 |
| 3 | 3 | 7/9 | 8/9 |
| 3 | 5 | 49/81 | 64/81 |

* The partition step: the number of good colourings equals $k!$ times the number of good partitions, which is at most $k^k$ times. MSTD blocks need $r\ge 20$ for $k=2$, so this check also used the stand-in predicate $|A+A|\ge2|A|$. Example rows as $(r,k,\#\text{partitions},\#\text{good partitions},\#\text{good colourings})$: $(8,2,127,72,144)$ and $(9,3,3025,144,864)$.

**The construction on actual intervals.** [check_interval.py](../shard007-formal-paper-331690-340121-opus-20261119-r1/340121/scripts/check_interval.py) ([log](../shard007-formal-paper-331690-340121-opus-20261119-r1/340121/scripts/check_interval.log)) used modular colourings in the form of Lemma 5, found by random search: $k=2$ with $h=7$, and $k=3$ with $h=27$. It took $Q=p$ and $T=Qp$, built the fringes, sampled random middles, and asserted every containment of Lemmas 9, 10, 12 and 13.

| $k$ | $h$ | $p$ | $T$ | $N$ | classes MSTD / classes sampled |
|---|---:|---:|---:|---:|---:|
| 2 | 7 | 14 | 196 | 784, 791, 885 | 12/12 at each $N$ |
| 3 | 27 | 54 | 2916 | 11664, 11677 | 6/6 at each $N$ |

**Constants produced by the proof's conditions.** [constants.py](../shard007-formal-paper-331690-340121-opus-20261119-r1/340121/scripts/constants.py) ([log](../shard007-formal-paper-331690-340121-opus-20261119-r1/340121/scripts/constants.log)) lists, for each $k$:
* $m$, the least value satisfying Lemma 6, with $h=2m+1$;
* $Q$, the least $Q\ge p$ satisfying (★);
* $T=Qp$ and $R=4T+1$;
* $\log_{10}D$ for $D=2k^{2T}$.

The Lean proof obtains *some* valid $m$ and $Q$ from limits and does not compute them.

| $k$ | $m$ | $h$ | $p$ | $Q$ | $T$ | $R$ | $\log_{10}D$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| 2 | 18 | 37 | 74 | 82 | 6068 | 24273 | 3654 |
| 3 | 56 | 113 | 226 | 235 | 53110 | 212441 | 50680 |
| 4 | 117 | 235 | 470 | 477 | 224190 | 896761 | 269952 |
| 5 | 204 | 409 | 818 | 818 | 669124 | 2676497 | 935396 |

The values of $h$ agree with the independent reviewer's computation (37, 113, 235, 409). The constants are astronomically weak. The theorem is about positivity, not about good constants.

## 9. Formal verification

### 9.1 Setting

The formalization uses Lean 4.34.1 and Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. There are ten modules, listed in import order in [LEAN-SOURCE-APPENDIX.md](../shard007-formal-paper-331690-340121-opus-20261119-r1/340121/LEAN-SOURCE-APPENDIX.md).

* `MSTD A` is `(A - A).card < (A + A).card`, with Mathlib's pointwise `Finset` operations on `ℤ`.
* `cls c i` is the class of colour `i` of `c : Fin r → Fin k`, placed on $\{1,\dots,r\}$ by `j ↦ j + 1`.
* `goodColourings r k` is the set of `c` all of whose classes are MSTD.
* `allPartitions r k` and `goodPartitions r k` filter Mathlib's `Finpartition (univ : Finset (Fin r))` by `parts.card = k`. For good partitions every part, placed on $\{1,\dots,r\}$, must be MSTD. Mathlib's `Finpartition` forbids empty parts, so these are exactly the $k$-decompositions.

### 9.2 Map from the proof to Lean

| Step | Lean declaration (module) |
|---|---|
| Freeness, Lemmas 1–4 | `Free`, `card_filter_mem_mul`, `card_filter_pair`, `card_iter_pair`, `card_iter_single` (MstdCount) |
| Definitions, translation invariance | `MSTD`, `cls`, `goodColourings`, `place`, `allPartitions`, `goodPartitions`, `Conjecture15`, `Conjecture15Count`, `LabelledPositiveProportion`, `mstd_image_add_iff` (MstdDefs) |
| Lemma 6, Lemma 5 | `exists_good_m`, `bad_count`, `card_pi2`, `card_sel_filter`, `colOf_congr`, `colOf_antipodal`, `exists_modular` (MstdModular) |
| Positions, classes, Lemmas 7–11 | `pt`, `cl`, `Omega`, `omega_left`, `omega_right`, `omega_free`, `omega_card`, `residue_in_interval`, `det_low`, `card_sub_cl_le`, `card_add_ge` (MstdInterval) |
| Lemmas 12, 13 | `trans_bad`, `mid_bad` (MstdEvents) |
| Lemma 14 | `rev`, `rev_pt`, `rev_injective`, `mem_cl_rev`, `mem_add_cl_rev`, `rev_mem_omega` (MstdReflect) |
| $\rho$, $W$, Lemmas 15, 16 | `rho`, `rho_facts`, `nat_to_frac`, `W`, `low_bad_le`, `sum_W_le` (MstdUnion) |
| Proposition 17, Lemma 18, Theorem A | `half_good`, `exists_Q`, `cls_eq_image`, `labelled_positive_proportion` (MstdMain) |
| Theorem B | `rank`, `rank_lt`, `rank_injOn`, `rankColouring`, `card_allPartitions_le`, `toPartition`, `toPartition_parts`, `surjective_of_good`, `toPartition_good`, `card_goodColourings_le`, `conjecture15Count`, `conjecture15` (MstdPartition) |
| Reviewer's endpoint forms, definitions unfolded | `mathdb_340121_labelled`, `mathdb_340121` (MstdAxioms) |

**Differences between the Lean route and the discovery write-up [PROOF].** The proof in Sections 4–7 is the one formalized. Compared with [PROOF] it differs as follows; none of the differences shrinks the range.

1. The modular colouring is built from $\omega:\mathbb Z/h\to\Pi$ via residue mod $h$ and parity. By the Chinese remainder theorem this is the same as colouring the antipodal pairs of $\mathbb Z/2h$.
2. A single ratio $\rho=1-1/(2k^2)$ bounds both the transition factor $(k-1)/k$ and the middle factor $\sqrt{(k^2-1)/k^2}$. Condition (★) replaces [PROOF]'s condition $2k(T+p)a^{T/p-1}+4k^3b^{\lfloor T/2\rfloor}<1/2$.
3. The middle uses $\lfloor(s-2T)/2\rfloor$ pairs starting at $T$, instead of $\lceil(s-2T)/2\rceil$.
4. The upper end is handled by reflecting the colouring into a second fringe set $\Omega_{F'}$, not by reflecting the probability space.
5. $m$ and $Q$ are obtained from limits, not from explicit inequalities.
6. The partition step uses the injection into partitions × rank vectors, with factor $k^k$, instead of the exact $k!$-to-one fibre count. Theorem B's constant is therefore $Dk^k$ rather than $D\,k!$.
7. All probabilistic statements are replaced by the exact counts of Section 4.

**The conjecture as `Prop`s.**
* `Conjecture15` is the proportion form: $\exists c>0\ \exists R\ \forall r\ge R$, $c\le\#\text{good}/\#\text{all}$, in $\mathbb Q$.
* `Conjecture15Count` is the counting form: $\#\text{all}\le D\cdot\#\text{good}$.
* `LabelledPositiveProportion` is Theorem A.

All three are proved for every `k ≥ 2`. The endpoints `mathdb_340121_labelled` and `mathdb_340121` restate the reviewer's required forms with every definition unfolded to Mathlib notions.

### 9.3 Endpoint statements and axioms

The following is the output of compiling `MstdAxioms.lean` in the clean rebuild, verbatim from `final-compile-MstdAxioms.output.txt` without its trailing JSON receipt line:

```text
def Mstd340121.MSTD : Finset ℤ → Prop :=
fun A => #(A - A) < #(A + A)
def Mstd340121.cls : {r k : ℕ} → (Fin r → Fin k) → Fin k → Finset ℤ :=
fun {r k} c i => image (fun j => ↑↑j + 1) {j | c j = i}
def Mstd340121.goodColourings : (r k : ℕ) → Finset (Fin r → Fin k) :=
fun r k => {c | ∀ (i : Fin k), MSTD (cls c i)}
def Mstd340121.place : {r : ℕ} → Finset (Fin r) → Finset ℤ :=
fun {r} s => image (fun j => ↑↑j + 1) s
def Mstd340121.allPartitions : (r : ℕ) → ℕ → Finset (Finpartition univ) :=
fun r k => {P | #P.parts = k}
def Mstd340121.goodPartitions : (r : ℕ) → ℕ → Finset (Finpartition univ) :=
fun r k => {P | #P.parts = k ∧ ∀ s ∈ P.parts, MSTD (place s)}
def Mstd340121.Conjecture15 : Prop :=
∀ (k : ℕ), 2 ≤ k → ∃ c, 0 < c ∧ ∃ R, ∀ (r : ℕ), R ≤ r → c ≤ ↑(#(goodPartitions r k)) / ↑(#(allPartitions r k))
def Mstd340121.Conjecture15Count : Prop :=
∀ (k : ℕ), 2 ≤ k → ∃ D R, 0 < D ∧ ∀ (r : ℕ), R ≤ r → #(allPartitions r k) ≤ D * #(goodPartitions r k)
def Mstd340121.LabelledPositiveProportion : Prop :=
∀ (k : ℕ), 2 ≤ k → ∃ D R, 0 < D ∧ ∀ (r : ℕ), R ≤ r → k ^ r ≤ D * #(goodColourings r k)
@exists_modular : ∀ {k : ℕ},
  2 ≤ k →
    ∃ h,
      Odd h ∧
        ∃ F,
          (∀ (x y : ℤ), x ≡ y [ZMOD ↑(2 * h)] → F x = F y) ∧
            (∀ (x : ℤ), F (x + ↑h) ≠ F x) ∧ ∀ (i : Fin k) (s : ℤ), ∃ u, F u = i ∧ F (s - u) = i
@card_iter_pair : ∀ {I : Type u_1} {β : Type u_2} [inst : DecidableEq I] [Fintype I] [inst_2 : Fintype β]
  [inst_3 : DecidableEq β] (k c : ℕ),
  Fintype.card β = k * c →
    0 < c →
      1 ≤ k →
        ∀ (S : Finset (I → β)) (n : ℕ) (X Y : ℕ → I) (G G' : ℕ → Finset β),
          (∀ (j : ℕ), #(G j) = c) →
            (∀ (j : ℕ), #(G' j) = c) →
              (∀ j < n, ∀ j' < n, X j ≠ Y j') →
                (∀ j < n, ∀ j' < n, j ≠ j' → X j ≠ X j') →
                  (∀ j < n, ∀ j' < n, j ≠ j' → Y j ≠ Y j') →
                    (∀ j < n, Free S (X j)) →
                      (∀ j < n, Free S (Y j)) →
                        #({ω ∈ S | ∀ j < n, ¬(ω (X j) ∈ G j ∧ ω (Y j) ∈ G' j)}) * k ^ (2 * n) = #S * (k ^ 2 - 1) ^ n
@card_iter_single : ∀ {I : Type u_1} {β : Type u_2} [inst : DecidableEq I] [Fintype I] [inst_2 : Fintype β]
  [inst_3 : DecidableEq β] (q g : ℕ),
  Fintype.card β = q →
    ∀ (S : Finset (I → β)) (n : ℕ) (X : ℕ → I) (G : ℕ → Finset β),
      (∀ (j : ℕ), #(G j) = g) →
        (∀ j < n, ∀ j' < n, j ≠ j' → X j ≠ X j') →
          (∀ j < n, Free S (X j)) → #({ω ∈ S | ∀ j < n, ω (X j) ∈ G j}) * q ^ n = #S * g ^ n
@card_sub_cl_le : ∀ {k N T Q h : ℕ} (F : ℤ → Fin k),
  0 < h →
    T = Q * (2 * h) →
      2 * T ≤ N →
        (∀ (x y : ℤ), x ≡ y [ZMOD ↑(2 * h)] → F x = F y) →
          (∀ (x : ℤ), F (x + ↑h) ≠ F x) → ∀ ω ∈ Omega N T F, ∀ (i : Fin k), #(cl ω i - cl ω i) + 2 * Q ≤ 2 * N + 1
@det_low : ∀ {k N T p : ℕ} (G : ℤ → Fin k),
  0 < p →
    p ≤ T →
      T ≤ N →
        (∀ (x y : ℤ), x ≡ y [ZMOD ↑p] → G x = G y) →
          (∀ (i : Fin k) (s : ℤ), ∃ u, G u = i ∧ G (s - u) = i) →
            ∀ (ω : Fin (N + 1) → Fin k),
              (∀ n < T, ω (pt N n) = G ↑n) → ∀ (i : Fin k) (s : ℕ), p ≤ s + 1 → s + p + 1 ≤ 2 * T → ↑s ∈ cl ω i + cl ω i
@trans_bad : ∀ {k N T p Q : ℕ} (G : ℤ → Fin k),
  0 < p →
    T = Q * p →
      4 * T ≤ N →
        (∀ (x y : ℤ), x ≡ y [ZMOD ↑p] → G x = G y) →
          (∀ (i : Fin k) (s : ℤ), ∃ u, G u = i ∧ G (s - u) = i) →
            ∀ (S : Finset (Fin (N + 1) → Fin k)),
              (∀ ω ∈ S, ∀ n < T, ω (pt N n) = G ↑n) →
                (∀ (n : ℕ), T ≤ n → n + T ≤ N → Free S (pt N n)) →
                  ∀ (i : Fin k) (s : ℕ),
                    2 * T ≤ s + p → s < 3 * T → #({ω ∈ S | ↑s ∉ cl ω i + cl ω i}) * k ^ (Q - 1) ≤ #S * (k - 1) ^ (Q - 1)
@mid_bad : ∀ {k N T : ℕ},
  1 ≤ k →
    ∀ (S : Finset (Fin (N + 1) → Fin k)),
      (∀ (n : ℕ), T ≤ n → n + T ≤ N → Free S (pt N n)) →
        ∀ (i : Fin k) (s : ℕ),
          3 * T ≤ s →
            s ≤ N →
              #({ω ∈ S | ↑s ∉ cl ω i + cl ω i}) * k ^ (2 * ((s - 2 * T) / 2)) ≤ #S * (k ^ 2 - 1) ^ ((s - 2 * T) / 2)
@half_good : ∀ {k N T Q h : ℕ},
  2 ≤ k →
    ∀ (F : ℤ → Fin k),
      0 < h →
        (∀ (x y : ℤ), x ≡ y [ZMOD ↑(2 * h)] → F x = F y) →
          (∀ (x : ℤ), F (x + ↑h) ≠ F x) →
            (∀ (i : Fin k) (s : ℤ), ∃ u, F u = i ∧ F (s - u) = i) →
              2 * h ≤ Q →
                T = Q * (2 * h) →
                  4 * T ≤ N →
                    2 * ↑k * (↑(T + 2 * h) * rho k ^ (Q - 1) + 2 * ↑k ^ 2 * rho k ^ (T - 1)) ≤ 1 / 2 →
                      #(Omega N T F) ≤ 2 * #({ω ∈ Omega N T F | ∀ (i : Fin k), MSTD (cl ω i)})
@card_allPartitions_le : ∀ {r k : ℕ}, 1 ≤ k → #(allPartitions r k) ≤ k ^ r
@card_goodColourings_le : ∀ {r k : ℕ}, #(goodColourings r k) ≤ k ^ k * #(goodPartitions r k)
labelled_positive_proportion : LabelledPositiveProportion
conjecture15Count : Conjecture15Count
conjecture15 : Conjecture15
mathdb_340121_labelled : ∀ (k : ℕ),
  2 ≤ k →
    ∃ D R,
      0 < D ∧
        ∀ (r : ℕ),
          R ≤ r →
            k ^ r ≤
              D *
                #{c |
                    ∀ (i : Fin k),
                      #(image (fun j => ↑↑j + 1) {j | c j = i} - image (fun j => ↑↑j + 1) {j | c j = i}) <
                        #(image (fun j => ↑↑j + 1) {j | c j = i} + image (fun j => ↑↑j + 1) {j | c j = i})}
mathdb_340121 : ∀ (k : ℕ),
  2 ≤ k →
    ∃ D R,
      0 < D ∧
        ∀ (r : ℕ),
          R ≤ r →
            #{P | #P.parts = k} ≤
              D *
                #{P |
                    #P.parts = k ∧
                      ∀ s ∈ P.parts,
                        #(image (fun j => ↑↑j + 1) s - image (fun j => ↑↑j + 1) s) <
                          #(image (fun j => ↑↑j + 1) s + image (fun j => ↑↑j + 1) s)}
'Mstd340121.exists_modular' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mstd340121.half_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mstd340121.labelled_positive_proportion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mstd340121.conjecture15Count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mstd340121.conjecture15' depends on axioms: [propext, Classical.choice, Quot.sound]
'mathdb_340121_labelled' depends on axioms: [propext, Classical.choice, Quot.sound]
'mathdb_340121' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`. The sources contain no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `bv_decide`, `implemented_by` or `decide`.

### 9.4 Build

All ten modules were compiled from an empty build directory and then kernel-checked with `leanchecker`. Each module was one run under 120 s CPU, 6 GiB resident memory and 32 GiB address space, on CPUs 28–29. All twenty runs exited with status 0. See [REPORT.md](../shard007-formal-paper-331690-340121-opus-20261119-r1/340121/REPORT.md) and [final-rebuild.log](../shard007-formal-paper-331690-340121-opus-20261119-r1/340121/final-rebuild.log).

## 10. Limits

* **Literature search was bounded.**
  * The discovery lane and the independent reviewer searched with degraded tools. The reviewer had no web search, because of an account usage limit, and Semantic Scholar and OpenAlex were partly rate-limited.
  * The reviewer checked the citation graph of the source (OpenAlex: 4 citing works; Semantic Scholar: 2 more) and ran Crossref keyword searches. They found no proof of Conjecture 1.5 for $k\ge3$.
  * The final referee searched 2019–2026 work on MSTD decompositions, including Chu and Miller and coauthors, and inspected the MathDB-linked ProbXiv entry. The referee found no proof of this conjecture for $k\ge3$, and the [ProbXiv entry](https://probxiv.com/problems/positive-proportion-conjecture-for-partitions-into-mstd-subsets) was open with no visible contribution. The search was bounded.
  * I did not run new keyword searches; I checked Crossref metadata for [Z1] and [MO].
* **Unread versions and papers.**
  * I read arXiv v1 and v2 of the source. The final referee also checked the conjecture in [INTEGERS 19 (2019), #A60](https://math.colgate.edu/~integers/t60/t60.pdf). The sufficient condition is numbered Theorem A.4 in arXiv v1, B.4 in arXiv v2 and 4.4 in the journal.
  * I read the arXiv v2 of [AMMS] (Theorem 1.4 and §6 statements), not the IJNT version.
  * I did not read [MO], [Z2], [HM] or [Z1]. Their results are cited as the source and [AMMS] state them.
  * [HDM] was read only at title and abstract level.
* **AI-produced.** The proof was found and written by AI systems. The discovery write-up came from an AI discovery lane of this campaign, the review from Claude Opus, and this formalization and paper from Claude Opus. There has been no human peer review. The Lean proof is the strongest check of correctness available.

## References

* [CLMS] Hùng Viê.t Chu, Noah Luntzlara, Steven J. Miller and Lily Shao, *Infinite families of partitions into MSTD subsets*, arXiv:1808.05460 (2018, v2 2019); INTEGERS 19 (2019).
* [AMMS] Megumi Asada, Sarah Manski, Steven J. Miller and Hong Suh, *Fringe pairs in generalized MSTD sets*, Int. J. Number Theory 13 (2017) 2653–2675; arXiv:1509.01657.
* [MO] Greg Martin and Kevin O'Bryant, *Many sets have more sums than differences*, in Additive Combinatorics, CRM Proceedings and Lecture Notes 43, Amer. Math. Soc., 2007, 287–305, doi:10.1090/crmp/043/16.
* [Z1] Yufei Zhao, *Counting MSTD sets in finite abelian groups*, J. Number Theory 130 (2010) 2308–2322, doi:10.1016/j.jnt.2010.06.001; arXiv:0911.2288.
* [Z2] Yufei Zhao, *Sets characterized by missing sums and differences*, J. Number Theory 131 (2011) 2107–2134; arXiv:0911.2292.
* [HM] Peter V. Hegarty and Steven J. Miller, *When almost all sets are difference dominated*, Random Structures Algorithms 35 (2009) 118–136.
* [HDM] Frank He, Karol Daniewski and Steven J. Miller, *Generating and generalizing MSTD sets through Markov processes*, arXiv:2610.08394 (2026).
* [PROOF] Discovery write-up `fresh-shard007-discovery-sol62-20261118-r1/PROOF-340121.md` and independent review `shard007-candidates-review-opus-20261118-r1/REVIEW-340121.md` in this campaign.
