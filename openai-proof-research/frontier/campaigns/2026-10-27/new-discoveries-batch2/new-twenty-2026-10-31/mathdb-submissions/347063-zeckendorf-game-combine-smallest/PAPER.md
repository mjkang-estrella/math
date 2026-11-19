# The Combine Smallest Zeckendorf game and its linear growth constant

## Abstract

For the Combine Smallest strategy of Li, Li, Miller, Mizgerd, Sun, Xia and Zhou, the number of moves from $n$ ones is
$$
\mathrm{CS}(n)=cn+O(\sqrt n\log n),\qquad
c=\frac52-\varphi+\sum_{j\ge2}\frac1{F_{2j}}
  =1.2064811686\ldots ,
$$
where $F_1=1, F_2=2$ and $\varphi=(1+\sqrt{5})/2$. This resolves the Combine Smallest half of Conjecture 1.4 of *Deterministic Zeckendorf Games* [1]. We give a written proof using the integer counter and chain of even levels used in the Lean endpoint proof. The published Split Smallest half, due to Cusenza et al. [2], is included with attribution.

## 1. Game and statement

Baird-Smith, Epstein, Flint and Miller introduced the underlying game [3]. We use Definition 1.1 and the deterministic priorities of §1.2 of Li et al. [1]. Set $F_0=1, F_1=1, F_{i+1}=F_i+F_{i-1}$ for $i\ge1$. Index $0$ is auxiliary. A position $a=(a_i)_{i\ge1}$ consists of finitely many chips at positive indices, with $a_i$ chips of value $F_i$. Write $e_i$ for one chip at $i$, $N(a)=\sum_i a_i F_i$ for value, and $T(a)=\sum_i a_i$ for chip count. A move replaces the two indicated inputs, requiring both copies when the inputs coincide.

| Move | Inputs | Outputs |
|---|---|---|
| $C_1$ | $1,1$ | $2$ |
| $C_k$, $k\ge2$ | $k-1,k$ | $k+1$ |
| $S_2$ | $2,2$ | $1,3$ |
| $S_k$, $k\ge3$ | $k,k$ | $k-2,k+1$ |

The entries are indices. The Fibonacci recurrence gives conservation of $N$, including $2F_2=F_1+F_3$ and $2F_k=F_{k-2}+F_{k+1}$ for $k\ge3$. Combines decrease $T$ by one, and splits preserve $T$.

**Lemma 1.1 (low positions and terminality).** Call a position *quiet* if it has at most one chip per site and no adjacent occupied sites. The quiet positions supported on $[1,t]$ represent each integer in $[0,F_{t+1}-1]$ exactly once, for every $t\ge0$. Their chip counts are at most $\lceil t/2\rceil$. A position is terminal exactly when it is quiet.

*Proof.* For $t=0$ only the empty position occurs, and for $t=1$ the values are $0,1$. For $t\ge2$, positions omitting $t$ represent $[0,F_t-1]$ by induction. Those using $t$ omit $t-1$ and represent $[F_t,F_t+F_{t-1}-1]$, again uniquely by induction. These disjoint intervals give the result. For the count, pair sites $(1,2),(3,4),\ldots$, allowing at most one chip per pair and one in the final unpaired site. A repeat makes $C_1$ or a split legal, and adjacency makes a consecutive combine legal. These are all the moves. $\square$

Write $Z(x)$ for the unique quiet position of value $x$, the Zeckendorf decomposition. Existence follows by taking $t$ large, and uniqueness follows by taking $t$ containing the supports of both proposed representations.

A complete play from $n e_1$ continues whenever there is a legal move. Section 2 proves that it terminates, so its length is the number of moves to $Z(n)$. Combine Smallest (CS) takes $C_1$ first if legal, then the smallest legal $C_k$ for $k\ge2$ if any, then the smallest legal $S_k$. Split Smallest (SS) takes the smallest legal $S_k$ first if any, then $C_1$ if legal, then the smallest legal $C_k$ for $k\ge2$. Write $\mathrm{CS}(n)$ and $\mathrm{SS}(n)$ for their lengths.

**Theorem A (Cusenza et al. [2]).** There is an absolute $C$ such that for every integer $n\ge2$,
$$
 \big|\mathrm{SS}(n)-\varphi^2n\big|\le C(\log n)^2.
$$

**Theorem B.** With $c$ as in the abstract, there is an absolute $C$ such that for every integer $n\ge2$,
$$
 \big|\mathrm{CS}(n)-cn\big|\le C\sqrt n\log n.
$$
The reciprocal series converges, and $1.206<c<1.207$. Here and below $\log$ is natural.

The source's Conjecture 1.4 predicts a limiting length per chip of $\varphi^2$ for SS and approximately $1.206$ for CS. The general order of growth was already known from the all-play bounds of [1, Theorem 1.2]. The contribution here is the source's Combine Smallest assertion from $n e_1$, with the exact constant and an error estimate. Section 2 includes the published Split Smallest result with attribution. No earlier proof of the Combine Smallest asymptotic was found in the campaign's bounded search of the named strategies and the follow-up literature examined. That search did not sweep citation indexes or the wider rewriting literature.

The supplied MathDB record 347063 says the game starts from the Zeckendorf decomposition of $n$. Such a position is terminal by Lemma 1.1 and gives zero moves for every $n$. Theorems A and B use the source's start of $n$ ones.

## 2. The potential and the attributed Split Smallest estimate

Let $\psi=-1/\varphi=1-\varphi$, $w_i=i+2+\psi^i/\varphi$, and $\Phi(a)=\sum_i a_i w_i$. We have $w_1=\varphi^2$ and $i+1<w_i<i+3$, since $1/\varphi<1$ and $|\psi|<1$.

**Lemma 2.1 (drops and remaining length).** The drop in $\Phi$, old minus new, is $1$ on $C_1$ and on every split, and $k$ on $C_k$, $k\ge2$. From any position $a$ supported on $[1,B]$, every continuation has length at most $\Phi(a)\le (B+3)T(a)$.

*Proof.* Split the drop into the contribution of $i+2$ and that of $\psi^i/\varphi$. Substitution into the move table gives
$$
\begin{array}{c|r|l}
 & i+2 & \psi^i/\varphi\\ \hline
 C_1 &2 &(2\psi-\psi^2)/\varphi=-1\\
 C_k (k\ge2)&k&\psi^{k-1}(1+\psi-\psi^2)/\varphi=0\\
 S_2&0&(2\psi^2-\psi-\psi^3)/\varphi=1\\
 S_k (k\ge3)&1&\psi^{k-2}(2\psi^2-1-\psi^3)/\varphi=0 .
\end{array}
$$
Here $\psi^2=1+\psi, \psi^3=1+2\psi$ and $1-\psi=\varphi$. Each move spends at least one unit of the nonnegative potential, including at the empty position, so any continuation is finite and the first bound follows. The second bound holds term by term. Thus every complete play ends at $Z(n)$ by Lemma 1.1. $\square$

**Remark 2.2.** The affine part is the index sum plus twice the chip count, whose contribution drops by $2$ per combine. The conjugate part has drop $-1$ on $C_1$ and $+1$ on $S_2$. For a complete play from $n e_1$, its initial value is $-n/\varphi^2$ and its final value has magnitude at most $\sum_{i\ge1}|\psi|^i/\varphi=1$, by squarefreeness. Consequently the number of $C_1$'s minus the number of $S_2$'s differs from $n/\varphi^2$ by at most $1$.

**Lemma 2.3 (length identity and index bound).** In any complete play from $n e_1$ of length $L$, let $M_k$ be the number of $C_k$'s. Then
$$
L=\varphi^2n-\Phi(Z(n))-\sum_{k\ge2}(k-1)M_k.
$$
For $n\ge1$, every occupied index during the play is at most $2\log_2 n+1$, with $\log_2 n=\log n/\log 2$.

*Proof.* The first identity is the sum of the drops in Lemma 2.1, with one unit per move and $k-1$ extra for each $C_k$ with $k\ge2$. For the index bound, $F_{i+2}\ge2F_i$ for $i\ge1$, so $F_i\ge 2^{\lfloor i/2\rfloor}$, starting from $F_1=1$ and $F_2=2$. An occupied $i$ has $F_i\le n$ by conservation, whence $i\le2\log_2 n+1$. $\square$

**Proof of Theorem A (attributed).** The length identity is the identity of Cusenza et al. [2, §3], here derived from the weights above. Cusenza et al. state the leading constant $\varphi^2$ [2, §1]; the explicit $(\log n)^2$ error term follows from their identity by the chip count below. Put $B=\lfloor2\log_2 n+1\rfloor$. Immediately before SS first takes a $C_k$ with $k\ge2$, all counts are at most one, since every split and $C_1$ have higher priority. There are then at most $B$ chips. Each subsequent combine decreases the nonincreasing chip count, so at most $B$ combines with $k\ge2$ occur in all. If there is no such first combine the weighted sum is zero. Thus the deficit in Lemma 2.3 lies between $0$ and $B(B+3)+B(B-1)$, since the final position also has at most $B$ chips. This proves the estimate. $\square$

## 3. Insertion and the integer counter

All transitions from now on are in CS unless explicitly described as an isolated insertion.

**Lemma 3.1 (isolated insertion).** For even $q\ge2$ and $0\le x<F_{q+1}$, start at $Z(x)+e_q$. At each step before the position is quiet there is exactly one legal move. Every move has even index at most $q$, and the sequence ends at $Z(x+F_q)$ in at most $q/2$ moves. In particular no intermediate position has two chips at $1$.

*Proof.* Since $x<F_{q+1}$, Lemma 1.1 places $Z(x)$ on $[1,q]$. If neither $q$ nor $q-1$ is occupied in $Z(x)$, the sum is already quiet. If $q-1$ is occupied, write $Z(x)=e_{q-1}+Z(x')$ where the remainder is empty for $q=2$ and has support at most $q-3$ for $q\ge4$ by nonadjacency. The only move is $C_q$. It consumes the chip at $q-1$ and leaves $Z(x')+e_{q+1}$, quiet and of value $x'+F_{q+1}=x+F_q$. This combine can consume the chip at $1$.

If $q$ is occupied, the only move is $S_q$. At $q=2$ the original position $Z(x)$ was $e_2$, and the split leaves $e_1+e_3$, quiet. At $q\ge4$ the split leaves $e_{q+1}$ and the insertion of $e_{q-2}$ into the residual $Z(x-F_q)$, supported at most at $q-2$. Its value is less than $F_{q-1}$ by Lemma 1.1. Inductively the residual moves have index at most $q-2$, and the residual support stays at most $q-1$, since updates produce at most one index higher than the move index. The chip at $q+1$ remains isolated throughout. Thus the residual moves are the only legal moves until the position is quiet. The length bound is $1+(q-2)/2$, and any final split at the base $q=2$ inserts at $1$ into an empty residual state. No step gives a repeat at $1$. Conservation and Lemma 1.1 identify the quiet result. $\square$

**Corollary 3.2 (total split count over insertions).** For even $q\ge2$, the number of splits in Lemma 3.1 summed over $0\le x<F_{q+1}$ is $A(q)=F_q-1$.

*Proof.* At $q=2$, only $x=2$ gives a split, so $A(2)=1=F_2-1$. At $q\ge4$, only $F_q\le x<F_{q+1}$ gives a split. There are $F_{q-1}$ such $x$ and their residual inputs $x-F_q$ run over all inputs at $q-2$. Hence $A(q)=F_{q-1}+A(q-2)=F_q-1$ by induction. $\square$

For a position $a$, define
$$
 d_i=f_{i-1}-[i\text{ even}],\qquad D(a)=\sum_i a_i d_i,\qquad
 \rho=2-\varphi=1/\varphi^2 ,
$$
where $f_0=0, f_1=1, f_{i+2}=f_{i+1}+f_i$ are the usual Fibonacci numbers, $F_i=f_{i+1}$, and brackets denote an indicator.

**Lemma 3.3 (counter).** The increase in $D$ is zero on $C_1$ and on odd-index combines, $1$ on even-index combines and even-index splits, and $-1$ on odd-index splits. For every position,
$$
 |D(a)-\rho N(a)|\le2T(a).
$$
In a segment with only even splits and no $C_1$, its length minus its counter increase equals the number of odd-index combines.

*Proof.* We have $d_1=d_2=0, d_3=1$, giving the $C_1$ and $S_2$ entries. For $C_k, k\ge2$, the $f$-parts cancel by the recurrence, and the indicator contribution is $[k-1\text{ even}]+[k\text{ even}]-[k+1\text{ even}]$, equal to $1$ for even $k$ and $0$ for odd $k$. For $S_k, k\ge3$ the $f$-parts cancel since $2f_{k-1}=f_{k-3}+f_k$. The indicator contribution is $2[k\text{ even}]-[k-2\text{ even}]-[k+1\text{ even}]$, equal to $1$ or $-1$ as claimed. For the approximation, $b_t=f_t-\rho f_{t+2}$ obeys the Fibonacci recurrence with $b_0=-\rho, b_1=1-2\rho=-\rho \psi$ (use $\varphi^2=1+\varphi$). Thus $b_t=-\rho \psi^t$ by induction. Its absolute value is at most $1$, so $|d_i-\rho F_i|\le2$. Sum with the chip multiplicities. The segment formula follows by summing the move increases. $\square$

## 4. Exact transitions at a level

For even $p\ge2$ define the ready position
$$
 B_p(r,m,h)=Z(r)+m e_p+h e_{p+2},\qquad 0\le r<F_{p-1}.
$$
The *pool* $m$ lies at $p$ and the *pile* $h$ at $p+2$. The low part is supported on $[1,p-2]$ by Lemma 1.1, and is empty for $p=2$. In a ready position there are no legal combines. If $m\ge2$ the smallest legal split is $S_p$, which is therefore the next move. If $m\le1$, the position may be relabelled as ready at $p+2$, with low part $Z(r)+m e_p$, pool $h$ and pile zero. This costs no move, even when $h$ can split.

For the transitions at $p\ge4$, let
$$
 S=S_p,\quad L=C_{p-2},\quad T_*=S_{p-2},\quad
 V=C_p,\quad U=C_{p+1},\quad H=C_{p+2},\quad I=C_{p+3}.
$$
Use the following cases for the low part before $S$.

| Case | Condition | Low effect of $S$ and of the indicated low moves |
|---|---|---|
| 1 | $r<F_{p-3}$ | $S$ adds an isolated chip at $p-2$, making a quiet low part of value $u=r+F_{p-2}$. |
| 2 | $F_{p-3}\le r<F_{p-2}$ | $S$ creates adjacency at $p-3,p-2$. $L$ removes that pair and produces one chip at $p-1$. The part at or below $p-2$ is then quiet of value $v=r-F_{p-3}$. |
| 3 | $F_{p-2}\le r<F_{p-1}$ | $S$ doubles site $p-2$. $T_*$ empties it and produces one chip at $p-1$. Its other product initiates the residual insertion $A$ below, after which the part at or below $p-2$ is quiet of value $v=r-F_{p-3}$. |

The ranges follow from Lemma 1.1 by partitioning according to whether $Z(r)$ contains $p-2$, $p-3$, or neither. In Case 3, at $p=4$ the other product of $T_*=S_2$ is a chip at $1$ in an empty residual part, and $A$ is empty. Its value is $F_1=F_2-F_1$. At $p\ge6$, $A$ is the isolated insertion at $q=p-4$ with $x=r-F_{p-2}<F_{p-3}$, as in Lemma 3.1. It has value $r-F_{p-2}+F_{p-4}=v$ after relaxation. Throughout $A$, its support is at most $p-3$, so the chip at $p-1$ cannot interact with it. The high combines $V,U,H,I$ likewise act on sites at least $p-1$. In Case 3 after $T_*$, take a legal residual combine before any high combine, because its index is smaller. When the next low move is a split, available high combines go first. When there are no high combines, the residual split has smaller index than any high split. These priority statements apply until the prescribed high combines and $A$ are done. In particular high splits wait while $A$ is unfinished. Lemma 3.1 gives $|A|\le(p-4)/2$ and all its splits and combines have even index.

**Lemma 4.1 (large-pool macro).** Suppose $m\ge5$. Each row below is a segment of the actual CS play from $B_p(r,m,h)$ to the ready position at $p$ with the listed parameters. In the Case 3 row the braces indicate interleaving of $A$ with the indicated high combines, by the stated priority rule. If $k$ is the segment length and $e$ is its increase in $D$, the last column gives $k-e$.

| Level and case | Moves | New $(r,m,h)$ | $k-e$ |
|---|---|---|---:|
| $p=2$ | $S_2,C_2,C_3,C_3$ | $(0,m-5,h+2)$ | 2 |
| $p\ge4$, 1 | $S,U$ | $(u,m-3,h+1)$ | 1 |
| $p\ge4$, 2 | $S,L,V,U,U$ | $(v,m-5,h+2)$ | 2 |
| $p\ge4$, 3 | $S,U,T_*,\{V,U;A\}$ | $(v,m-5,h+2)$ | 2 |

*Proof.* In all rows the ready condition forces the pool split. At $p=2$ the split creates one chip at $1$ and one at $3$, with $m-2\ge3$ chips at $2$. Thus $C_2$ goes first, giving two chips at $3$ and $m-3$ at $2$, and the two $C_3$'s exhaust site $3$ before any $C_4$ or split. This takes four moves, increases $D$ by two, and consumes five pool chips.

At $p\ge4$ after $S$ there are $m-2$ chips at $p$, one at $p+1$, and $h$ at $p+2$. If $h>0$, $H$ is also legal here, but $U$ is smaller. In Case 1 there is no low move and $U$ clears site $p+1$. In Case 2, $L$ is first, and its product enables $V$ before $U$. After $V$, site $p+1$ holds two chips and site $p$ holds $m-3\ge2$, so both $U$'s go before $H$ or any split. In Case 3 the doubled site first waits for $U$, which clears $p+1$ and leaves $m-3\ge2$ at $p$. Then $T_*$ is the smallest split with no combine legal. Its $p-1$ product enables $V$; $V$ enables $U$ by placing one chip at $p+1$ while at least one chip at $p$ remains. Each high combine is the smallest high combine at its turn. During this pair, the interleaving rule above applies because the residual support is separated from all high inputs and outputs. In particular $A$ can be empty or can start with a combine, in which case that combine precedes $V$. Counting these updates gives the displayed values, with $u<F_{p-1}$ and $0\le v<F_{p-2}$, and every row ends with sites $p\pm1$ empty. All splits used are even and $C_1$ is absent. The last column follows from Lemma 3.3 by counting the $U$'s (or the $C_3$'s for $p=2$). $\square$

**Lemma 4.2 (exit from a small pool).** Suppose the start is $B_p(r,K,M)$ with $0\le K\le4, M\ge4$ and $p$ even. The following tables give a forced segment up to the indicated ready position $B_{p+2}(r',m',h')$. For $p\ge4$ the segment takes at most $7+(p-4)/2$ moves, and for $p=2$ at most six. In both tables $M-4\le m'\le M+1, 0\le h'\le2$, and $0\le k-e\le2$ for length $k$ and counter increase $e$.

| $K$ | Case at $p\ge4$ | Moves | $r'$ | $m'$ | $h'$ |
|---:|---:|---|---|---|---:|
| 0 | all | none | $r$ | $M$ | 0 |
| 1 | all | none | $r+F_p$ | $M$ | 0 |
| 2 | 1 | $S,H,I$ | $u$ | $M-2$ | 1 |
| 2 | 2 | $S,L,H,I$ | $v+F_{p-1}$ | $M-2$ | 1 |
| 2 | 3 | $S,H,I,T_*,A$ | $v+F_{p-1}$ | $M-2$ | 1 |
| 3 | 1 | $S,U$ | $u$ | $M+1$ | 0 |
| 3 | 2 | $S,L,V,H,H,I,I$ | $v$ | $M-4$ | 2 |
| 3 | 3 | $S,U,T_*,A$ | $v+F_{p-1}$ | $M+1$ | 0 |
| 4 | 1 | $S,U$ | $u+F_p$ | $M+1$ | 0 |
| 4 | 2 | $S,L,V,U,H,I$ | $v$ | $M-1$ | 1 |
| 4 | 3 | $S,U,T_*,\{V,H,I;A\}$ | $v$ | $M-1$ | 1 |

| $K$ at $p=2$ | Moves | $r'$ | $m'$ | $h'$ |
|---:|---|---|---|---:|
| 0 | none | $0$ | $M$ | 0 |
| 1 | none | $F_2$ | $M$ | 0 |
| 2 | $S_2,C_4,C_5$ | $1$ | $M-2$ | 1 |
| 3 | $S_2,C_2,C_4,C_4,C_5,C_5$ | $0$ | $M-4$ | 2 |
| 4 | $S_2,C_2,C_3,C_4,C_5$ | $0$ | $M-1$ | 1 |

*Proof.* The rows for $K\le1$ use the ready relabelling. For the others, track the six counts at $p-1,p,p+1,p+2,p+3,p+4$. For $p\ge4$, just after the forced $S$ the counts are $(0,K-2,1,M,0,0)$. The low effects of $L,T_*$ add one to the first count. $V,U,H,I$ each consume one from their respective adjacent pair in this tuple and add one at the next site. To see which high moves run, the following are the three possibilities once the pool is zero and site $p+1$ has $b\in\{0,1,2\}$ chips, with $M_*$ at $p+2$ and no chips at $p+3,p+4$. For $b=0$ there is no high combine. For $b=1,2$ and $M_*\ge2b$, exactly $b$ copies of $H$ clear site $p+1$ into site $p+3$, and then $b$ copies of $I$ clear site $p+3$ into $p+4$. The earlier $H$'s have smaller index than $I$. If both $p+3,p+4$ become occupied, $I$ still has smaller index than $C_{p+4}$. The resulting counts at $p+2,p+4$ are $M_*-2b,b$. All these combines precede any split unless interleaved with a smaller residual combine.

In Case 1 there is no low move. At $K=2$ the zero pool leaves $b=1$ with $M_*=M$. At $K=3,4$ the single $U$ exhausts $p+1$, so the $K-3$ remaining pool chips stay low and the new pool is $M+1$.

In Case 2 the newly legal $L$ is smaller than every high combine and places a chip at $p-1$. At $K=2$ the zero pool leaves that chip low and gives $b=1$ with $M_*=M$. At $K=3,4$, $V$ goes first among the high combines, leaving $K-3$ at $p$ and two at $p+1$. At $K=3$ this gives $b=2, M_*=M$. At $K=4$ a single $U$ empties $p$ and leaves $b=1, M_*=M+1$.

In Case 3 the repeat at $p-2$ awaits a split until there are no combines. At $K=2$ the initial zero pool gives $b=1, M_*=M$, forcing $H,I$ first. At $K=3,4$ the single $U$ clears $p+1$ into $p+2$ before the split and leaves $K-3$ at $p$. In each of these three rows $T_*$ is now the smallest legal split. At $K=2,3$ the pool remains zero and the $p-1$ product stays low while $A$ finishes. At $K=4$ that product enables $V$, which empties the pool and gives $b=1, M_*=M+1$; $H,I$ follow in the high part. After $T_*$ the separation and priority rule for $A$ applies exactly as in the macro. The outputs listed as low are quiet: in the rows with a chip at $p-1$, its lower neighbours are absent because the residual support is at most $p-3$. In Case 1 a retained chip at $p$ is separated from the low part at or below $p-2$. All other low parts are already quiet with support at most $p-2$.

At $p=2$, $S_2$ inserts directly at $p-1=1$, with no other low state. This is the same six-count tuple as after $S,L$ in Case 2. Thus the Case 2 high sequences apply with $p=2$, and the chip at $1$ stays low exactly at $K=2$.

Every listed endpoint leaves sites $p+1$ and $p+3$ empty. Its low support is at most $p$, so Lemma 1.1 gives $r'<F_{p+1}$. The tables show $M-4\le m'\le M+1$ and $h'\le2$. The move bounds count the displayed letters with $|A|\le(p-4)/2$. All splits in these rows are even, and the only odd-index combines are the displayed $U,I$ (or $C_3,C_5$ at $p=2$). Each row has at most two such combines and no $C_1$, so Lemma 3.3 gives the bound on $k-e$. $\square$

## 5. Assembling the levels

**Lemma 5.1 (one level).** From $B_p(r,m,h)$ with $m\ge24, h\le2$, CS reaches $B_{p+2}(r',m',h')$ with $h'\le2$. For the length $k$ of this segment and its counter increase $e$,
$$
 m'-3\le k-e\le m'+6 .
$$

*Proof.* Repeat Lemma 4.1 while the pool is at least five. Each macro consumes between three and five chips from the pool, adds at least one to the pile, and has length minus counter increase equal to its pile gain. The pool strictly decreases until its size is $K\le4$. At that point the pile $M$ satisfies $M-h\ge(m-K)/5\ge4$. The length minus counter increase across these macros is exactly $M-h$. Lemma 4.2 adds between zero and two to that quantity. Since $h\le2$ and $M-4\le m'\le M+1$, the result is at least $M-2\ge m'-3$ and at most $M+2\le m'+6$. This includes level $2$ through its four-move macro. $\square$

**Lemma 5.2 (opening).** For every even $n$, the first $n/2$ moves give $B_2(0,n/2,0)$ and the counter increase is zero. For $n=2s+1\ge5$, the first $s+2$ moves give $B_2(0,s-2,1)$ with counter increase one. For $n=1$ the initial state is terminal, and for $n=3$ the opening is $C_1,C_2$ to the terminal $e_3$.

*Proof.* CS first consumes all pairs of ones by $C_1$, leaving $\lfloor n/2\rfloor$ chips at $2$ and $n\bmod 2$ ones. The even case is already ready. In the odd case, if $s\ge2$, $C_2$ consumes the one and produces a chip at $3$, and $C_3$ takes that chip with a remaining chip at $2$ into $4$. These are the smallest legal combines at their respective turns. The counter changes follow from Lemma 3.3. If $s=0$, only the one remains. If $s=1$, $C_2$ leaves only $e_3$. $\square$

**Lemma 5.3 (mass estimate).** If $B_p(r,m,h)$ has value $n$ and $h\le2$, then
$$
 n/F_p-7\le m\le n/F_p,\qquad T(B_p(r,m,h))\le (p-2)/2+m+h .
$$

*Proof.* The value is $n=r+mF_p+hF_{p+2}$. Since $r<F_{p-1}\le F_p$ and $F_{p+2}=2F_p+F_{p-1}\le3F_p$, the part outside the pool has value at most $7F_p$. The chip count is exactly the sum from the low part, pool and pile, with the low count bounded by Lemma 1.1. $\square$

**Lemma 5.4 (chain).** Suppose $n\ge1000$, $J\ge0$, and $F_{2J+2}^2\le n$. For every $0\le j\le J$, CS reaches a ready position $a^{(j)}$ at level $p=2j+2$ with pile at most two, after $k_j$ moves, and
$$
 \left|k_j-D(a^{(j)})-\left(\frac n2+n\sum_{i=0}^{j-1}\frac1{F_{2i+4}}\right)\right|
 \le16(j+1).
$$
The sum is zero for $j=0$.

*Proof.* At $j=0$ apply Lemma 5.2. The initial counter is zero, and the difference in the bound is zero for even $n$ and $1/2$ for odd $n$. Suppose $j<J$. At $p=2j+2$, Lemma 5.3 gives pool size at least $n/F_p-7\ge \sqrt n-7\ge24$. Thus Lemma 5.1 produces the next ready state with pool $m'$ and pile at most two. By conservation and Lemma 5.3, $0\le n/F_{p+2}-m'\le7$. Lemma 5.1 now puts the increment of $k_j-D(a^{(j)})$ between $n/F_{p+2}-10$ and $n/F_{p+2}+6$. The displayed comparison sum increases by exactly $n/F_{p+2}$. The error grows by at most $10\le16$, proving the induction through arrival at $2J+2$. $\square$

## 6. The coefficient and the remainder

**Lemma 6.1 (series and numerical bound).** For every $j_0\ge2$, the tail $\sum_{j\ge j_0}1/F_{2j}$ is at most $2/F_{2j_0}$. The constant $c$ in Theorem B satisfies $1.206<c<1.207$ and $1.2064811686<c<1.2064811687$.

*Proof.* Since $F_{i+2}\ge2F_i$, comparison with a geometric series gives convergence and the tail bound. For a short bracket, $2.23606^2<5<2.23608^2$ gives $0.88196<5/2-\varphi<0.88197$. The rational sum
$$
 S_8=1/5+1/13+1/34+1/89+1/233+1/610+1/1597
$$
equals $723535294906/2232250643545$, which is strictly between $0.324128$ and $0.324129$. The tail beginning with $1/F_{18}$ is at most $2/4181<0.000479$. Adding the lower bounds gives $c>1.206088$; adding the upper bounds gives $c<1.206578$.

For the finer decimal, take $B=10^{15}$, $a=2236067977499789$, and $S_{32}=\sum_{j=2}^{32}1/F_{2j}$. The integer inequalities $a^2<5B^2<(a+1)^2$ give bounds for $\sqrt{5}$. The Fibonacci recurrence and rational arithmetic give
$$
 0.324515157406<S_{32}<0.324515157408,\qquad
 2/F_{66}<10^{-13}.
$$
For the sum, the recurrence gives $\sum_{j=2}^{32}\lfloor B/F_{2j}\rfloor=324515157406875$, which differs from $BS_{32}$ by less than $31$. For the tail, $F_{66}=44945570212853$. Substitution into $c=2-\sqrt{5}/2+S_{32}+\sum_{j\ge33}1/F_{2j}$ gives the finer bounds. $\square$

**Proof of Theorem B.** For $n\ge1000$, take $J$ maximal with $F_{2J+2}\le \sqrt n$, and set $p=2J+2$. Thus the chain consumes the levels $2,4,\ldots,p-2$ and arrives at $p$. We have $\sqrt n<F_{p+2}\le3F_p$, so Lemma 5.3 bounds the arriving pool by $3\sqrt n$. For $a=a^{(J)}$ write $T_a=T(a)$. The chip bound gives $T_a\le3\sqrt n+(p-2)/2+2$. Every occupied site is at most $2\log_2 n+1$ by conservation and Lemma 2.3, and $p\le2\log_2 n+1$ by $F_p\le n$. Consequently $T_a=O(\sqrt n)$, and by Lemma 2.1 the remaining number of moves is at most $(2\log_2 n+4)T_a$. By Lemma 3.3, the counter at arrival differs from $\rho n$ by at most $2T_a$. The chain error is at most $16(J+1)$. The omitted sum begins at $1/F_{p+2}$, so Lemma 6.1 bounds the omitted contribution to the length by $2n/F_{p+2}<2\sqrt n$. Thus the coefficient is
$$
 \rho+\frac12+\sum_{i\ge0} \frac1{F_{2i+4}}
 =\frac52-\varphi+\sum_{j\ge2}\frac1{F_{2j}},
$$
and the sum of the four error bounds is $O(\sqrt n\log n)$.

For explicit bounds, $\log 2\ge1/2$ by integrating $1/x$ from 1 to 2, and $\log n\le \sqrt n$ since $\log x/\sqrt x$ has maximum $2/e$ for $x\ge1$. The estimates above give $T_a\le7\sqrt n$, $2\log_2 n+4\le12\log n$, and $16(J+1)\le64\log n$. The remaining length, counter, chain and tail bounds therefore sum to at most $180\sqrt n\log n$. For $2\le n<1000$, both $\mathrm{CS}(n)$ and $cn$ lie between $0$ and $3n$, by Lemmas 2.1 and 6.1. Then $3n\le6\sqrt{1000}\sqrt n\log n$. In particular $C=200$ works throughout. $\square$

## 7. Linear functionals on the move set

**Proposition 7.1.** For the full move set, a linear functional with unit drop on every combine has zero drop on every split. A linear functional conserved by every combine is proportional to the value.

*Proof.* If the drops on combines are one, subtract $T(a)$, which already has that drop and is conserved by splits. It remains to classify the functionals conserved by combines. Writing the coefficients of such a functional as $\mu_i$, conservation under $C_1$ gives $\mu_2=2\mu_1$, and conservation under $C_k$ gives $\mu_{k+1}=\mu_{k-1}+\mu_k$. Induction gives $\mu_i=\mu_1F_i$, a multiple of the value, which is conserved on splits as well. In particular there is no linear functional with unit drop on every move of the full move set. $\square$

## 8. Verification

### 8.1 Lean endpoints

The companion [Lean source appendix](LEAN-SOURCE-APPENDIX.md) reproduces the formal development. The three endpoint statements are as follows.

```lean
theorem Zeck.split_smallest_asymptotic :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(SS n : ℝ) - phi ^ 2 * n| ≤ C * (Real.log n) ^ 2

theorem Zeck.combine_smallest_asymptotic :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |(CS n : ℝ) - (5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ)) * n|
        ≤ C * Real.sqrt n * Real.log n

theorem Zeck.combine_constant_bracket :
    (1.206 : ℝ) < 5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ) ∧
      5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ) < 1.207
```

Lean's $F(i)=\mathrm{Nat.fib}(i+1)$ is the paper's $F_i$, and its sum starts at $j=0$, with denominator $F_4$. The ambient `Pos` admits an index-0 coordinate. The source starts and the reachable legal updates only use positive indices. The selectors `stepSS` and `stepCS` implement the priority orders, and `gameLen` gives the least iterate at which no legal move remains. The literal-record controls are `Zeck.CS_zeckendorf_zero` and `Zeck.SS_zeckendorf_zero`.

The independent formal review records a clean extracted replay and an axiom audit of the three endpoints, with only `propext`, `Classical.choice` and `Quot.sound`. That replay uses the pinned Lean and Mathlib dependencies. The written arguments in this revision stand on their own, and the Lean verification is independent confirmation. This revision did not rerun Lean.

| Written result | Related declarations in namespace `Zeck` |
|---|---|
| Lemma 1.1, terminality and low-state estimates | `terminal_le_one`, `noMove_of_zeckendorf`, `Zk.val_lt`, `Zk.chips_le`. The interval enumeration and sharper pair count are written here. |
| Lemmas 2.1 and 2.3, potential and index estimates | `Phi_doA1`, `Phi_doCons`, `Phi_doSplit`, `CSfrom_le_Phi`, `Phi_le_chips_mul`, `SS_deficit`, `idx_bound` |
| Theorem A | `SS_excess_le`, `SS_final_Phi_le`, `SS_estimate`, endpoint `split_smallest_asymptotic` |
| Lemma 3.1, insertion and its use in §4 | `cascade`, `pending`. The bound on isolated insertion length and the summed count of Corollary 3.2 are written here. |
| Lemma 3.3, counter | `d_cons_even`, `d_cons_odd`, `d_split`, `D_approx`. The endpoint uses the even-split equation. |
| Lemmas 4.1 and 4.2, macros and exits | `macro_step`, `macro_step0`, `exit_step`, `exit_step0`. The exit declarations bound the counter-adjusted count by $e\le k\le e+2$ with $e$ variable. The ordered exit tables and length bounds are proved in §4. |
| Lemmas 5.1–5.4, level assembly | `level_step`, `start_phase`, `val_B`, `chips_B`, `chain`. Its index $j$ denotes pool level $2j+2$ and satisfies $j\le J$, with $n\ge1000$ and $F_{2J+2}^2\le n$. It controls $k-e$ using `Ssum j`. |
| Lemma 6.1, coefficient | `aT_summable`, `aT_tail_le`, `combC_bracket`, endpoint `combine_constant_bracket`. The tighter decimal is a separate rational calculation in §6. |
| Theorem B | `CS_large`, `CS_estimate`, endpoint `combine_smallest_asymptotic`. Both proofs use the potential for the remainder and a crude linear bound for $2\le n<1000$, with their own explicit constants. |

The endpoint proof imports the counter and level-chain machinery. The separate module `ZeckRotation` proves rotation and cycle balance for an alternative route. The coefficient in §6 comes directly from the counter density and the next-pool series. Corollary 3.2 and Proposition 7.1 are written side results.

### 8.2 Finite checks

The [verification script](scripts/check.py) simulates Definition 1.1 with the two priority rules of §1. It compares the selected moves and the resulting positions against the written macro and exit tables. It also checks the ledgers, cutoff, and bounds. The [runner](scripts/run-checks.sh) pins the process to CPUs 12–15 and enforces the 30-minute and 8 GB limits. The completed run is recorded in [checks/verification.txt](checks/verification.txt).

| Sections | Coverage |
|---|---|
| §§1–2, 3.3, 7 | All quiet configurations with support bound $0\le t\le18$, all 729 positions with counts $0,1,2$ at sites 1 through 6, and move and coefficient identities through index 200. |
| §§3.1–3.2 | 10,944 isolated insertions, all input values at each even $q=2,\ldots,18$, including the summed split counts. |
| §4 | 125,400 macro and 83,600 exit instances. All low values at each even $p=2,\ldots,18$ were tested with macro pools $5,6,7,12,24,80$ and piles $0,1,2,4,9$, and with every exit pool $0,\ldots,4$ and piles $4,5,6,11$. The run includes the eleven-move exit at $p=14$, $r=376$, $K=M=4$. |
| §5 | 5,238 synthetic whole levels, including boundary low values and pools at the threshold $24$. Full plays test the opening, the level ledger and the chain through the maximal cutoff. |
| §6 | Exact rational comparisons for the two brackets and for all partial tails with $2\le j_0\le j_1\le100$. |
| Theorems A and B | Both complete plays for every $n=0,\ldots,4000$ and for additional inputs up to $200{,}000$, including neighbours of Fibonacci-square cutoffs. The exact input list is in the output. |

The finite checks supplement the proofs. The asymptotic estimates give upper bounds for the errors. The exact size and structure of the errors and the correspondence to historical residual plots are outside these estimates.

## References

1. R. Li, X. Li, S. J. Miller, C. Mizgerd, C. Sun, D. Xia and Z. Zhou, *Deterministic Zeckendorf Games*, Fibonacci Quarterly **58**(5) (2020), 152–157. [arXiv:2006.16457v1](https://arxiv.org/abs/2006.16457v1)
2. A. Cusenza et al., *Bounds on Zeckendorf Games*, Fibonacci Quarterly **60**(1) (2022), 57–71. [arXiv:2009.09510](https://arxiv.org/abs/2009.09510)
3. P. Baird-Smith, A. Epstein, K. Flint and S. J. Miller, *The Zeckendorf Game*. [arXiv:1809.04881](https://arxiv.org/abs/1809.04881)
