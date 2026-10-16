# Candidate: the crossing number of $K_n$ minus an edge

Status: proposed by the research sub-agent; not accepted. Parent review required.
Owned directory: `frontier/campaigns/2026-10-14/fresh-substantial-discovery-r2/`.

## 1. Statement

**Theorem A (Zheng–Lin–Yang–Cui conjecture, 2007).** For every integer $n\ge 2$ and every edge $e$ of $K_n$,
$$
\operatorname{cr}(K_n-e)=Z(n)-\binom{\lfloor (n-1)/2\rfloor}{2}
=\frac14\Big\lfloor\frac{n+2}{2}\Big\rfloor\Big\lfloor\frac{n-1}{2}\Big\rfloor\Big\lfloor\frac{n-3}{2}\Big\rfloor\Big\lfloor\frac{n-4}{2}\Big\rfloor ,
$$
where $Z(n)=\frac14\lfloor n/2\rfloor\lfloor (n-1)/2\rfloor\lfloor (n-2)/2\rfloor\lfloor (n-3)/2\rfloor$ and $\operatorname{cr}$ is the ordinary crossing number (continuous arcs, finitely many crossings). In parity form, for $s\ge 2$,
$$
\operatorname{cr}(K_{2s+1}-e)=\binom{s}{2}^{2}-\binom{s}{2},\qquad
\operatorname{cr}(K_{2s}-e)=\binom{s}{2}\binom{s-1}{2}-\binom{s-1}{2}=\tfrac14(s^2-1)(s-2)^2 .
$$

**Corollary B (Zheng et al. 2007 Conjecture (1.2); Clancy–Haythorpe–Newcombe Conjecture 74).** For all $m\ge 4$ and $n\ge 1$, with $P_n$ the path with $n$ edges (Ouyang–Wang–Huang convention),
$$
\operatorname{cr}(K_m\,\square\,P_n)=\frac14\Big\lfloor\frac{m+1}{2}\Big\rfloor\Big\lfloor\frac{m-1}{2}\Big\rfloor\Big\lfloor\frac{m-2}{2}\Big\rfloor\Big(n\Big\lfloor\frac{m+4}{2}\Big\rfloor+\Big\lfloor\frac{m-4}{2}\Big\rfloor\Big).
$$

Since $\operatorname{Aut}(K_n)$ is edge-transitive, all graphs $K_n-e$ are isomorphic; we fix the missing pair $\{a,b\}$.

### Exactly what is new (bounded novelty claim)

* Given the pinned upstream Harary–Hill theorem (family 165), the **even** case of Theorem A is already implied by Ouyang–Wang–Huang 2014, Theorem 3.2/3.3 (re-verified in §4). Odd $n\le 13$ follows from OWH Theorem 3.1, upstream Harary–Hill and integrality (check G). Odd $n\le 11$ and even $n\le 12$ were published (OWH Thm 3.4).
* The genuinely new content is the **odd case $n=2s+1\ge 15$** (Proposition 3.6 below). It needs a new lower-bound argument: the counting route leaves a deficit of $(s-1)(s-2)/(2(2s+1))$, which is not closed by integrality for any odd $n\ge 15$ (check G, verified to $n=81$, and it is an exact identity).
* Corollary B is then a formal consequence of OWH Corollary 5.1 (the zip-product identity, literature, not re-audited) and Theorem A. It is new for odd $m\ge 13$ (where $m+2\ge 15$ is odd); for even $m$ it was already implied by upstream Harary–Hill + OWH.

## 2. Setting and upstream interfaces used

All upstream labels refer to `preprints/The-crossing-number-of-complete-graphs-September-23-2026/build/main.tex` at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (sha256 `5ae2c607…2301`); see `source-contracts.md` for exact line numbers.

* **U1 (`lem:normalization`, line 850).** For every finite simple graph a minimum ordinary drawing can be chosen polygonal, straight near every vertex and crossing, with no crossings between edges having a common endpoint ("normalized").
* **U2 (`eq:J` line 222 and `lem:cycles` line 231).** For a normalized drawing of a finite simple graph $G$, the skew form $J(e,f)=I(e,f)+\frac12\sum_{w}\sigma_{we}\sigma_{wf}T_w(e,f)$ on the edge space satisfies $J(z,z')=0$ for any two cycles $z,z'$ (the proof explicitly "applies to every finite simple graph").
* **U3 (`lem:weights`, line 362).** For distinct nodes $u_1,\dots,u_N$, $G(t)=\prod(t-u_p)$: $\sum_p A(u_p)/G'(u_p)=0$ when $\deg A\le N-2$.
* **U4 (`lem:detector`, line 443).** For $2s$ distinct real nodes in any prescribed linear order with $S(p,q)=\pm\frac12$, the pairing
  $M(A,B)=\sum_{p,q}S(p,q)\frac{u_p-u_q}{G'(u_p)G'(u_q)}A(u_p,u_q)B(u_p,u_q)$
  is nonsingular on $\mathcal P_{s-1,s-2}\times\mathcal P_{s-2,s-1}$ ($\mathcal P_{\alpha,\beta}$ = polynomials of degree $\le\alpha$ in $u$ and $\le\beta$ in $v$).
* **U5 (`thm:main`, line 117).** $\operatorname{cr}(K_n)=Z(n)$ for all $n\ge 3$.
* **U6 (§`sec:upper`, `prop:upper` line 766).** The endpoint-sum two-page drawing of $K_n$: vertices $0,\dots,n-1$ on a line, edge $ij$ above the spine iff $(i+j)\bmod n<m=\lfloor n/2\rfloor$; its crossings are exactly the same-page pairs with alternating endpoints, and there are $Z(n)$ of them.

U1–U4 are used in the form stated; the K_n-specific Lemmas `lem:tests`, `lem:injectivity`, `prop:odd` are **not** used as black boxes. Their proofs are re-run below with modifications, and every changed step is proved here.

## 3. Lower bound for odd $n=2s+1$

Fix $s\ge 2$, $n=2s+1$, $G=K_n-\{a,b\}$, and a normalized minimum drawing $D$ of $G$ (U1). Form $J=J_G$ (U2) on the edge space of $G$. Extend it to ordered vertex pairs of $K_n$ by $J([ip],[kq])=J_G$ value when $\{i,p\},\{k,q\}\in E(G)$, $[pi]=-[ip]$, $[ii]=0$, and $J=0$ whenever one of the two pairs is $\{a,b\}$. Choose distinct reals $t_1,\dots,t_n$, put $F(t)=\prod_i(t-t_i)$, $w_i=1/F'(t_i)\neq 0$.

Let $\mathcal V=\mathcal P_{n-2,n-2}$ (two variables), and
$$
\mathcal A=\{A\in\mathcal V:\ A(t_a,t_b)=A(t_b,t_a)\}.
$$

**Lemma 3.1 (cycle tests for $K_n-e$).** Let $H(x,u,y,v)$ have degree $\le n-2$ in each variable and satisfy
$$
H(t_a,t_b,y,v)\equiv H(t_b,t_a,y,v),\qquad H(x,u,t_a,t_b)\equiv H(x,u,t_b,t_a)
$$
as polynomials. Then $\sum_{i,p,k,q}J([ip],[kq])\,w_iw_pw_kw_q\,H(t_i,t_p,t_k,t_q)=0$.

*Proof.* (i) *Tensor characterization.* Let $\varphi(A)=A(t_a,t_b)-A(t_b,t_a)$, a nonzero functional on $\mathcal V$ ($\varphi(x)=t_a-t_b$), so $\mathcal A=\ker\varphi$ has codimension one. Pick $e_0\in\mathcal V$ with $\varphi(e_0)=1$ and a basis $e_1,\dots$ of $\mathcal A$. Write $H=\sum_{j,k}c_{jk}e_j(x,u)e_k(y,v)$ (possible since $\mathcal V\otimes\mathcal V=\mathcal P_{n-2}^{\otimes 4}$). Then $H(t_a,t_b,y,v)-H(t_b,t_a,y,v)=(\varphi\otimes\mathrm{id})H=\sum_k c_{0k}e_k(y,v)\equiv0$ gives $c_{0k}=0$; the second hypothesis gives $c_{j0}=0$. Hence $H=\sum_r A_r(x,u)B_r(y,v)$ with all $A_r,B_r\in\mathcal A$.
(ii) *Cycles.* For $A\in\mathcal A$ put $z_A=\sum_{i,p}w_iw_pA(t_i,t_p)[ip]$, a chain on the vertex pairs of $K_n$. The coefficient of the basis edge $[ab]$ is $w_aw_b\varphi(A)=0$, so $z_A$ lies in the edge space of $G$. Its boundary is $\sum_{i,p}w_iw_pA(t_i,t_p)(\mathbf e_p-\mathbf e_i)$, which vanishes for each monomial $x^\alpha u^\beta$, $\alpha,\beta\le n-2$, by U3 (as in upstream `lem:tests`), hence for all $A\in\mathcal V$. So $z_A$ is a cycle of $G$.
(iii) By U2, $J_G(z_A,z_B)=0$; by bilinearity and the zero extension of $J$ on the missing pair, $J_G(z_A,z_B)=\sum_{i,p,k,q}J([ip],[kq])w_iw_pw_kw_qA(t_i,t_p)B(t_k,t_q)$. Summing over $r$ proves the lemma. $\square$

*Remark.* The symmetry hypothesis is necessary in general: check B evaluates a generic product test $A\otimes B$ without it and finds a nonzero sum on every tested drawing.

Let $\mathcal T$ be the set of ordered pairs of **edges of $G$** with no common endpoint and $J\neq0$. Each unordered pair in $\mathcal T$ needs at least one crossing, so
$$
c(D)\ge |\mathcal T|/2. \tag{3.1}
$$

Let $\mathcal S$ be the upstream space: polynomials $P(x,u,y,v)$ of degree $\le s-2$ in each variable, symmetric under $x\leftrightarrow u$ and under $y\leftrightarrow v$; $\dim\mathcal S=\binom s2^2$ (upstream eq:dim). Define
$$
\mathcal S_a=\{P\in\mathcal S: P(t_a,t_b,y,v)\equiv0\},\qquad
\mathcal S_b=\{Q\in\mathcal S: Q(x,u,t_a,t_b)\equiv0\}.
$$

**Lemma 3.2 (dimension).** $\dim\mathcal S_a=\dim\mathcal S_b=\binom s2^2-\binom s2$.

*Proof.* $\rho:P\mapsto P(t_a,t_b,y,v)$ maps $\mathcal S$ into the symmetric polynomials in $(y,v)$ of degree $\le s-2$ in each variable (dimension $\binom s2$). It is onto: a symmetric $q(y,v)$ is the image of $P(x,u,y,v)=q(y,v)\in\mathcal S$. So $\dim\ker\rho=\binom s2^2-\binom s2$. The swap $(x,u)\leftrightarrow(y,v)$ is a linear isomorphism $\mathcal S_a\to\mathcal S_b$. $\square$

Note that by within-pair symmetry, $P\in\mathcal S_a$ also satisfies $P(t_b,t_a,y,v)\equiv0$, and $Q\in\mathcal S_b$ satisfies $Q(x,u,t_b,t_a)\equiv0$.

Let $E:\mathcal S\to\mathbb R^{\mathcal T}$, $E(P)_{(\{i,p\},\{k,q\})}=P(t_i,t_p,t_k,t_q)$ (well defined by the within-pair symmetries).

**Lemma 3.3 (mixed isotropy).** Let $\Delta=(x-u)(y-v)(x-y)(x-v)(u-y)(u-v)$ and $a_\alpha=J([ip],[kq])w_iw_pw_kw_q\Delta(t_i,t_p,t_k,t_q)$ for $\alpha=(\{i,p\},\{k,q\})\in\mathcal T$ (independent of the chosen orientations). Then every $a_\alpha\ne0$ and
$$
\sum_{\alpha\in\mathcal T}a_\alpha E(P)_\alpha E(Q)_\alpha=0\qquad(P\in\mathcal S_a,\ Q\in\mathcal S_b).
$$

*Proof.* $H=PQ\Delta$ has degree $\le 2(s-2)+3=2s-1=n-2$ in each variable. $H(t_a,t_b,y,v)$ and $H(t_b,t_a,y,v)$ vanish identically because $P$ does; $H(x,u,t_a,t_b)$ and $H(x,u,t_b,t_a)$ vanish because $Q$ does. So Lemma 3.1 applies. Terms with a repeated vertex vanish because $\Delta$ does; terms involving the missing pair have $J=0$; the remaining terms are independent edge pairs of $G$, nonzero only on $\mathcal T$. The four endpoint orientations of a pair contribute equally (reversing an edge flips the signs of both $J$ and $\Delta$; $P,Q$ are within-pair symmetric). Divide by four. $a_\alpha\ne0$ because $J\ne0$ on $\mathcal T$, $w_i\ne0$, and the four nodes are distinct. $\square$

**Lemma 3.4 (twisted detector).** Let $2s$ distinct real nodes $u_1,\dots,u_{2s}$ carry any prescribed linear order, and let $c$ be one of them. If $A\in\mathcal P_{s-2,s-2}$ and $M(A,(v-u_c)B')=0$ for every $B'\in\mathcal P_{s-1,s-2}$, then $A=0$.

*Proof.* $M(A,B)$ depends only on the product $AB$, so $M(A,(v-u_c)B')=M(B',\tilde A)$ with $\tilde A=(v-u_c)A\in\mathcal P_{s-2,s-1}$. By U4, $M$ is nonsingular on $\mathcal P_{s-1,s-2}\times\mathcal P_{s-2,s-1}$, so $\tilde A=0$; as $v-u_c\neq0$ in the domain $\mathbb R[u,v]$, $A=0$. $\square$
(Check I confirms the full-rank statement for $s\le5$, random orders, all choices of $c$.)

**Lemma 3.5 (injectivity on $\mathcal S_a$ and $\mathcal S_b$).** $E$ is injective on $\mathcal S_a$ and on $\mathcal S_b$.

*Proof.* *(a) Localization.* Let $P\in\mathcal S_a$ with $E(P)=0$. Use in Lemma 3.1
$$
H=P(x,u,y,v)\,(u-v)(u-y)(v-x)\,U(x)\,(y-t_a)V'(y)\,(v-t_a)B'(u,v),
$$
with $\deg U\le s$, $\deg V'\le s-1$, $B'\in\mathcal P_{s-1,s-2}$. Degrees: in $x$: $(s-2)+1+s=2s-1$; in $u$: $(s-2)+2+(s-1)=2s-1$; in $y$: $(s-2)+1+1+(s-1)=2s-1$; in $v$: $(s-2)+2+1+(s-2)=2s-1$. All $\le n-2$.
Symmetry hypotheses: $H(t_a,t_b,\cdot,\cdot)\equiv H(t_b,t_a,\cdot,\cdot)\equiv0$ since $P\in\mathcal S_a$. $H(x,u,t_a,t_b)\equiv0$ through the factor $(y-t_a)$, and $H(x,u,t_b,t_a)\equiv0$ through the factor $(v-t_a)$. So Lemma 3.1 applies.
Evaluate the sum. Independent pairs of $G$-edges contribute $J\cdot E(P)_\alpha\cdots=0$ (either $J=0$ or $\alpha\in\mathcal T$ and $E(P)_\alpha=0$); pairs involving $\{a,b\}$ have $J=0$; $i=p$ or $k=q$ give $[ii]=0$. The factor $(u-v)(u-y)(v-x)$ kills $p=q$, $p=k$, $q=i$. Only $i=k$ with $p,q,i$ distinct survives. For $i\notin\{a,b\}$ all spokes $ip,iq$ are edges of $G$; they do not cross (normalized), both point out of $i$, so $J([ip],[iq])=\frac12T_i(ip,iq)=:S_i(p,q)$, a linear-order sign on the $2s$ other nodes. For $i\in\{a,b\}$ some terms are zero; we will not need them. Using $(t_p-t_i)w_p=1/F_i'(t_p)$ with $F_i=\prod_{p\ne i}(t-t_p)$ (as in upstream eq:local):
$$
0=\sum_i w_i^2\,U(t_i)(t_i-t_a)V'(t_i)\;\Sigma_i(B'),
$$
where for $i\notin\{a,b\}$, $\Sigma_i(B')=M_i\big(P(t_i,u,t_i,v),\,(v-t_a)B'(u,v)\big)$ is the upstream order pairing on the $2s$ nodes $\{t_p\}_{p\ne i}$ with the order $S_i$.
*Isolation.* Fix $i_0\notin\{a,b\}$. The Lagrange polynomial $L_{i_0}$ of degree $\le 2s$ that is $1$ at $t_{i_0}$ and $0$ at the other $n-1$ nodes vanishes at $t_a$, so $L_{i_0}=(t-t_a)R$ with $\deg R\le 2s-1$. Every monomial $t^k$, $k\le 2s-1$, is a product $t^{k_1}t^{k_2}$ with $k_1\le s$, $k_2\le s-1$; by linearity in $(U,V')$ (for fixed $B'$) the weight $U(t)(t-t_a)V'(t)$ may be replaced by $L_{i_0}$. All terms except $i=i_0$ (including $i=a,b$) then drop, and $w_{i_0}\ne0$ gives $M_{i_0}(P(t_{i_0},u,t_{i_0},v),(v-t_a)B')=0$ for all $B'\in\mathcal P_{s-1,s-2}$. Since $P(t_{i_0},u,t_{i_0},v)\in\mathcal P_{s-2,s-2}$, Lemma 3.4 (with $u_c=t_a$, one of the $2s$ nodes) gives $P(t_{i_0},u,t_{i_0},v)\equiv0$ for every $i_0\notin\{a,b\}$.
*(b) Division.* $P(x,u,x,v)$ has degree $\le 2s-4$ in $x$ and vanishes for the $n-2=2s-1>2s-4$ values $x=t_{i_0}$, $i_0\notin\{a,b\}$; applying the root bound coefficientwise in $(u,v)$, $P(x,u,x,v)\equiv0$, so $(x-y)\mid P$. Exactly as in upstream `lem:injectivity` (within-pair symmetry, primality and pairwise non-associateness of the linear factors), $C=(x-y)(x-v)(u-y)(u-v)$ divides $P$.
*(c) Descent.* Suppose $\ker E\cap\mathcal S_a\neq0$; choose $P\ne0$ there of minimum $x$-degree and write $P=CR$. $C$ is invariant under both within-pair swaps, so $R$ is within-pair symmetric; each separate degree of $R$ is two less than that of $P$, so $R\in\mathcal S$. Also $C(t_a,t_b,y,v)=(t_a-y)(t_a-v)(t_b-y)(t_b-v)\neq0$ in $\mathbb R[y,v]$ and $0=P(t_a,t_b,y,v)=C(t_a,t_b,y,v)R(t_a,t_b,y,v)$, so $R\in\mathcal S_a$. $C$ is nonzero at every independent edge pair (distinct nodes), so $E(R)=0$. This contradicts minimality. Hence $E|_{\mathcal S_a}$ is injective.
For $\mathcal S_b$: $\mathcal T$ is closed under exchanging the two edges, and $E(Q)_{(f,g)}=E(Q^{\mathrm{sw}})_{(g,f)}$ where $Q^{\mathrm{sw}}(x,u,y,v)=Q(y,v,x,u)\in\mathcal S_a$. So $E(Q)=0\Rightarrow E(Q^{\rm sw})=0\Rightarrow Q=0$. $\square$

**Proposition 3.6 (odd lower bound).** For $s\ge2$, every drawing of $K_{2s+1}-e$ has at least $\binom s2^2-\binom s2$ crossings.

*Proof.* With $D$ normalized and minimum, let $W_a=E(\mathcal S_a)$, $W_b=E(\mathcal S_b)$ and let $\langle X,Y\rangle=\sum_{\alpha}a_\alpha X_\alpha Y_\alpha$, a nondegenerate symmetric form on $\mathbb R^{\mathcal T}$ (Lemma 3.3). Lemma 3.3 says $W_b\subseteq W_a^{\perp}$, and nondegeneracy gives $\dim W_a^\perp=|\mathcal T|-\dim W_a$ (the upstream argument in `prop:odd`). Thus $\dim W_a+\dim W_b\le|\mathcal T|$. By Lemmas 3.5 and 3.2 the left side is $2\big(\binom s2^2-\binom s2\big)$. With (3.1), $c(D)\ge|\mathcal T|/2\ge\binom s2^2-\binom s2$. Every drawing has at least as many crossings as $D$. $\square$

*Why the split matters.* The full upstream space $\mathcal S$ is not admissible: for $P\in\mathcal S$, $PQ\Delta$ generally violates the missing-pair symmetry, and the resulting chains are not cycles of $G$. Using one space for both slots ($\mathcal S_a\cap\mathcal S_b$) would lose $2\binom s2-1$ dimensions per side. Pairing two different spaces, each losing only $\binom s2$, gives exactly the conjectured value.

## 4. Even $n$ (re-verified literature argument, Ouyang–Wang–Huang 2014, Thms 3.1–3.3)

Let $n=2M\ge 6$, $D$ a good (normalized, U1) optimal drawing of $K_n-xy$, other vertices $v_1,\dots,v_{n-2}$. Let $K^x$ (resp. $K^y$) be the subdrawing without $y$ (resp. $x$); both are drawings of $K_{n-1}$, with $c(K^x)=Z(n-1)+l_1$, $c(K^y)=Z(n-1)+l_2$ ($l_j\ge0$, U5).
For each $i$ draw a new edge $x\to y$ alongside $xv_i$, around $v_i$ inside a small disk crossing $m_i$ spokes of $v_i$, then alongside $v_iy$. This gives a drawing $D_i$ of $K_n$ with $c(D_i)=c(D)+a_i+m_i$, where $a_i$ is the number of crossings on the path $xv_iy$; write $c(D_i)=Z(n)+c_i$, $c_i\ge0$ (U5; $D_i$ need not be good, which is harmless for the lower bound).
Counting crossings of $D$ by type ($K_{n-2}$, $T_x$, $T_y$ with $T_x,T_y$ the stars at $x,y$; adjacent edges never cross):
$2c(D)=c(K^x)+c(K^y)+\sum_ia_i$ (each $T$–$K_{n-2}$ crossing lies on one path $xv_iy$, each $T_x$–$T_y$ crossing on two). Also $\sum_ic(D_i)=(n-2)c(D)+\sum a_i+\sum m_i=(n-2)Z(n)+\sum c_i$. Eliminating $\sum a_i$:
$$
n\,c(D)=2Z(n-1)+l_1+l_2+(n-2)Z(n)+\textstyle\sum c_i-\sum m_i. \tag{4.1}
$$
Responsibilities $r(v)$ (crossings on edges at $v$; $\sum_v r_D(v)=4c(D)$ since $D$ is good): $r_D(x)=c(D)-c(K^y)$, $r_D(y)=c(D)-c(K^x)$, and $r_D(v_i)+m_i=r_{D_i}(v_i)=c(D_i)-c(D_i-v_i)\le Z(n)+c_i-Z(n-1)$ (the new edge is not at $v_i$; spokes at $v_i$ never cross each other). Summing,
$$
2c(D)\le (n-2)Z(n)-nZ(n-1)-(l_1+l_2)+\textstyle\sum c_i-\sum m_i. \tag{4.2}
$$
Subtracting (4.2) from (4.1): $(n-2)c(D)\ge(n+2)Z(n-1)+2(l_1+l_2)$, so $c(D)\ge\frac{n+2}{n-2}Z(2M-1)=\frac14(M^2-1)(M-2)^2$, which is the target (check J; and $\frac{2M+2}{2M-2}\cdot\frac{(M-1)^2(M-2)^2}{4}=\frac{(M+1)(M-1)(M-2)^2}{4}$ by hand). Only U5 is used; the $m_i$ cancel, so their exact values are irrelevant. For $n\le5$ the target is $0$.

## 5. Upper bound (all $n\ge 4$)

Take the U6 drawing of $K_n$ and delete the edge $\{0,t\}$, $t=\lfloor(n-1)/2\rfloor$. Its crossings are the same-page edges $\{i,j\}$ with $0<i<t<j\le n-1$.
* $n=2s+1$, $t=s$: the removed edge has endpoint-sum residue $s\ge m=s$, so it lies on the lower page, whose residues are $[s,2s]$. For $1\le i\le s-1<s+1\le j\le 2s$, $i+j\in[s+2,3s-1]$; the residue lies in $[s,2s]$ iff $i+j\le2s$. Count $\sum_{i=1}^{s-1}(s-i)=\binom s2$.
* $n=2s$, $t=s-1<m=s$: upper page, residues $[0,s-1]$. For $1\le i\le s-2$, $s\le j\le 2s-1$, $i+j\in[s+1,3s-3]$; upper iff $i+j\ge2s$. Count $\sum_{i=1}^{s-2}i=\binom{s-1}2$.
Thus $c=Z(n)-\binom t2$ (check A confirms counts for $n\le40$). For $n\le 3$ both sides are $0$.

Sections 3–5 prove Theorem A for all $n$ ($n=2,3,4,5$: planar, formula $0$).

## 6. Corollary B

OWH Corollary 5.1: $\operatorname{cr}(K_m\square P_n)=(n-1)\operatorname{cr}(K_{m+2}-e)+2\operatorname{cr}(K_{m+1})$ for $m\ge4$, $n\ge1$. Insert Theorem A and U5.
$m=2k$: $(n-1)\frac14(k+2)k(k-1)^2+2\frac{k^2(k-1)^2}{4}=\frac14k(k-1)^2\big(n(k+2)+k-2\big)$, the Zheng formula ($\lfloor\frac{m+1}2\rfloor=k$, $\lfloor\frac{m-1}2\rfloor=\lfloor\frac{m-2}2\rfloor=k-1$, $\lfloor\frac{m+4}2\rfloor=k+2$, $\lfloor\frac{m-4}2\rfloor=k-2$).
$m=2k+1$: $(n-1)\frac14(k+2)(k+1)k(k-1)+2\frac{(k+1)k^2(k-1)}4=\frac14(k+1)k(k-1)\big(n(k+2)+k-2\big)$, again the formula. Check F confirms $4\le m\le200$, $1\le n\le 7$.
Dependency caveat: OWH Cor 5.1 rests on OWH Thms 5.1/5.2, Lemma 4.1 (zip product) and Bokal's Lemma 5.1; these are cited peer-reviewed literature and were **not** re-audited here.

## 7. Validation (exact finite support; not a proof)

`checks/kn_minus_e_checks.py` (stdlib, exact rationals; output `checks/kn_minus_e_checks.out`, all pass, 37 s):
* A: U6 counts, edge $\{0,t\}$ has $\binom t2$ crossings, $4\le n\le40$.
* B/C ($n=7,8$; two-page minus max edge and two random rectilinear drawings minus an edge): Lemma 3.1 tests vanish exactly; generic non-symmetric tests do not; the localization test of Lemma 3.5 vanishes for random $P\in\mathcal S_a$, $U,V',B'$, for both $t_a$ and $t_b$ twists.
* D/E ($7\le n\le 12$): exact orthogonality of $E(\mathcal S_a)$ and $E(\mathcal S_b)$ (sampled pairs); $\operatorname{rank}E|_{\mathcal S_a}=\operatorname{rank}E|_{\mathcal S_b}=\dim\mathcal S_a=$ target; $|\mathcal T|\ge 2\,$target; tight for the two-page drawing. (For even $n$ the script uses the analogous spaces of degrees $(s-2,s-3)$; this is numerical evidence only. The proof of the even case is §4.)
* F, G, H, J: formula identities; G shows the counting route fails for every odd $n\ge15$ up to $81$ with deficit $(s-1)(s-2)/(2(2s+1))$, an exact identity.
* I: twisted detector full rank, $s\le5$.
`checks/kn_minus_e_modp_large.py` (numpy, mod $2^{31}-1$; output `.out`): D/E for $13\le n\le19$, including $n=15,17,19$ in the new range; ranks equal the target and the two-page drawing is tight.

## 8. Attack on the weakest steps

1. *Is $J_G$ the right form when an edge is missing?* U2 is proved for every finite simple graph; the zero extension at $\{a,b\}$ is just the inclusion of the edge space of $G$ into that of $K_n$. Lemma 3.1(ii) checks that the chains $z_A$ really lie in $G$'s edge space. Checks B confirm on concrete drawings both the identity and its failure without the symmetry condition.
2. *Tensor characterization.* Proved by a basis adapted to $\ker\varphi$; both hypotheses are polynomial identities, which our tests satisfy by explicit vanishing factors.
3. *Localization at endpoints of the missing edge.* Avoided: only $i\notin\{a,b\}$ is isolated, and $2s-1$ roots exceed the degree bound $2s-4$. The $i=a,b$ terms are removed by the Lagrange polynomial, which needs no information about their (incomplete) rotation orders.
4. *Degree budget.* Recomputed per variable in Lemma 3.5(a): exactly $2s-1$ in each variable; the extra factors $(y-t_a)$ and $(v-t_a)$ are paid for by lowering $\deg V$ to $s$ total and $\deg_v B$ to $s-1$ total, which is exactly what Lemma 3.4 tolerates.
5. *Descent preserves $\mathcal S_a$.* Uses that $C(t_a,t_b,y,v)$ is a nonzero polynomial; true since $t_a\neq t_b$ are constants and $y,v$ are variables.
6. *Isotropy between different spaces.* Standard linear algebra; nondegeneracy requires all $a_\alpha\ne0$, which holds on $\mathcal T$ by definition.
7. *Repeated crossings / sign cancellation.* As upstream: cancellation can only remove coordinates from $\mathcal T$; $c(D)\ge|\mathcal T|/2$ still holds.
8. *Small $s$.* $s=2$ ($n=5$): target $0$, nothing to prove. For $s\ge3$ every ingredient is used in its stated range: U4 needs $s\ge2$ and $2s$ nodes (the $2s$ vertices other than $i_0$), and the root count needs $2s-1>2s-4$.
9. *Even case through literature.* §4 re-derives OWH Thm 3.2 line by line using only U1 and U5; the cancellation of the $m_i$ removes the only geometric estimate in the original ($m_i\le\lfloor(n-3)/2\rfloor$ is not needed).

## 9. Novelty limits

* Conjecture status before the pin: Clancy–Haythorpe–Newcombe survey (arXiv 1901.05155v1, §2.2.1) lists Conjecture 29 ($K_n-e$) as known for $n\le12$ and Conjecture 74 ($K_m\square P_n$) as confirmed for $m\le10$. OWH 2014 (Discrete Math. 328, 71–78) reduce the even case to Harary–Hill. Chia–Lee (Ars Combin., 2015) obtained an equivalent even-case result (per the survey).
* Upstream (pin `fd4aeeb`) proves only $\operatorname{cr}(K_n)$ and $\operatorname{cr}(K_{m,n})$; no $K_n-e$ or Cartesian-product statement appears in main.tex, the bipartite sections, or README (grep recorded in `provenance.json`).
* An October 2026 ResearchGate preprint by A. Sadhu settles the **bipartite** Chia–Lee conjecture $\operatorname{cr}(K_{m,n}-e)$ with the same upstream framework; it does not treat $K_n-e$ (abstract and closing "Further questions" mention only $K_{m,n}-F$). This shows the method is being actively extended, so priority for $K_n-e$ is not certified.
* Web searches (2026-10-15) found no resolution of Conjecture 29 for odd $n\ge13$ or of Conjecture 74 beyond OWH. This is a bounded search, not a priority certificate.
* Honest substantiality assessment: the odd-case proof is a structured adaptation of the upstream rank/isotropy method. The new ingredients are the missing-pair test condition (Lemma 3.1), the split spaces with mixed isotropy (Lemmas 3.2–3.3), and the twisted localization/detector (Lemmas 3.4–3.5). The conjectures themselves are long-standing (2007), stated in the standard survey, and were open for odd $n\ge13$.
