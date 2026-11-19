# Laurent integrality and the sharp positivity range for cyclic Catalan triangle sums

## Abstract

We prove Guo and Lian’s Conjecture 6.1 on normalized cyclic sums of products of Gaussian binomial coefficients. The sums are Laurent polynomials over \(\mathbb Z\) for every integer phase parameter \(j\). For a cycle with \(m\) parts, all coefficients are nonnegative if \(0\le j\le m\). This range is sharp for every \(m\). In the one-part case, a Newton basis transforms the signed moment recurrence into an operator with nonnegative coefficients. At each denominator root, interpolation in the moment variable extends the zero-phase divisibility to every \(j\). The cyclic result follows from the \(q\)-Chu–Vandermonde reduction and inversion. Both clauses, with the literal fraction-field expression, are formalized in Lean 4.

## 1. Definitions and statement

Let \(q\) be an indeterminate. For an integer \(h\ge0\), put
\[
 [h]=\frac{1-q^h}{1-q}=\sum_{i=0}^{h-1}q^i,\qquad
 (u;q)_h=\prod_{i=0}^{h-1}(1-uq^i).
\]
In particular \([0]=0\) and \((u;q)_0=1\). For an integer \(N\ge0\) and any integer \(K\), the Gaussian binomial is
\[
 G(N,K)=\begin{bmatrix}N\\K\end{bmatrix}_q
 =\begin{cases}
 (q;q)_N/((q;q)_K(q;q)_{N-K})&0\le K\le N,\\
 0&\text{otherwise}.
 \end{cases}
\]
All identities with quotients are first taken in \(\mathbb Q(q)\). Write \(F_h=\prod_{i=1}^h[i]\), with \(F_0=1\). Since \((q;q)_h=(1-q)^h F_h\), the Gaussian quotient also equals \(F_N/(F_KF_{N-K})\) within its index range.

The following is Conjecture 6.1 of Guo and Lian, quoted from arXiv:1806.02685v1, the only arXiv version. [Guo and Lian, §6](https://arxiv.org/pdf/1806.02685#page=13)

> **Conjecture 6.1** Let \(n_1,\ldots,n_m,n_{m+1}=n_1\) be positive integers. Then, for any integer \(j\) and non-negative integers \(a,r\) with \(a\leqslant n_1\), the expression
> \[
> \frac{1}{[n_m+a]}\begin{bmatrix}n_1+n_m\\n_1-a\end{bmatrix}^{-1}
> \sum_{k=a}^{n_1}[2k][k]^{2r}q^{jk^2-(r+1)k}
> \prod_{i=1}^{m}\begin{bmatrix}n_i+n_{i+1}\\n_i+k\end{bmatrix}
> \]
> is a Laurent polynomial in \(q\), and it has non-negative integer coefficients if \(0\leqslant j\leqslant m\).

Write \(S_r(a;\mathbf n;j;q)\) for this expression. MathDB records 381408 and 339461 refer to the same conjecture. The first clause of the conjecture asks only for a Laurent polynomial in \(q\); the theorem below proves the stronger statement that its coefficients are integers for every integer \(j\).

**Theorem.** Let \(m\ge1\) and \(n_1,\ldots,n_m\ge1\) be integers, with \(n_{m+1}=n_1\). Let \(a,r\) be nonnegative integers satisfying \(a\le n_1\). For every \(j\in\mathbb Z\),
\[
 \frac{1}{[n_m+a]}\begin{bmatrix}n_1+n_m\\n_1-a\end{bmatrix}_q^{-1}
 \sum_{k=a}^{n_1}[2k][k]^{2r}q^{jk^2-(r+1)k}
       \prod_{i=1}^{m}\begin{bmatrix}n_i+n_{i+1}\\n_i+k\end{bmatrix}_q
 \ \in\ \mathbb Z[q,q^{-1}].
\]
If \(0\le j\le m\), every coefficient is nonnegative. For each \(m\ge1\) and each integer \(j\) outside this interval, some admissible choice has a negative coefficient.

Guo and Lian’s Theorem 4.2 proves integer Laurentness for \(0\le j\le m\), and their Theorem 4.1 and recurrence (4.1) treat the one-part moments. Their paper arose from conjectures of Pedro J. Miana, Hideyuki Ohtsuka, and Natalia Romero about ordinary Catalan triangle numbers. Conjecture 6.3 of Victor J. W. Guo and Su-Dan Wang is an earlier \(a=0\) version, with normalization by \([n_1]\). Section 4 below shows that reversing the cycle exchanges the two normalizations for \(a=0\). Ji-Cai Liu’s 2026 paper concerns the positivity of odd \(q\)-super Catalan numbers and an alternating cyclic Gaussian sum, the subjects of Guo’s Conjectures 5.1 and 7.1 in a different paper. [Guo and Lian](https://arxiv.org/abs/1806.02685), [Miana, Ohtsuka, and Romero](https://doi.org/10.1016/j.disc.2017.05.006), [Guo and Wang](https://arxiv.org/abs/1701.07016v2), [Liu](https://arxiv.org/abs/2605.28012)

## 2. Gaussian coefficients and the one-part positive moments

### 2.1. Gaussian coefficients

For \(u,v\ge0\), splitting the geometric sum gives
\[
 [u+v]=[u]+q^u[v].
 \tag{1}
\]
For \(1\le K<N\), multiply
\[
 G(N,K)=G(N-1,K)+q^{N-K}G(N-1,K-1)
 \tag{2}
\]
by \(F_K F_{N-K}\). The right side becomes \(F_{N-1}([N-K]+q^{N-K}[K])=F_N\) by (1). The two boundary values \(G(N,0)=G(N,N)=1\) follow from the product. Hence (2) proves by induction on \(N\) that all \(G(N,K)\) are polynomials with nonnegative integer coefficients, including the zero values outside the range. The factors \(F_h\) are monic and nonzero, so the product identity implies that \(G(N,K)\) is monic in range. The same product identity gives the symmetry \(G(N,K)=G(N,N-K)\) for \(0\le K\le N\). These facts make both denominator factors in the theorem nonzero, since \(n_m+a\ge1\) and \(0\le n_1-a\le n_1+n_m\).

### 2.2. Telescoping and the signed recurrence

Fix \(a\ge0\). For \(n\ge a\) let
\[
 \begin{aligned}
 D_n&=[n+a]G(2n,n-a), & A_k&=q^{-k}[k]^2,\\
 W_n(t)&=q^t[2(n-t)]G(2n,t),&
 U_r(n)&=\sum_{t=0}^{n-a}W_n(t)A_{n-t}^r.
 \end{aligned}
\]
These definitions include \(D_0=U_r(0)=0\) when \(a=0\), with \(A_0^0=1\). For \(n>0\), the change \(t=n-k\) and Gaussian symmetry give
\[
 D_n q^n S_r(a;(n);j;q)
 = \sum_{t=0}^{n-a} W_n(t) A_{n-t}^r q^{j(n-t)^2}.
 \tag{3}
\]
Indeed the power of \(q\) on the right is \(t-r(n-t)+j(n-t)^2\), which is \(n+jk^2-(r+1)k\).

For \(n>0\), writing \(C_t=[t]G(2n,t)\) gives \(C_{t+1}=[2n-t]G(2n,t)\) when \(0\le t\le n\), since both products reduce to \(F_{2n}/(F_tF_{2n-t-1})\). Equation (1) with \(u=t\) and \(v=2(n-t)\) then gives \(C_{t+1}-C_t=W_n(t)\). The endpoints \(C_0=0\) and \(C_{n-a+1}=[n+a]G(2n,n-a)=D_n\) yield \(U_0(n)=D_n\). At \(n=0\) the same equality holds because both sides are zero.

For \(n\ge k\ge0\), the two orders in (1) give
\[
 \begin{aligned}
 [n]^2-q^{n-k}[k]^2
  &= [n]([n]-q^{n-k}[k])+q^{n-k}[k]([n]-[k])\\
  &= [n-k]([n]+q^n[k])=[n-k][n+k].
 \end{aligned}
\]
Multiplying by \(q^{-n}\) gives \(A_n-A_k=q^{-n}[n-k][n+k]\). For \(t=1,\ldots,n-a\) and \(n>a\), the factorial identity gives
\[
 [t][2n-t]G(2n,t)=[2n][2n-1]G(2n-2,t-1).
\]
Here \(t\ge1\) and \(2n-t\ge n\ge1\), so one factor can be canceled at the end of each factorial in the denominator. It follows that
\[
 \begin{aligned}
 A_n U_r(n)-U_{r+1}(n)
    &=q^{1-n}[2n][2n-1]\,U_r(n-1),\\
 [2n][2n-1]\,D_{n-1}
    &=[n-a][n+a-1]\,D_n.
 \tag{4}
 \end{aligned}
\]
For the first equality, the term with \(t=0\) vanishes, and replacing \(t\) by \(t-1\) in the remaining terms gives the weights at \(n-1\) with the same \(k=n-t\). For the second equality, use the same factorial identity with \(t=n-a\) and multiply by \([n+a-1]\). This also proves it at \(n=1,a=0\), where both sides vanish.

On functions \(f(n)\) indexed by \(n\ge a\), define a linear operator \(\mathcal T\) by
\[
 (\mathcal T f)(a)=A_a f(a),\qquad
 (\mathcal T f)(n)=A_n f(n)-q^{1-n}[n-a][n+a-1]f(n-1)\quad(n>a).
\]
Set \(M_0(n)=1\) and \(M_{r+1}=\mathcal T M_r\). Then \(D_n M_r(n)=U_r(n)\) for every \(n\ge a\). The assertion holds at \(r=0\) by telescoping. At \(n=a\), the sum \(U_r(n)\) has one term, so \(U_{r+1}(a)=A_aU_r(a)\). At \(n>a\), multiply the defining recurrence by \(D_n\), substitute the induction hypothesis at \(n\) and \(n-1\), and apply (4). This proof includes the zero row without any division there. By (3), \(M_r(n)=q^n S_r(a;(n);0;q)\) for \(n\ge a\) with \(n>0\).

### 2.3. A positive Newton action

Define, for \(i\ge0\), the polynomial in \(z\) over \(\mathbb Q(q)\)
\[
 H_i(z)=\prod_{s=0}^{i-1}\frac{z-q^{-a-s}}{1-q}.
\]
Write \(h_i(n)=H_i(q^{-n})\) for \(n\ge a\). If \(i>n-a\), the factor with \(s=n-a\) makes \(h_i(n)=0\). Otherwise each factor in \(h_i(n)\) is \(q^{-n}[n-a-s]\). Thus all \(h_i(n)\) belong to \(\mathbb Z_{\ge0}[q,q^{-1}]\). Equivalently this evaluation is \(q^{-ni}\prod_{s=0}^{i-1}[n-a-s]\), where a negative length is truncated to zero for this product. In particular,
\[
 h_{i+1}(n)=q^{-n}[n-a-i]h_i(n)
\]
under the same truncation convention.

Put
\[
 c_i=A_a+q^{-a-i}[i]+q^{1-a-i}[i][2a+i-1],
\]
with the last term zero when \(i=0\). The lengths that occur in a nonzero term are nonnegative. In particular \(2a+i-1\ge0\) when \(i>0\), so \(c_i\) has nonnegative Laurent coefficients. We prove
\[
 \mathcal T h_i = c_i h_i + [i+1]h_{i+1}.
 \tag{5}
\]
At \(n=a\), \(h_0(a)=1\), \(h_i(a)=0\) for \(i>0\), and \(c_0=A_a\), proving (5) there. Suppose \(n>a\) and put \(u=n-a>0\). If \(i>u\), all three basis evaluations \(h_i(n),h_i(n-1),h_{i+1}(n)\) vanish. For \(i\le u\), the first factor of the product \(\prod_{s=0}^{i}[u-s]\) is \([u]\), and its remaining factors are the length product for \(h_i(n-1)\). Its last factor is \([u-i]\), and the preceding factors are the length product for \(h_i(n)\). Accounting for the powers \(q^{-ni}\) gives
\[
 [u]h_i(n-1)=q^{i}[u-i]h_i(n).
\]
Consequently the left side of (5) at \(n\) is \(h_i(n)\) times
\[
 A_n-q^{1-n+i}[n+a-1][u-i]
  =A_a+q^{-n}[u]+q^{1-n}[n+a-1][i].
 \tag{6}
\]
To obtain (6), use \(A_n-A_a=q^{-n}[u][n+a]\), \([n+a]=1+q[n+a-1]\), and \([u]-q^i[u-i]=[i]\). Splitting \([u]=[u-i]+q^{u-i}[i]\) makes \(q^{-n}[u]\) equal to \(q^{-n}[u-i]+q^{-a-i}[i]\). For \(i>0\), split \([n+a-1]=[u-i]+q^{u-i}[2a+i-1]\). When \(i=0\), the term multiplied by \([i]\) vanishes and that split is unnecessary. In either case (6) equals \(c_i+(1+q[i])q^{-n}[u-i]\). Now \(1+q[i]=[i+1]\), which proves (5).

The constant function \(M_0=h_0\) lies in the set of finite linear combinations of the \(h_i\) with coefficients in \(\mathbb Z_{\ge0}[q,q^{-1}]\). Formula (5) and linearity show that \(\mathcal T\) preserves this set. Induction therefore gives \(M_r(n)\in\mathbb Z_{\ge0}[q,q^{-1}]\) for every \(n\ge a\). For \(n>0\), multiplying by \(q^{-n}\) proves the singleton claim at \(j=0\).

## 3. Integer Laurentness for every singleton phase

### 3.1. The denominator has simple, nonzero roots

Fix \(n>0\) and \(0\le a\le n\). Put \(b=n-a\) and \(c=n+a-1\), so \(b,c\ge0\) and \(b+c+1=2n\). The factorial formula gives
\[
 D_n F_b F_c = F_{2n}.
 \tag{7}
\]
At \(q=0\) every \([i]\) with \(i\ge1\) equals 1, and at \(q=1\) it equals \(i\). Thus (7) implies that no root of \(D_n\) is 0 or 1. At a root \(\zeta\), (7) also implies \([i](\zeta)=0\) for some \(1\le i\le 2n\). Since \(\zeta\ne1\), this implies \(\zeta^i=1\).

Let \(d\ge2\) be the order of \(\zeta\). For \(i\ge1\), \([i]\) vanishes at \(\zeta\) precisely when \(d\mid i\). Then the root is simple because \((q^i-1)'(\zeta)=i\zeta^{i-1}\ne0\) and the factor \(q-1\) does not vanish at \(\zeta\). Hence the multiplicity in \(F_s\) is \(\lfloor s/d\rfloor\), and by (7) the multiplicity in \(D_n\) is
\[
 \left\lfloor\frac{b+c+1}{d}\right\rfloor
   -\left\lfloor\frac b d\right\rfloor
   -\left\lfloor\frac c d\right\rfloor .
\]
Writing each of \(b,c\) as an integer quotient times \(d\) plus a remainder in \([0,d-1]\) shows that the combined remainder plus 1 is at most \(2d-1\). The displayed multiplicity is therefore at most one. The polynomial \(D_n\) is monic by §2.1 and \(n+a>0\). If it is constant, monicity gives \(D_n=1\).

### 3.2. Interpolation and descent

Let \(\zeta\) be any root of \(D_n\). Since \(\zeta\ne0\), evaluation at \(\zeta\) makes sense for Laurent polynomials. The identity \(U_h(n)=D_n M_h(n)\) gives
\[
 \sum_{t=0}^{n-a} W_n(t)(\zeta)\, A_{n-t}(\zeta)^h=0
 \qquad(h\ge0).
 \tag{8}
\]
We show that \(k\mapsto \zeta^{jk^2}\) is constant on the fibers of \(k\mapsto A_k(\zeta)\). If \(A_k(\zeta)=A_l(\zeta)\), write \(x=\zeta^k\) and \(y=\zeta^l\). The geometric identity gives \(A_k(\zeta)(1-\zeta)^2x=(1-x)^2\) and the corresponding identity for \(l\). Multiplying the first by \(y\) and the second by \(x\) and subtracting yields
\[
 0= y(1-x)^2-x(1-y)^2=(x-y)(xy-1).
\]
Thus \(\zeta^{k-l}=1\) or \(\zeta^{k+l}=1\). Because \(j(k^2-l^2)=j(k-l)(k+l)\), this gives \(\zeta^{jk^2}=\zeta^{jl^2}\) for every integer \(j\), using \(\zeta\ne0\) for negative exponents.

Let \(V=\{A_{n-t}(\zeta):0\le t\le n-a\}\). For \(u\in V\) define \(v_u=\zeta^{jk^2}\) for any \(k\in[a,n]\) with \(A_k(\zeta)=u\). The fiber property gives a well-defined \(v_u\). The polynomial
\[
 P(X)=\sum_{u\in V} v_u \prod_{v\in V\setminus\{u\}}\frac{X-v}{u-v}
\]
satisfies \(P(u)=v_u\), because each other summand has a zero factor at \(u\) and every factor in the \(u\)-summand equals 1. Expanding \(X^rP(X)\) into powers and using (8) term by term shows that the right side of (3) vanishes upon evaluation at \(\zeta\). This works at every root.

Call the right side of (3) \(N(q)\). It is in \(\mathbb Z[q,q^{-1}]\). Choose \(e\ge0\) so that \(q^eN(q)\) is an ordinary integer polynomial. Since \(D_n\) is monic, division gives \(q^eN=D_n Q+R\) over \(\mathbb Z[q]\), with \(R=0\) or \(\deg R<\deg D_n\). If \(D_n=1\), the remainder is zero. Otherwise \(D_n\) has \(\deg D_n\) distinct roots over \(\mathbb C\). At each such root \(R\) vanishes since \(q^eN\) vanishes there. A nonzero polynomial of smaller degree cannot have this many distinct roots. Hence \(R=0\), and (3) gives \(S_r(a;(n);j;q)=q^{-e-n}Q\).

## 4. Reduction of cycles

### 4.1. The Gaussian convolution

For \(h\ge0\) define \(\tau(h)=h(h-1)/2\), with \(\tau(0)=0\). For \(o,N\ge0\), the coefficient of \(X^h\) in \(\prod_{i=0}^{N-1}(1+q^{o+i}X)\) is \(q^{oh+\tau(h)}G(N,h)\). To prove this, the case \(N=0\) is the constant 1. The constant term remains 1 at each step. Multiplication by \(1+q^{o+N}X\) changes the coefficient of \(X^h\) for \(h\ge1\) to
\[
 q^{oh+\tau(h)}G(N,h)
  +q^{o+N+o(h-1)+\tau(h-1)}G(N,h-1).
\]
For \(1\le h\le N+1\) the second exponent exceeds \(oh+\tau(h)\) by \(N+1-h\), so (2) gives the new coefficient. At \(h=N+1\), this uses \(G(N,h)=0\) and \(G(N,N)=1\). For \(h>N+1\) both old coefficients are zero and so is \(G(N+1,h)\).

Split this product with \(o=0,N=u+v\) into blocks starting at 0 and \(u\), of lengths \(u\) and \(v\), respectively. Extract the term of degree \(K\) and divide by \(q^{\tau(K)}\). For degrees \(f,g\) with \(f+g=K\), the remaining exponent is
\(\tau(f)+ug+\tau(g)-\tau(f+g)=(u-f)g\). Take \(u=x-k\), \(v=y+k\), \(K=x+k\), and suppose \(0\le k\le\min(x,y)\). Write \(g=l+k\), giving \(f=x-l\). The constraints \(0\le f\le u\) and \(0\le g\le v\) become \(k\le l\le\min(x,y)\). By Gaussian symmetry in the first block we obtain
\[
 G(x+y,x+k)=
 \sum_{l=k}^{\min(x,y)}q^{l^2-k^2}G(x-k,l-k)G(y+k,l+k).
 \tag{9}
\]

### 4.2. The two reductions

For \(x,k\ge0\), set \(K_x(k)=1/(F_{x+k}F_{x-k})\) if \(k\le x\), and \(K_x(k)=0\) otherwise. By (9) and the factorial formulas,
\[
 F_{x+y} K_x(k)K_y(k)
  =\sum_{l=k}^{\min(x,y)} \frac{q^{l^2-k^2}K_l(k)}{F_{x-l}F_{y-l}} .
 \tag{10}
\]
Indeed for \(k\le\min(x,y)\), divide (9) by \(F_{x-k}F_{y+k}\). The left side becomes \(F_{x+y}/(F_{x+k}F_{y-k}F_{x-k}F_{y+k})\), and each right side term cancels the two numerator factorials \(F_{x-k}, F_{y+k}\). For \(k>\min(x,y)\), one left kernel is zero and the sum is empty.

For a nonempty cycle \(\mathbf n=(n_1,\ldots,n_m)\), the cyclic Gaussian product equals
\[
 \left(\prod_{i=1}^{m}F_{n_i+n_{i+1}}\right)\prod_{i=1}^{m}K_{n_i}(k).
\]
If \(k\le\min_i n_i\), this follows by collecting one factor \(F_{n_i+k}\) from the edge leaving vertex \(i\) and one \(F_{n_i-k}\) from the edge entering it. If \(k>\min_i n_i\), the edge entering a part less than \(k\) has a lower index above its upper index, so both sides are zero. For \(p=n_m\) and \(x=n_1\), the denominator is \(F_{x+p}/(F_{x-a}F_{p+a-1})\), by \(F_{p+a}=[p+a]F_{p+a-1}\) and \(p+a\ge1\). Canceling the closing edge factor \(F_{p+x}\) yields the representation
\[
 S_r(a;\mathbf n;j;q)
   = F_{x-a}F_{p+a-1}\left(\prod_{i=1}^{m-1}F_{n_i+n_{i+1}}\right)
      \sum_{k=a}^x [2k][k]^{2r}q^{jk^2-(r+1)k}
         \prod_{i=1}^m K_{n_i}(k).
 \tag{11}
\]

Now \(m\ge2\), write \(y=n_2\), and let \(I=[\max(1,a),\min(x,y)]\cap\mathbb Z\). Apply (10) to the \(x,y\) kernels and open-edge factor \(F_{x+y}\) in (11). For each \(k\) the sum over \(l\) can be taken over \(I\): the term \(k=0\) has coefficient \([0]=0\), and for \(k\ge\max(1,a)\) the additional indices \(l<k\) have \(K_l(k)=0\). Swap the two finite sums. For each \(l\in I\), the terms \(k>l\) vanish again by \(K_l(k)=0\), and \(q^{l^2-k^2}q^{jk^2-(r+1)k}=q^{l^2}q^{(j-1)k^2-(r+1)k}\). Thus the inner sum is the kernel sum of the smaller cycle \((l,n_3,\ldots,n_m)\) in (11) with the parameter \(j-1\).

If \(m=2\), the old prefactor after removing \(F_{x+y}\) is \(F_{x-a}F_{y+a-1}\), and the new singleton prefactor is \(F_{l-a}F_{l+a-1}\). The factor \(F_{x-l}F_{y-l}\) comes from (10). Dividing the old by the new and by this factor gives \(G(x-a,l-a)G(y+a-1,l+a-1)\). If \(m\ge3\), write \(z=n_3\). Both prefactors include \(F_{p+a-1}\) and all open edge factors from \(z\) onwards. The remaining old factors are \(F_{x-a}F_{y+z}\), and the new are \(F_{l-a}F_{l+z}\). Their ratio, divided by \(F_{x-l}F_{y-l}\), gives \(G(x-a,l-a)G(y+z,y-l)\). In either case \(l\in I\) ensures \(l\ge1\), \(a\le l\le x\), and \(l\le y\). In particular \(l+a-1\ge0\) whenever it occurs. We have proved the reductions
\[
\begin{aligned}
 S_r(a;(x,y);j;q)
  &=\sum_{l\in I}q^{l^2}G(x-a,l-a)G(y+a-1,l+a-1)S_r(a;(l);j-1;q),\\
 S_r(a;(x,y,z,\ldots,p);j;q)
  &=\sum_{l\in I}q^{l^2}G(x-a,l-a)G(y+z,y-l)S_r(a;(l,z,\ldots,p);j-1;q).
 \tag{12}
\end{aligned}
\]
These are Guo and Lian’s reductions (4.8) for two parts and (4.7) for three or more parts. Their coefficients have nonnegative Laurent coefficients by §2.1, and the proof of (12) applies to every integer \(j\). [Guo and Lian, §4](https://arxiv.org/pdf/1806.02685)

The reversal assertion in §1 now follows. For \(a=0\), the cyclic Gaussian product is unchanged by reversal, since the edge sums and kernel factors are unchanged as multisets. The common support is bounded above by \(\min_i n_i\), so exchanging the summation bounds \(n_1\) and \(n_m\) leaves the sum unchanged. The denominator Gaussian is unchanged by symmetry, while the factor \([n_m]\) for the reversed list becomes \([n_1]\) in the original indexing. The term \(k=0\) is zero.

### 4.3. Reflection and the induction

For \(h\ge1\), reversing the sum defining \([h]\) gives \([h](q^{-1})=q^{1-h}[h](q)\); the same equality holds for \(h=0\) since both sides are zero. Thus \(F_s(q^{-1})=q^{-s(s-1)/2}F_s(q)\), and taking the factorial ratio gives
\[
 G(N,K)(q^{-1})=q^{-K(N-K)}G(N,K)(q)\qquad(0\le K\le N).
\]
In any nonzero summand of the cyclic numerator, \(k\le\min_i n_i\). Inverting its Gaussian factors contributes an exponent
\[
 -\sum_i(n_i+k)(n_{i+1}-k)
   = m k^2-\sum_i n_i n_{i+1},
\]
since \(\sum_i(n_i-n_{i+1})=0\). The factor \([2k][k]^{2r}\) contributes \(1-2k+2r(1-k)\). The phase with \(m-j\) contributes \(-(m-j)k^2+(r+1)k\). Adding the three exponents gives \(jk^2-(r+1)k+2r+1-\sum_i n_i n_{i+1}\). Terms that vanish before inversion also vanish after it. The denominator is multiplied under inversion by \(q^{-\delta}\), where \(\delta=n_m+a-1+(n_1-a)(n_m+a)\). We obtain
\[
 S_r(a;\mathbf n;m-j;q^{-1})
 =q^{\,2r+1-\sum_i n_i n_{i+1}+\delta}\,S_r(a;\mathbf n;j;q).
 \tag{13}
\]
Multiplication by any integral power of \(q\) and the substitution \(q\mapsto q^{-1}\) each permute the coefficient positions of a Laurent polynomial, so both preserve coefficient nonnegativity.

We prove both assertions by induction on \(m\). For \(m=1\), §3 gives Laurentness for every integer \(j\), §2 gives positivity at \(j=0\), and (13) gives positivity at \(j=1\). For \(m\ge2\), every shorter cycle in (12) satisfies the positivity and lower-bound hypotheses on its parts. The induction hypothesis gives integer Laurentness for every \(j-1\). Since the multipliers are Laurent polynomials over \(\mathbb Z\), the finite sums in (12) give integer Laurentness. When \(1\le j\le m\), the new parameter satisfies \(0\le j-1\le m-1\), so every shorter-cycle witness and every multiplier has nonnegative coefficients. Consequently the sum has nonnegative coefficients. Finally \(j=m\) has just been proved positive, so reflection (13) proves positivity at \(j=0\).

## 5. Sharpness and small cases

For any \(m\ge1\), take all \(n_i=2\), \(a=1\), and \(r=0\). The \(k=1\) factors are \(G(4,3)=[4]\), the \(k=2\) factors are \(G(4,4)=1\), and the denominator is \([3]G(4,1)=[3][4]\). Cancellation gives
\[
 [3]S_0(1;(2,\ldots,2);j;q)
    =[2][4]^{m-1}q^{\,j-1}+q^{\,4j-2}.
 \tag{14}
\]
For \(j\le-1\), the lowest exponent on the right is \(4j-2\), with coefficient 1, and the next exponent \(4j-1\) has coefficient zero because \(j-1-(4j-2)=1-3j\ge4\). The constant coefficient of \([3]=1+q+q^2\) is 1, so the Laurent polynomial \(S_0\) starts with coefficient 1 at exponent \(4j-2\) and coefficient \(-1\) at exponent \(4j-1\). For \(j\ge m+1\), the exponent \(4j-2\) is the largest on the right because the first term has degree \(j+3m-3\), at least four below \(4j-2\). The highest coefficient on the right is 1 and the next is zero. Since the leading two coefficients of \([3]\) are 1, \(S_0\) has leading coefficient 1 at exponent \(4j-4\) and coefficient \(-1\) at exponent \(4j-5\). This certifies sharpness for each \(m\) and each excluded \(j\).

The entries below were checked by exact polynomial multiplication after clearing the denominator and shifting both sides by an integral power of \(q\). For example, the first negative example in the table comes from dividing \(1+q^4+q^5\) by \(1+q+q^2\), with quotient \(1-q+q^3\) and shift \(-6\) in (14). The second negative example comes from dividing \(1+q+q^5\) by \(1+q+q^2\), with quotient \(1-q^2+q^3\) and shift \(1\). The zero case has \(a>\min_i n_i\), so every Gaussian product is zero. These examples serve as checks of the formula. The proof uses no enumeration of parameters.

| \(\mathbf n\) | \(a\) | \(r\) | \(j\) | \(S_r(a;\mathbf n;j;q)\) |
|---|---:|---:|---:|---|
| \((1)\) | 0 | 2 | \(-1\) | \(q^{-4}\) |
| \((2)\) | 1 | 0 | \(-1\) | \(q^{-6}-q^{-5}+q^{-3}\) |
| \((2)\) | 1 | 0 | 0 | \(q^{-2}\) |
| \((2)\) | 1 | 0 | 1 | \(1\) |
| \((2)\) | 1 | 0 | 2 | \(q-q^3+q^4\) |
| \((2)\) | 1 | 1 | 0 | \(q^{-4}+q^{-3}\) |
| \((2,2)\) | 1 | 0 | 0 | \(q^{-2}+1+q\) |
| \((2,2)\) | 1 | 0 | 1 | \(1+q+q^2\) |
| \((2,2)\) | 1 | 0 | 2 | \(q+q^2+q^4\) |
| \((3,1,2)\) | 2 | 1 | 2 | \(0\) |
| \((2,1,3)\) | 0 | 0 | 3 | \(q^2+q^3\) |

## 6. Lean correspondence and scope

The accompanying Lean source uses `LaurentPolynomial ℤ` for the witness ring and `FractionRing (LaurentPolynomial ℤ)` for the exact rational expression. The list is nonempty, its entries are strictly positive, and the last edge explicitly closes to the first entry. The theorem `Catalan.mathdb381408` proves `Catalan.GuoLianConjecture`. Its projections are `Catalan.mathdb381408_laurent` and `Catalan.mathdb381408_nonnegative`. The former uses integer coefficients throughout, including outside the positivity range. The latter tests every Laurent coefficient, including the coefficients of negative powers. The kernel checks allow only `propext`, `Classical.choice`, and `Quot.sound`.

The following declaration names are in namespace `Catalan`.

| Argument | Lean declarations and implementation choices |
|---|---|
| Definitions and the literal quotient | `qInt`, `gauss`, `edgesFrom`, `cyclicPairs`, `numerator`, `denominator`, `expression`, `denominator_ne_zero`, `expression_eq_embed_iff`. The integer exponent is represented by the Laurent monomial `LaurentPolynomial.T` and then embedded in the fraction field. |
| Geometric addition and Gaussian theory, (1)–(2) | `qInt_add`, `rect_succ_succ`, `rect_factorial`, `gauss_pochhammer`, `gauss_nonneg`, `gauss_monic`, `gauss_symm`. Lean starts with Pascal recursion in the two complementary column sizes and derives the factorial equations by cross multiplication. |
| Singleton reindexing and moment recurrence, (3)–(4) | `oneNumer_literal`, `oneWeight_telescopes`, `momentSum_zero`, `A_sub`, `gr_lower`, `momentSum_step`, `oneDenom_step`, `moment_normalizes`. The signed recurrence is defined before proving the product identity, allowing the zero row without division. |
| Positive Newton action, (5)–(6) | `newton`, `newton_shift`, `action_coefficient`, `newton_action`, `PositiveSpan.closed_under_momentOp`, `moment_nonnegative`, `singleton_zero_phase`. Lean works with the evaluated falling products and natural offsets, avoiding the rational-function shift of the unevaluated Newton polynomials used in the initial proof. The paper gives the denominator-free variant. |
| Root multiplicity and interpolation, (7)–(8) | `oneDenomPoly_factorial`, `oneDenomPoly_root_ne_zero`, `oneDenomPoly_root_ne_one`, `oneDenomPoly_rootMultiplicity_le_one`, `phase_factors`, `phasedMoment_vanishes`, `oneDenom_dvd_of_vanishes`, `singleton_integral`. Lean uses Mathlib’s Lagrange interpolation on the finite image and the comparison of root multiplicities over \(\mathbb C\). The descent uses `Polynomial.map_dvd_map` for monic divisors, which is proved by monic remainders. The paper expresses that descent using the remainder’s degree. |
| Gaussian convolution and reduction, (9)–(12) | `gen_coeff`, `gen_split`, `qChu`, `kernel_chu`, `weight_factorization`, `normalized_cycle`, `reduced_raw`, `cycle_reduce_two`, `cycle_reduce_many`. Lean uses an outer polynomial variable for the generating product and sums over the two degrees in an antidiagonal. The inverse factorial factors from the two incident edges are grouped at each part. |
| Reflection and assembly, (13) | `invert_qi`, `invert_gr`, `invert_walk`, `invert_numerator`, `invert_denominator`, `reflect_witness`, `cons_cases`, `mathdb381408`. Lean proves Gaussian inversion by Pascal recursion and symmetry. The paper uses the factorial ratio. Lean carries out the quotient transformation as a multiplication identity in the Laurent ring. |

The sharpness proof in §5 and the small-case table are supplementary to the two formal endpoints. The sharpness proof is algebraic, and exact arithmetic independently checks the table and sampled members of the sharpness family. The prior-art check included the source, its stated ancestor, related recent work, and the Semantic Scholar and OpenAlex citation lists of both Guo–Lian and Guo–Wang, and found no proof or disproof of either clause. The full text of one citing paper, Song-Xiao Li and Su-Dan Wang’s 2026 article on sums of products of \(q\)-Narayana numbers, could not be read, and no citation database is complete, so priority beyond this checked literature remains open to verification.

## References

1. Victor J. W. Guo and Xiuguo Lian, “Proofs of two conjectures on Catalan triangle numbers,” *Journal of Difference Equations and Applications* 24(9) (2018), 1473–1487. [arXiv:1806.02685](https://arxiv.org/abs/1806.02685), [DOI](https://doi.org/10.1080/10236198.2018.1501041)
2. Victor J. W. Guo and Su-Dan Wang, “Factors of sums involving \(q\)-binomial coefficients and powers of \(q\)-integers,” *Journal of Difference Equations and Applications* 23 (2017), 1670–1679. [arXiv:1701.07016v2](https://arxiv.org/abs/1701.07016v2)
3. Pedro J. Miana, Hideyuki Ohtsuka, and Natalia Romero, “Sums of powers of Catalan triangle numbers,” *Discrete Mathematics* 340 (2017), 2388–2397. [DOI](https://doi.org/10.1016/j.disc.2017.05.006)
4. Ji-Cai Liu, “Proofs of Two Positivity Conjectures of Guo,” 2026. [arXiv:2605.28012](https://arxiv.org/abs/2605.28012)
