# Two obstructions to specific PPT repairs

These are author deductions about proposed methods, not counterexamples to T101G69 and not campaign nominations. The simplex construction itself is paid r69 material. Here its full partial-transpose spectrum is computed to test two new repair proposals.

Use P_(ij),(kl)=sum_r T_ijr T_klr, E(Y)=sum_r X_r Y X_r, and let F(Y)=Y*. Partial transpose is P^Gamma_(ij),(kl)=P_(il),(kj). Full cubic symmetry gives

    P^Gamma=EF,  PF=P,  EF=FE,
    ||P^Gamma−P||HS²=||E−P||HS²=2C.                 (1)

The transpose F must not be omitted: E and P^Gamma have opposite signs on skew matrices.

## A bounded residual can have quadratically many negative PPT modes

Let m>=3, n=m+1, V=1^perp in R^n, v_i=e_i−1/n, and

    a²=(m+1)/(m−1),  T=a sum_(i=1)^n v_i^tensor3.

All operators below act on V. The r69 simplex computation gives B=I, C=m/(m−1), trace(T)=0, and P is a rank-m orthogonal projection. Set

    M(Y)=sum_i(v_i*Yv_i)v_i v_i*.

The Gram <v_i,v_j>=delta_ij−1/n shows that M has eigenvalue m/(m+1) on the identity direction, eigenvalue (m−1)/(m+1) on the m-dimensional slice span, and zero on its orthogonal complement. Indeed its nonzero spectrum is that of the entrywise squared vector Gram, namely ((m−1)/(m+1))I_n+(1/(m+1)²)11*. The identity and slice subspaces are orthogonal because trace(T)=0. In particular

    a² M=P+(m/(m−1)) |I/sqrt(m)><I/sqrt(m)|.         (2)

For x in V, the slice is a times the compression of diag(x) to V. Summing the coordinate Gram delta_ij−1/n yields, for every matrix Y,

    E(Y)=a²M(Y)−Y/(m−1).                             (3)

Combining (2), (3), and (1), the spectrum of P^Gamma is:

| Invariant subspace | Dimension | Eigenvalue |
| --- | ---: | ---: |
| Identity | 1 | 1 |
| Original slices | m | (m−2)/(m−1) |
| Symmetric complement of identity and slices | (m−2)(m+1)/2 | −1/(m−1) |
| Skew matrices | m(m−1)/2 | 1/(m−1) |

These dimensions sum to m². Hence the negative part has

    rank (P^Gamma)_-=(m−2)(m+1)/2,
    tr (P^Gamma)_-=(m−2)(m+1)/(2(m−1)),
    ||(P^Gamma)_-||HS²=(m−2)(m+1)/(2(m−1)²).

The first two quantities are not bounded by an absolute constant times C, which tends to one. Thus paying for each negative eigenvector separately, or assuming trace negativity is O(C), cannot establish the desired global bound. Spectral clipping yields a positive part of rank (m²+m+2)/2, and partial-transposing that positive part back has not been shown positive. No exact PPT approximant follows from this clipping operation alone.

There is nevertheless a short real separable repair in this example:

    Q=((m−1)/m)a² M=((m−1)/m)P+|I/sqrt(m)><I/sqrt(m)|.

Write z_i=v_i/||v_i|| and w_i=m/(m+1). Then Q=sum_i w_i z_i^tensor4, sum_i w_i z_i z_i*=I, length m+1, and

    ||Q−P||HS²=1+1/m.

This is exactly one extra classical mode with bounded cost. It confirms that the negative-eigenvalue count is the wrong measure of mode inflation; it does not refute the desired flexible repair or the cubic target.

## Positive-addition-only PPT repair cannot have quadratic trace cost

For 0<t<=1/4 consider the genuine fully symmetric cubic on R² with nonzero coefficients T_111=T_222=1 and T_112=T_121=T_211=t. Its slices and Gram are

    X1=[[1,t],[t,0]], X2=[[t,0],[0,1]],
    B=[[1+2t²,t],[t,1+t²]].

The maximal absolute row sum of B−I is at most 2t²+t<=3/8, so B<=2I. Direct calculation gives

    beta²=2t²+5t^4,
    C=2(t−t²)²,
    R:=beta²+C=4t²−4t³+7t^4.

Let h=(e_1⊗e_2−e_2⊗e_1)/sqrt(2). For any real symmetric 2-by-2 matrix X, X h X acts on the skew line by det(X). Thus (1) gives

    <h,P^Gamma h>=−(det X1+det X2)=−t+t².

Suppose A>=0 and P+A has positive partial transpose. Put W=(|h><h|)^Gamma. In the basis (11,12,21,22), W has diagonal entries (0,1/2,1/2,0) and off-diagonal entries W_11,22=W_22,11=−1/2. Its largest eigenvalue is 1/2. Consequently

    t−t² <= <h,A^Gamma h>=tr(AW)<=tr(A)/2,
    tr(A)>=2t(1−t).                                  (4)

The ratio of (4) to R diverges as t tends to zero. Therefore no absolute K can guarantee a positive-addition-only PPT repair with tr(A)<=K R, even in dimension two and with B<=2I.

This does not exclude a two-sided Frobenius repair. A trace cost linear in t may still correspond to squared Frobenius cost O(t²). It also does not exclude using the already paid local theorem for small total residual. Its precise use is to reject an unjustified quadratic trace budget for a monotone positive completion.
