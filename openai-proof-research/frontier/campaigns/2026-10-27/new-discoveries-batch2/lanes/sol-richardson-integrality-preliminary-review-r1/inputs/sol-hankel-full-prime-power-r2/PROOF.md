# Full ordinary proof of Richardson's integrality criterion

Status: ordinary mathematics complete, subject to root's independent review and substantive/prior-art decision. No acceptance or discovery count is claimed. The proposed linearization, weighted sum, and carry strategy were supplied by root in the assignment; this lane independently verifies and proves them. All parameters below are integers unless stated otherwise.

## Statement and source identification

For every n>=1 and r>=1 let R be the n by n matrix, with zero-based indices, given by

    R[i,j] = 1 / binom(i+j+r,r),  0<=i,j<n.

Then R is invertible and its inverse is integral if and only if r divides n(n-1). Equivalently, for every prime power q dividing r, n is 0 or 1 modulo q. Different prime factors may choose different alternatives.

This is precisely Richardson, The Filbert Matrix, Fibonacci Quarterly 39(3) (2001), 268–275, Definition 1.1 and Conjecture 5.1 on p272: his b_k(r)=binom(k+r-1,r) and one-based Hankel index i+j-1 give this matrix after subtracting 1 from both indices. The earlier arXiv version is math/9905079v1, 12 May 1999. Theorem 5.2 already gives an inverse formula; we do not claim its discovery. The proof below supplies the full arithmetic implication, not just a denominator bound or squarefree case.

Throughout, binomial coefficients with nonnegative top and lower index outside [0,top] are zero.

## 1. Exact inverse kernel, with normalization proved

Use the measure dmu=r(1-x)^(r-1)dx on [0,1]. The elementary beta integral gives its moment of order s>=0 as 1/binom(s+r,r). Thus R is its monomial Gram matrix, positive definite since a nonzero polynomial has strictly positive squared integral.

Define

    P_i(k)=binom(k,i)binom(k+r+i-1,i),
    Q_k(x)=sum_{i=0}^k (-1)^i P_i(k) x^i.

These are ordinary shifted Jacobi polynomials, but no convention about their normalization is assumed. In fact

    Q_k(x) = (1-x)^(1-r)/k! * D^k[x^k(1-x)^(k+r-1)].

To see the coefficient identity directly, Leibniz gives the right side as

    sum_{a=0}^k (-1)^a binom(k,a)binom(k+r-1,a) x^a(1-x)^(k-a).

The coefficient of x^i is (-1)^i binom(k,i) times
sum_{a=0}^i binom(i,a)binom(k+r-1,a), which equals
(-1)^i binom(k,i)binom(k+r+i-1,i) by Vandermonde.

The first k-1 derivatives of x^k(1-x)^(k+r-1) vanish at both endpoints (also for r=1). Integrating by parts k times proves orthogonality to polynomials of degree less than k. The leading coefficient of Q_k is L_k=(-1)^k binom(2k+r-1,k). The same calculation with Q_k in place of the test polynomial gives

    integral_0^1 Q_k(x)^2(1-x)^(r-1) dx
      = (-1)^k L_k Beta(k+1,k+r) = 1/(2k+r).

For the triangular coefficient matrix C[k,i]=(-1)^i P_i(k), we have
C R C^T=diag(r/(2k+r)). Since C has nonzero diagonal, inversion yields

    (R^-1)[i,j] = (-1)^(i+j)/r * N[i,j],
    N[i,j] = sum_{k=0}^{n-1} (2k+r) P_i(k)P_j(k).             (1)

All P_i(k) and N[i,j] are integers. This is the standard orthogonal-polynomial kernel inversion, consistent with Berg's actual Theorem 2.1 and its proof; the above derives the needed specialization completely.

## 2. Exact integral linearization, proved by induction

For all i,j,k>=0 and r>=1,

    P_i(k)P_j(k) = sum_{l=max(i,j)}^{i+j} A(i,j,l)P_l(k),
    A(i,j,l)=binom(l,i)binom(l,j)binom(r+i+j-1,i+j-l).       (2)

Proof. Set X=k(k+r). As polynomials in X,

    P_i = product_{h=0}^{i-1}(X-h(h+r))/(i!)^2,
    X P_l = (l+1)^2 P_{l+1}+l(l+r)P_l.

We prove (2) by induction on j for every fixed i. For j=0, A(i,0,i)=1. Multiplying the induction hypothesis by X-j(j+r) and dividing by (j+1)^2 shows that the required coefficient recurrence is

    (j+1)^2 A(i,j+1,l)
       = l^2 A(i,j,l-1)+(l(l+r)-j(j+r))A(i,j,l).           (3)

Here A is zero outside its stated support. On max(i,j)<=l<=i+j, put d=i+j+1-l>=1. If l>=j+1, elementary factorial ratios give

    A(i,j+1,l)/A(i,j,l) = (l-j)(r+i+j)/((j+1)d),
    l^2 A(i,j,l-1)/A(i,j,l)
                             = (l-i)(l-j)(r+l-1)/d.

The second formula includes a zero previous coefficient when l=i or l=j. Substitution reduces (3) to the polynomial identity

    (l-i)(r+l-1)+(l+j+r)(i+j+1-l) = (j+1)(r+i+j),

obtained by expansion. If l=j>=i, all terms of (3) vanish. At the new top l=i+j+1, only the previous top coefficient remains, and (3) reads

    (j+1)^2 binom(i+j+1,i)^2
        = (i+j+1)^2 binom(i+j,i)^2,

which is the factorial formula. Below max(i,j), or above i+j+1, every term is zero. These cover every boundary, including i=0. Thus (3) and the induction hold. Evaluation at any k>=0 proves (2), including l>k where P_l(k)=0. Every A is an integer for positive integer r. No finite check is used in this proof.

## 3. Exact weighted sum, proved by telescoping

For n>=0,l>=0,r>=1,

    S_l(n):=sum_{k=0}^{n-1}(2k+r)P_l(k)
       = (n+r-1)binom(n,l+1)binom(n+r+l-1,l).             (4)

Let T_l(k) be the right side with n=k. For k>=l,

    T_l(k)   = ((k+r-1)(k-l)/(l+1)) P_l(k),
    T_l(k+1) = ((k+1)(k+r+l)/(l+1)) P_l(k).

The difference is (2k+r)P_l(k), since the difference of the two numerators is (l+1)(2k+r). For k<l, both T terms and P_l(k) vanish. Also T_l(0)=0. There is a harmless formal top -1 at k=0,r=1,l=0 in the displayed binomial expression: define T_0(0)=0 directly; for l>0 the factor binom(0,l+1) makes T_l(0)=0 by definition. Thus telescoping proves (4) without using any negative-top convention. In particular for l>=n both sides are zero.

## 4. All prime powers, including 2, with no large-index restriction

Fix a prime p and e>=1 with p^e|r. Suppose n=0 or1 modulo p^e. We prove p^e|S_l(n) for every l>=0. If l>=n, this is immediate from (4). Otherwise let m=l+1, so 1<=m<=n, and rewrite (4) as

    S_l(n)=(n+r-1)binom(n,m)binom(n+r+m-2,m-1).          (5)

If n=1 modulo p^e, the factor n+r-1 alone suffices.

If n=0 modulo p^e, put a=v_p(n)>=e and t=v_p(m), s=min(e,t). The identity m binom(n,m)=n binom(n-1,m-1) gives

    v_p binom(n,m) >= max(0,a-t) >= max(0,e-t).

For the other binomial, its complementary parts are m-1 and n+r-1. Both numbers are congruent to -1 modulo p^s. Therefore their last s base-p digits are all p-1. Adding them produces a carry at each of those positions: the first sum is 2p-2>=p, and every later sum, with the incoming carry, is 2p-1>=p. Kummer's theorem gives

    v_p binom(n+r+m-2,m-1) >= s.

For completeness the carry count follows also from Legendre's formula v_p(z!)=(z-s_p(z))/(p-1); each base-p carry decreases the combined digit sum by p-1. This proves the invoked version of Kummer directly. The two lower bounds total max(0,e-t)+min(e,t)=e. The remaining factor in (5) is integral, so p^e divides (5).

When m=1, t=s=0 and the first binomial is n, supplying all e factors. When p=2 the first carry is 1+1=2 and every subsequent one is 1+1+1=3, so the argument is unchanged. It never requires m<p^e, or a unit factorial, or n to equal p^e.

## 5. Sufficiency and necessity

Apply (2) in (1) and interchange two finite sums:

    N[i,j] = sum_l A(i,j,l) S_l(n).

Each coefficient is an integer and Section 4 makes every S_l(n) divisible by every maximal prime power p^v_p(r). Their pairwise coprimality gives r|N[i,j]. Equation (1) proves integral inverse entries. For r=1 this is immediate with no prime factors to consider.

Conversely P_0(k)=1, so (1) gives

    (R^-1)[0,0] = n(n+r-1)/r = n+n(n-1)/r.

Integrality of the inverse implies r|n(n-1). Since consecutive integers are coprime, a prime power dividing their product divides one of them entirely. This proves the stated equivalence, including n=1, arbitrary mixed CRT alternatives, every index, and every positive n,r.

## Scope and novelty boundary

The proof establishes the full ordinary source endpoint, not the stronger exact common-denominator law observed in r1, nor uniqueness in the literature. The beta/Jacobi kernel, integral linearization mechanism, telescoping and carry theorem are classical tools. The exact comparison and remaining prior-art/access limits are in discovery.md. No Lean certificate, manuscript, acceptance, count update, or external publication is part of this task.
