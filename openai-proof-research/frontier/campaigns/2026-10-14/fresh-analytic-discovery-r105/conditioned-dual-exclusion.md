# Conditioning away sparse annihilators: an exact surviving ensemble

Author derivation, not an independent review. Full frozen single-lattice target remains unchanged and open. This note continues the cube obstruction rather than asserting that an annealed obstruction rules out favorable lattice selection.

Use exactly n=p, r, l, a, mu and S={1,...,l}^n from construction-a-upper-tail-obstruction.md. Put W=U^perp, a uniform (n-r)-subspace of F_p^n. Let

 s=floor((log R)n/(8 log n)),
 E={W contains no nonzero vector supported on at most s coordinates}.

## 1. The conditioning has exponentially small cost

Let D_s be the set of projective lines having a representative with support at most s, and M_s=|D_s|. Then

 M_s <= sum_(j=1)^s binom(n,j)(p-1)^j <= s(np)^s.

A fixed nonzero vector belongs to W with probability

 theta=(p^(n-r)-1)/(p^n-1) <= 2p^(-r).

Consequently

 P(E^c)<=M_s theta<=exp(-(3/4)(log R)n+o(n)).

Indeed log M_s <= log s+2s log n <=(log R)n/4+o(n), while r log p>=n log R+log(n log n). No independence is assumed. In particular E excludes EVERY coordinate-codimension alignment used in the earlier obstruction, already by excluding its coordinate annihilators. Conditioned U still defines one genuine lattice; no coset union has been substituted.

## 2. Exact conditional pair control

Fix a line w not in D_s. Conditional on w subset W, a distinct line v belongs to W with probability

 theta_2=(p^(n-r)-p)/(p^n-p)<=2p^(-r).

This follows by quotienting by w, not by assuming independent membership. Therefore

 theta(1-2M_s p^(-r)) <= P(w subset W and E) <= theta.

Dividing by P(E), uniformly over every nonsparse w,

 P(w subset W | E)=theta(1+O(M_s p^(-r))).

Sparse lines have conditional probability zero. These bounds hold simultaneously as numerical probability estimates; they do not assert joint independence of a collection of lines.

## 3. Exact Fourier variance after conditioning

Write psi(t)=l^(-1) sum_(j=1)^l exp(2 pi i t j/p) and Psi(xi)=product_i psi(xi_i). For N_U(X)=|S intersect(X+U)|, finite-group Fourier inversion gives

 N_U(X)/mu = sum_(xi in W) Psi(xi) exp(-2 pi i xi.X/p).

Signs can be reversed without changing any conclusion. Thus Parseval gives

 E_X |N_U(X)/mu-1|^2 = sum_(0!=xi in W)|Psi(xi)|^2.

The one-coordinate identity sum_t |psi(t)|^2=p/l=a^(-1) yields total nonzero weight a^(-n)-1. The weight on vectors supported on at most s is exactly

 L_s=sum_(j=1)^s binom(n,j)(a^(-1)-1)^j = exp(o(n)).

For the last bound use s=O(n/log n), binom(n,j)<= (en/j)^j, and a^(-1)->R. On the other hand a^(-n)=exp((log R+o(1))n). Hence L_s/a^(-n)->0 exponentially. Applying the uniform conditional inclusion estimate from section2 and summing the nonnegative Fourier weights proves

 E_[U|E] E_X |N_U(X)/mu-1|^2
 = (1+o(1)) theta a^(-n)
 = (1+o(1))/mu.

This is a genuine quantitative estimate for a conditioned single-lattice model. It shows that the earlier rare cube alignments can be removed at exponentially small ensemble cost without damaging the natural second-moment scale. It does NOT give the required exp(-n log n-O(n)) high-overlap tail: Chebyshev still gives only O(1/mu) at a fixed multiple of the mean. Conversely a variance of order1/mu is fully consistent with the desired exponential tail, so it is not another impossibility assertion.

## 4. What a higher-moment replacement must actually estimate

For distinct z_1,...,z_k in S with affine rank d, the unconditioned joint inclusion probability is exactly

 p^(r-n) product_(i=0)^(d-1) (p^r-p^i)/(p^n-p^i),

with value zero for d>r (and the empty product for d=0). First require z_1 in X+U, then the d independent differences in U. Therefore factorial moments are sums over affine ranks, not sums of independent Bernoulli terms. The conditioned probability is this expression multiplied by

 P(E | span{z_i-z_1} subset U)/P(E).

Under that conditioning W is a uniform (n-r)-subspace of the annihilator of the difference span. If the latter forces a sparse vector into W, the numerator is zero; in general it is not equal to P(E). Thus section2 cannot be applied to replace ALL these factors by1, especially when d grows. The desired Chernoff exponent uses k of order mu~n log n, whereas r~n/log n. Almost all such tuples are necessarily linearly dependent if they contribute. A proof must bound their actual convex-box incidence count and the conditional annihilator factor; ordinary independent-point Chernoff is unavailable.

No source lower-hole completion has yet been coupled to this conditioned distribution. Even an upper-tail estimate would leave that joint choice obligation. The established source and primary reading ranges remain those in reading-limits.md; sections1-4 above are finite-group deductions, not newly attributed primary theorems.
