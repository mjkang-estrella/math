# Convex-cube obstruction to an annealed Construction-A upper-tail estimate

This is an author proof about a precise random-neighbor architecture. It leaves the full frozen thin-covering existence target unchanged and unrefuted. In particular cubes themselves tile. No independent review or contribution verdict is asserted.

## Statement

Fix R>=4 and any constant C>0. Along primes p->infinity, with n=p, there are cubes K_n and random single lattices Lambda_U, each of normalized volume density mu_n=Theta_R(n log n), such that

 E_U [Haar measure of {x mod Z^n: m_(K_n,Lambda_U)(x)>C mu_n}]
 >= exp(−c_(C,R)n−O_(C,R)(log n)).

The coarse lattice Z^n packs K_n, its packing and covering dilation factors agree, and the fine grid p^(-1)Z^n covers sK_n with s=O_R(1/n). Thus the example respects convexity and the basic geometric discretization promises used in the paid neighbor reduction. It rules out an upper bound exp(−n log n−O(n)) for the ANNEALED upper-tail volume in this model, for every fixed multiple C of its mean.

## 1. Parameters and a genuine single lattice

Let rho=n log n and

 r=ceil((n log R+log rho)/log p),
 L=p(rho/p^r)^(1/n),  l=floor L,  a=l/p,
 K=[0,a]^n.

Then (p/R)p^(−1/n)<=L<=p/R, so a->1/R. For all sufficiently large p, L>=p/(2R), L>=2, and

 rho exp(−4R)<=mu:=a^n p^r=rho(l/L)^n<=rho.

Here log(1−1/L)>=−2/L and n=p prove the lower bound. Also r~n log R/log p=o(n), while r->infinity.

Let U be a uniformly random r-dimensional linear subspace of F_p^n. Set

 Lambda_U=Z^n+p^(-1)U,

where the right side means the full inverse image under p^(-1)Z^n->F_p^n. This is a lattice, not a selected list of independent cosets: it contains ALL p^r elements of U modulo Z^n, and det Lambda_U=p^(−r). Its density for K is exactly mu. Since a<1, distinct coarse translates of K are disjoint; both the coarse packing supremum and covering infimum dilation factors equal1/a. The fine grid covers (1/l)K because that cube has side1/p.

## 2. Exact identification with continuous overlap volume

Write a Haar-uniform x in the coarse torus as (j+delta)/p with j uniform in F_p^n and delta uniform in(0,1)^n, independently. Away from the null cell boundaries, the fine-grid points in x+K have residues

 j+S,  S={1,...,l}^n mod p.

Therefore m_(K,Lambda_U)(x), which also equals #(Lambda_U intersect(x−K)), has the same distribution as

 N=|S intersect(X+U)|,

with X uniform in F_p^n, independent of U (reflection and translation preserve uniform X). This is an exact distributional identity for the essential overlap-volume functional, not a statement only about a finite net. In particular E_(U,X)N=|S|p^(r−n)=mu.

## 3. A low-codimension alignment event

Choose a fixed positive integer q with R^q>4(C+1), and put

 V={z:z_1=...=z_q=0},  d=n−q.

For all large n, r<d. Counting ordered independent bases gives

 P(U subset V)
 =product_(i=0)^(r−1) (p^(n−q)−p^i)/(p^n−p^i)
 >=(1/2)p^(−qr).

Indeed after taking out p^(−qr), the numerator product is at least1−sum_i p^(i−n+q), which tends to1; each denominator factor is<=1.

Conditional on this event, U is uniformly distributed among the r-subspaces of V. The coset X+U meets S only when the first q coordinates of X lie in{1,...,l}. This active event has probability a^q. Given it, the remaining X coordinates are still uniform and independent of U; the count is the random affine-subspace intersection with S'={1,...,l}^d in F_p^d. Its conditional mean is

 mu'=l^d p^(r−d)=mu/a^q >=R^q mu>4(C+1)mu.

## 4. Exact rank-two second moment

For distinct z,z' in F_p^d,

 P(z,z' in X+U)=p^(r−d)(p^r−1)/(p^d−1).

This follows by first requiring z in the coset and then requiring the nonzero difference z'−z in its uniform direction. If M=|S'|, then

 E N(N−1)=M(M−1)p^(r−d)(p^r−1)/(p^d−1),
 Var N<=mu'+mu'^2/(p^d−1).

Thus P(N<=mu'/2)<=4/mu'+4/(p^d−1)->0. Since mu'/2>Cmu, the conditional upper-tail probability is at least1/2 for all sufficiently large n. Combining the two events,

 P(N>Cmu)>=(a^q/4)p^(−qr).

Since a>=1/(2R) eventually and

 r log p<=n log R+log rho+log p,

this is at least

 [4(2R)^q]^(-1) R^(−qn) rho^(−q) p^(−q)
 =exp(−q(log R)n−O_(C,R)(log n)).

This proves the statement.

## What this rules out, and what remains possible

The exact two-sided completion criterion at eta~1/n requires bad overlap volume smaller than exp(−n log n−O(n)). The present ANNEALED volume is much larger, even for cubes with coarse radius ratio1. Hence a first-moment proof that this random-neighbor ensemble supplies the required upper-tail volume cannot work unchanged. Likewise convexity plus coarse packing/fine covering does not justify replacing the subspace law by independent point sampling.

This does NOT rule out selecting favorable subspaces after excluding these alignments. The event used above has exponentially small probability, so its removal might preserve another useful event. It also does not establish that a typical subspace fails the target, that every single-lattice construction fails, or that the source's lower-hole mechanism can be combined with such a conditioning. A successful conditioned architecture must quantify every relevant low-codimension alignment, including noncoordinate ones selected by K, and prove enough remaining upper-tail control jointly with coverage.
