# Dense obstruction normals survive coordinate-sparse dual conditioning

This author proof continues the precise ensemble in construction-a-upper-tail-obstruction.md and conditioned-dual-exclusion.md. It leaves the full frozen arbitrary-convex-body existence target open. The obstruction below is to FIXED-COORDINATE conditioning; body-dependent exclusions remain possible.

Fix R>=4 and C>0, and use p=n, r,l,a,mu and s from those notes. Choose fixed q with R^q>4(C+1). For all sufficiently large primes n, q<n-r and n-q+1>s.

## 1. An integer-unimodular change with dense obstruction normals

Enumerate all elements t_1,...,t_n of F_p. The q-by-n Vandermonde matrix D has entries D_ij=t_j^(i-1). Its row space D_0 has dimension q. Every nonzero element has at most q-1 zero coordinates: it evaluates a nonzero polynomial of degree at most q-1 at n distinct points. Hence its Hamming support is at least n-q+1>s.

Extend these q rows to an invertible n-by-n matrix over F_p. Rescaling its last row makes determinant1 without changing the first q rows; call the result Bbar. It has an integer-unimodular lift B in SL_n(Z). For completeness, elementary row elimination over a field expresses any SL_n matrix as a product of elementary transvections. A diagonal pair diag(t,t^(-1)) is also a product of transvections, by the usual two-dimensional elimination, so determinant-preserving elimination suffices. Lift each transvection coefficient to an integer; its determinant remains1, and the product reduces to Bbar. Let A=B^(-1), also integer-unimodular.

Set K=A[0,a]^n. Because A Z^n=Z^n and A(p^(-1)Z^n)=p^(-1)Z^n, the coarse packing supremum and covering infimum are still both1/a, and the fine grid covers (1/l)K. Volume and lattice determinant are unchanged. Thus this is an arbitrary convex parallelotope satisfying exactly the previous affine discretization promises, not a nonconvex set.

## 2. The alignment event is now invisible to sparse exclusion

Let U be a uniform r-subspace, W=U^perp, and E={W has no nonzero vector of support<=s}. Put V=ker D, and F={U subset V}, equivalently {D_0 subset W}. The earlier subspace count gives P(F)>=(1/2)p^(-qr).

No sparse nonzero vector belongs to D_0. For each sparse projective line v, quotienting by D_0 gives

 P(v subset W | F)=(p^(n-r)-p^q)/(p^n-p^q)<=2p^(-r).

Consequently P(E^c | F)<=2M_s p^(-r)=o(1), with M_s as in the conditioned-dual note. This estimate explicitly retains the dependence among all membership events; it uses a union bound, not independence.

## 3. Conditional high-overlap volume

Multiplication by B preserves coarse-torus Haar measure and sends Lambda_U to Lambda_(Bbar U). Conditional on F, Bbar U is uniform among r-subspaces whose first q coordinates vanish. It sends K back to the original cube. The continuous overlap-volume calculation and rank-two moment computation from the original obstruction therefore apply exactly.

For a Haar translate, the first q transformed cell coordinates are active with probability a^q. This event depends only on the translate and is independent of U, F, and E. Given activity and F, the remaining intersection count has mean mu'=mu/a^q and variance at most mu'+mu'^2/(p^(n-q)-1). Hence its conditional probability of exceeding Cmu tends to1. Subtracting P(E^c|F)=o(1), for all sufficiently large n,

 P(N>Cmu and E | F, activity)>=1/2.

It follows that

 E_[U|E] Haar{x:m_(K,Lambda_U)(x)>Cmu}
 = P(N>Cmu and E)/P(E)
 >= (a^q/4)p^(-qr)
 >= exp(-q(log R)n-O_(C,R)(log n)).

Thus coordinate-sparse dual conditioning, despite preserving the natural variance scale, still cannot give the required exp(-n log n-O(n)) annealed tail uniformly over convex bodies satisfying the stated affine coarse/fine promises.

## Exact boundary of the result

This does not forbid first choosing a body-adapted basis and then excluding its sparse dual vectors. For this parallelotope the basis A trivializes the body, and a tiling lattice is already available. Nor does it imply that typical conditioned lattices fail, since F is rare. It identifies a requirement on any viable uniform construction: exceptional normals must be defined from the body, not only from an externally fixed coordinate support. No new primary theorem is invoked in this finite-field argument; existing source and primary reading limits are unchanged.
