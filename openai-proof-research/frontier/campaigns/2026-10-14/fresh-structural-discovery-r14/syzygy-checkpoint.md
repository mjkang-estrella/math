# Checkpoint 3: a necessary finite-field behavior, not a contradiction

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Let k be a finite field, A a finite-dimensional self-injective k-algebra,
and M a finite-dimensional nonprojective module. If Ext_A^i(M,M)=0 for
EVERY i>=1, then the dimensions of its successive minimal syzygies tend
to infinity. This elementary necessary condition does not disprove FT2.

Over a self-injective algebra, syzygy Omega is invertible on the stable
category: choose an embedding into a projective-injective for its inverse;
the elementary comparison of the two short exact sequences makes the
two composites stably identity. Also

 Ext_A^d(M,M) = stable Hom_A(Omega^d M,M), d>0.

If Omega^j M and Omega^l M are isomorphic for 0<=j<l, apply the stable
inverse Omega^{-j}. This gives a stable isomorphism Omega^{l-j} M -> M.
Its stable class is nonzero, because the identity of M is nonzero in the
stable category: if it factored through a projective, M would be a
projective direct summand. This contradicts Ext^{l-j}=0.
Thus all the syzygies are pairwise nonisomorphic, even stably.

For each fixed integer D, there are only finitely many A-modules over k
of dimension at most D. If a=dim_k A and |k|=Q, the number of module
structures on k^d is at most Q^{a d^2}, since the action of a fixed basis
of A is specified by a matrices of size d. Associativity and unity only
reduce this number. Consequently at most

                      sum_{d=0}^D Q^{a d^2}

syzygies can have dimension at most D. Each D has finitely many such
indices, proving dim Omega^j M -> infinity. This does NOT give a specified
lower bound for each individual index j: a bound on the number of visits
to small dimensions does not bound the last such visit.

For a pair whose vanishing is known only in degrees 1,...,r, the same
argument only forbids repeats whose index difference is <=r. In
particular its first r+1 syzygies are pairwise nonisomorphic. This is
compatible with the finite-window pairs in checkpoint 2. Neither bounded
syzygies nor periodicity was imposed in original-scope.md, so this
necessary condition cannot be used as a negative answer to FT2.

This argument is elementary finite-state counting and stable periodicity.
Schulz's work on bounded modules is a primary antecedent for the periodic
versus parameter-shifting distinction. It is not a substantial result
nomination. A possible finite-field construction must leave the bounded
syzygy template; no construction with the full vanishing was found.
