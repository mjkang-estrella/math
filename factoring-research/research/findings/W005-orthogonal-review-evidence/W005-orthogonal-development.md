# W005 B — orthogonal-pair escape and its concrete generation problem

Date: 2026-10-08. **PROVISIONAL parent derivation, not yet independently reviewed.**
This note was developed after launching the first B review; it is not in that
review's frozen assignment. Preserve that task. A later review must include
both its result and this response. No experiment or numerical search ran.

The reflection proposal has a specific likely defect: its useful quaternion
gcd is already visible in a scalar dot-product gcd. A materially different
case occurs when the scalar test gives the full modulus at every prime, but
left versus right orientation differs. Exact orthogonality forces precisely
that scalar degeneracy. It deserves a direct extraction criterion.

## Proposed extraction lemma, including all odd prime powers

Let A,B be integer-coordinate quaternions, with

    Norm(A)=Norm(B)=N odd, and <A,B>=0.

Identify their coordinate columns with a,b. Put

    V=B*conjugate(A), W=conjugate(A)*B,
    g_V=gcd(N,V_i,V_j,V_k), g_W=gcd(N,W_i,W_j,W_k).

V and W are pure and each has norm N^2. The proposed identity is

    L_V R_W = N^2 I_4 - 2N*(a*a^T+b*b^T),

where L_V,R_W mean real left/right multiplication on quaternions.

Proof: these two commuting skew-symmetric multiplication matrices have
symmetric product. That product has square N^4 I, has eigenvalue -N^2
on A and B, and has trace zero. Its other two eigenvalues are therefore
+N^2. Since A,B are orthogonal with squared length N, the displayed
orthogonal-projector formula follows. Trace zero also follows directly from
trace(L_u R_v)=4 Re(u)Re(v).

For e_i,e_j in {i,j,k}, the nine matrices L_(e_i) R_(e_j) are pairwise
orthogonal for the Frobenius inner product, each with squared norm 4.
Taking their inner product with the displayed identity shows

    N divides 4*V_i*W_j, hence N divides V_i*W_j since N is odd.

At each p^e dividing N, minimum coordinate valuations consequently give
v_p(g_V)+v_p(g_W)>=e. Thus N divides g_V*g_W, without a squarefree
assumption or knowledge of the primes in the algorithm.

If g_V=N, then V=N*u with u a pure integer quaternion of norm 1,
so u is one of +/-i,+/-j,+/-k and B=u*A.
If g_V=1, then g_W=N, giving B=A*u for one of the same six units.
Therefore any orthogonal B of equal norm that avoids the at most twelve
vectors u*A and A*u necessarily gives **1<g_V<N**.

This is a deterministic polynomial-bit extraction from a supplied pair,
not a way to obtain the pair. No quaternion gcd implementation is needed:
two products, integer gcds, and checking the norm/orthogonality suffice.
All input coordinates have O(log N) bits. The obvious twelve exceptions
can be listed and compared at polynomial cost. Some exceptions themselves
might yield other gcd information; the sufficient criterion does not claim
they all fail.

## An actual finite generator, and why its current cost is uncompetitive

Given a primitive A, compute a rank-three integer basis H for
L={z in Z^4: <A,z>=0} by extended gcd/Hermite reduction. Its covolume
is sqrt(N). Reduce H if desired, charging reduction, and put G=H^T H.

For every coordinate t_i of a vector Ht of squared length N, exact
Cauchy-Schwarz gives

    |t_i| <= floor(sqrt(N*(G^(-1))_ii)) = B_i.

Choose the two smallest B_i, enumerate their two integer coordinates,
and solve the remaining integer quadratic equation exactly using its
discriminant and divisibility conditions. For every solution, reconstruct B,
reject the twelve exceptions, and use the extraction lemma. This is an
explicit search, including finite termination and output checking. Its
cost is bounded by

    C_A + C_basis + O((2B_1+1)*(2B_2+1)*poly(log N)),

where C_A includes obtaining A and widths of any chosen basis algorithm
must be bounded. No fast all-input sampler or favorable basis shape is
granted. If there is no nonexceptional pair, report failure at that scope.

In an isotropic geometry with basis lengths about N^(1/6), these coordinate
bounds are about N^(1/3), so the two-coordinate scan is about N^(2/3).
That is a shape diagnostic, not a proved average or worst-case count.
It already gives no reason to expect a factoring improvement. LLL finds
short vectors in the ball; it does not directly find an exact vector on the
specified sphere or remove the twelve exceptional answers.

The next computation to change is now precise: solve the exact ternary
quadratic equation t^T G t=N while excluding those known points, with
less total work than the appropriate factoring comparator. A proposed
binary-slice prime search must pay for the slice discriminant, class
membership, prime generation and failed slices. Calling fixed dimension
or a short lattice basis a fast exact-shell solver is invalid.

## The rational-rotation version exposes the same integral constraint

Another explicit representation asks for a pure integer quaternion C with

    Norm(C)=N^2, C*A=0 mod N,

and sets B=C*A/N. Then B is integral, orthogonal to A and has norm N.
The congruence lattice can be constructed by integer linear algebra;
the norm equation remains. It is a denominator-N transformation, so it
changes the failed unit-denominator reflection representation materially.
It does not grant division by N in modular arithmetic.

A shorter rational rotation with a denominator coprime to N preserves the
same local orientation at every prime. Merely changing its rational
parameter cannot produce the mixed orientation needed here. A denominator
with proper gcd already factors N; full-modulus denominators require the
paid integral constraint above.

## Primary prior art checked; no novelty assertion

This general research route is already present in
[Machiavelo–Rocadas, Connections between the arithmetic and the geometry of
Lipschitz integers](https://cmup.fc.up.pt/main/sites/default/files/publications/Quaternions_AM_LR.pdf).
Its introduction explicitly motivates orthogonal four-square pairs for
factoring. Lemma 4.2 supplies an orthogonal-lattice basis; Theorems 4.3–4.4
show why natural vector-product constructions preserve left/right multiples.
Thus an unmodified cross-product generator is not a new escape.

[Kiss–Kutas, Cubes of integral vectors in dimension four](https://ewkiss.web.elte.hu/wp/wordpress/wp-content/uploads/2014/11/Int4vec9.pdf),
Lemma 3.3 and Theorem 3.5, classify local common divisors and express an
orthogonal tuple as gamma*epsilon_i*delta. This supports the need to charge
the factor-bearing decomposition; it is not a polynomial-time construction
from an unfactored N.

Read scope: the former's introduction, Lemma 4.2, Theorems 4.3–4.4 and final
remarks; the latter's Lemmas 3.1–3.4 and Theorem 3.5, including the displayed
proofs. PDF conjugation marks require visual inspection; the retained
extraction lemma above is independently derived rather than trusting text
extraction with missing bars. PDFs and hashes are in W005-parent-sources.
No claim of a complete literature survey or novel reduction follows.

This branch bypasses relation collection and makes useful-pair recognition
cheap and exact. The unresolved part is the generator, for which an honest
finite baseline is now specified. The parent will investigate a different
exact-shell computation while the already-running reflection audit finishes.
