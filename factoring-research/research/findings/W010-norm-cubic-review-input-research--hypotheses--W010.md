# W010 — norm-selected odd cubic concentration

2026-10-08. Parent constructive candidate, PROVISIONAL.
No experiment, installed solver, Lean change or factoring improvement.
This keeps a zero-absorbing odd polynomial, merges two signed sampled
pairs at once, and uses no reciprocal chart or power-subgroup promise.
It is a new acquisition rule; earlier polynomial/reciprocal envelopes
do not automatically apply.

## Executable mechanism

Maintain a monic odd polynomial by its circuit, initially P(X)=X.
Take two fresh uniform residues modulo a remaining N=pq, p,q>3, and
evaluate z=P(r), u=P(s). Test z,u,z-u,z+u individually by gcd.
A proper gcd returns a factor. A full failure is a paid no-op under a
fixed raw-attempt budget. On the unit chart set

    beta=z^2+z*u+u^2,
    P_new=P^3-beta*P.                                           (1)

Beta need not be a unit. There is no division or square root. An optional
gcd(beta,N) would be an additional success channel and is not included
in the initial protocol. Every current map remains monic and odd;
zero is absorbing.

The exact identity is

    F_beta(T)-F_beta(z)=(T-z)*(T-u)*(T+z+u),
    F_beta(z)=F_beta(u)=F_beta(-z-u)=-z*u*(z+u).                   (2)

Thus the two actually sampled fibers z,u merge; their distinct negatives
merge into the opposite output. The third value -z-u also merges if it
is in the current image. Its presence is not assumed or supplied as an
oracle. The legal chart ensures the two outputs are nonzero and opposite.

Each update/probe stage needs a fixed number of modular operations.
Fresh parameter acquisition through depth k still costs O(k^2), and a
probe costs O(k); odd symmetry supplies negative anchors without extra
evaluations. The proposed saving would be a faster concentration of
nonzero fibers before a final absorption step, not cheap circuit evaluation.
The final step P*(P-a), a=P(r) from one paid fresh sample, can absorb a
mass-biased fiber; its cost and CRT success remain charged.

## Exact proposed sampler and drift

Fix one current odd map over F_p. Its output law mu is symmetric.
Write m=mu(0), let nu be the nonzero residual law, and set
s=sum nu, v=sum nu^2, q4=sum nu^4. Define Q(z,u)=z^2+z*u+u^2 and

    K(beta)=sum_(z,u!=0; z!=u; z!=-u; Q(z,u)=beta) nu(z)*nu(u),
    A(beta)=sum_(a!=0; a^2=beta) nu(a)^2,
    B(beta)=sum_(a!=0; a^2=beta) nu(a).

All ordered pairs are counted. Symmetry gives
sum K=s^2-2v=:ell. This is the raw legal probability; when ell=0
the conditional acquired-parameter law is undefined. When ell>0 it is
K(beta)/ell. The sampler measures no K.

The full off-diagonal collision gain at fixed beta has three disjoint
parts: K(beta), the opposite pairs A(beta), and the pairs involving zero
2m*B(beta). Also m_new=m+B(beta).
Symmetry implies B(beta)^2=2A(beta), including beta=0 or a nonsquare,
where both sides are zero. Subtracting the new atom square yields

    v_new-v=K(beta)-A(beta),
    m_new-m=B(beta).                                            (3)

Consequently the actual raw moments are

    E[1_legal*Delta v]=sum_beta K(beta)^2-sum_beta K(beta)*A(beta),
    E[1_legal*Delta m]=sum_beta K(beta)*B(beta).                  (4)

This supplies an executable bias toward the relevant quadratic-form
merger mass. Unlike the reciprocal sampler, it does not automatically
remove the two sampled heavy fibers into marked atoms. However the
root-removal term in (4) can still defeat a gain for a weighted law.
No universal monotonicity or reachable-law persistence is asserted.

For a flat symmetric residual support of size M, mass d=s/M per point,
every legal pair forces the four distinct ordered pairs
(z,u),(u,z),(-z,-u),(-u,-z). Thus K(beta)>=4d^2, while A(beta)<=2d^2.
This gives pointwise Delta v>=2d^2. The post-update law is generally
nonflat, so this one-step property cannot be iterated without proof.

## The actual uniform start, not an idealized distribution

Let epsilon=chi(-3), h=chi(3), C=p-epsilon-4 and D=3+h.
At uniform affine input nu=1/p on F_p^*, let k_beta=p^2*K(beta).
The standard nonsingular binary-quadratic count, followed by deletion
of zero coordinates and the two diagonals, proposes

    k_0=(p-1)*(1+epsilon),
    k_beta=C-D*chi(beta),              beta!=0,
    ell=(p-1)*(p-3)/p^2.                                     (5)

One can derive the count by completing the square:
4Q(z,u)=(2z+u)^2+3u^2. It is not a heuristic random-parameter law.
At nonzero beta, the original conic has p-epsilon points; remove
2*(1+chi(beta)) zero-coordinate points, 1+chi(beta/3) diagonal points,
and 1+chi(beta) opposite points. These deletions are disjoint for p>3.

Equations (3)-(5) give the proposed exact conditional means

    E[Delta v | legal]
      =[(p-1)*(1+epsilon)^2+C^2+D^2-C+D]/[p^2*(p-3)],
    E[Delta m | legal]=(C-D)/[p*(p-3)].                         (6)

In particular the first residual collision mass is 2/p+O(1/p^2),
and root mass is 2/p+O(1/p^2). No first-step exponent gain follows.
The potential difference is the subsequent weighted quadratic incidence,
not initial formal degree three or the number of planted pairs.

## Complete acquisition and recovery obligations

At a fixed map modulo N, fresh CRT samples are independent and the joint
clean probability is ell_p*ell_q. The raw local drifts in (4) multiply by
the other prime's ell in the no-op full-tape process. The accepted histories
are correlated across primes. Zero/full gcds and all unstarted stages stay
in the ledger; a clean-law formula is not a factoring success probability.
Every intermediate zero remains an endpoint zero, but extra coefficient
or derivative gcds would change the protocol.

A cheap-looking reservoir shortcut has an explicit debt. In a fixed pool
of input samples, applying the current global update to every stored value
merges at least the two distinct sampled classes on every accepted step.
Without replenishment, a pool of M distinct values supports at most M-1
such steps; if signed pairs are stored, the drop can be larger. Updating
all M values at every stage costs O(M*k). A fresh input evaluated through
the full circuit costs O(k). This closes only that literal pool scheme;
it is not a lower bound on lazy or structurally compressed acquisition.

The decisive mathematical gate is (4) for REACHABLE weighted laws:
does its non-forced quadratic-form energy create useful concentration
soon enough to pay for the k^2 training and final probes, or is its drift
only the generic 1/p scale? An arbitrary flat support or a favorable
quadratic-form count does not establish this. A cheap exact audit should
first validate (2)-(6), seek a weighted symmetric counterexample to any
attempted monotonic extension, and isolate the forced contribution.
A depth sweep is not selected until that calculation identifies a
quantitative candidate advantage and a preregistered rejection criterion.

The scalar-product branch W008 remains separate: an improved collision
detector could save work without requiring the concentration claimed here.

