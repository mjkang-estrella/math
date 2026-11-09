# W009 — enforce odd symmetry with one sampled anchor

2026-10-08. Parent constructive variation, PROVISIONAL. This is not in
the frozen reciprocal-law or simple-pole audits. No experiment or factoring
bound. It changes the anchor acquisition, rather than assuming favorable
independent samples.

Start P(X)=X and maintain an odd projective map. Draw one uniform residue r,
evaluate y=P(r), and gcd-check a finite nonzero chart. Acquire the opposite
anchor as P(-r)=-y without a second circuit evaluation. Since N is odd,
the anchors differ by the unit 2y. Update

    F_y(z)=(z-y)*(z+y)/z=z-y^2/z,
    [U:V] -> [U^2-y^2*V^2 : U*V].

The map remains odd, with no basepoints, and retains the simple pole at
infinity. This deterministically removes the output translation y+w.
It saves one training evaluation per stage and guarantees a particular
symmetry. Acquisition remains O(k^2), probes O(k): this alone is a constant
improvement, not an exponent change.

For a fixed local odd map on uniform affine inputs, nu(z)=nu(-z). Write
s=sum nu, v=sum nu^2, u3=sum nu^3, and Gamma(c) as in the two-anchor note.
A local chart is legal with probability s, rather than s^2-v. For a legal y,

    m_new-m=2*nu(y),
    v_new-v=Gamma(-y^2)-4*nu(y)^2.

Therefore its raw moments are

    E[1_legal*(m_new-m)]=2*v,
    E[1_legal*(v_new-v)]=sum_y nu(y)*Gamma(-y^2)-4*u3.

The selected product -y^2 is NOT sampled with weight Gamma; the previous
squared-energy identity must not be reused. This trades merger-mass bias
for paid deterministic symmetry and a less restrictive chart. For a fixed
composite map, raw accepted updates multiply these moments by s at the
other prime under the no-op full-tape protocol.

The collision input c=-y^2 is always a nonsquare when p=3 mod4 and a
square when p=1 mod4. For the actual uniform affine start this fixes the
first-step residual mass at (2p-6)/p^2 or (2p-8)/p^2, respectively.
For p=3 mod4 the finite involution has no fixed points. This is a concrete
local difference, but the rational trace image need not be preserved by
the next acquired involution.

The frame-alignment question becomes precise: c_next=4c requires
y_next=+/-2y. Asking the same fold to produce 2y requires a preimage
z/y=1+/-sqrt(2). Such roots modulo N are not supplied by the symmetry.
Choosing all y_next=2y as arbitrary constants is cheap, but forfeits the
sampled-fiber acquisition promise and returns the known torus powering
construction. A general claim that frame alignment is a rare iid event
is wrong for this correlated generator; a useful aligned next fiber is
still unpaid.

A diagnostic character formula makes the next gate concrete. With
C=nu*nu, M(eta)=sum nu(x)eta(x) and quadratic character chi,

    sum_y nu(y)*C(-y^2)
      =(1/(p-1))*sum_eta M(eta)^2*conj(eta(-1))*M(conj(eta)^2).

The trivial and quadratic characters have to be separated; eta^2 can be
trivial even when eta is not. If all nontrivial coefficients have magnitude
at most delta, Parseval gives the upper bound

    s^3/(p-1)+s*|M(chi)|^2/(p-1)
      +delta*(v-s^2/(p-1)-|M(chi)|^2/(p-1)).

The simple-pole character bound can potentially control early depths here
too. The materially different outstanding question is whether the acquired
odd family preserves a stronger correlation at later depth, or permits
cheap acquisition of the aligned next fiber. Neither follows from degree,
no fixed points, or the first-step mass. Do not select a depth sweep before
this law and a decisive success criterion are audited/preregistered.
