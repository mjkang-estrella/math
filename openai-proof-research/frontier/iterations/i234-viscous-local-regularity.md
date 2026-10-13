# I234 — local regularity for the viscous limiting equation

**Verdict: NOT CLOSED.** I did not prove the required local spatial-gradient modulus for every bounded continuous viscosity solution. The cited primary results do not provide it with the required hypotheses. No counterexample to that statement or to the entire all-fit rigidity statement is claimed. No tenth finding is nominated.

## Exact target and source boundary

For every d>=1, tau>0 and M<infinity, the desired theorem would assign K<infinity and omega(s)->0, depending only on d,tau,M, such that every continuous viscosity solution of

    V_tt+2D_xV.D_xV_t+D_xxV[D_xV,D_xV]+tau Delta_xV=0

with oscillation at most M on B_1 x (-1,1) has classical D_xV on B_(1/2) x (-1/2,1/2), bounded by K and with common modulus omega in space-time. Upper tests satisfy the displayed operator >=0; lower tests satisfy <=0. No initial gradient, density, energy or Hessian bound is assumed.

I read the actual pinned introduction and Liouville statement in 03-reduction.tex, using the existing non-live corpus. The stipulated homogeneous result has no transverse trace term and cannot be substituted here. All pinned results and lower operations remain accepted. I did not read the live I231 or I230 directories or any independent gate.

The principal matrix is

    A(p)=[[tau I+p tensor p,p],[p^T,1]].

Its quadratic form is tau|xi|^2+(p.xi+eta)^2, but its least eigenvalue is at most tau/(1+|p|^2). Strict convexity of exp((V_t+|D_xV|^2/2)/tau) likewise gives no global uniform ellipticity. Smooth-test transformations do justify the parent's scaling and Galilean invariances for viscosity solutions.

## What was paid, and what was not

The full calculations are in [analytic-attempt.md](../experiments/i234_viscous_local_regularity/analytic-attempt.md).

1. **Bernstein route.** For smooth V, write h=|D_xV|^2/2, w=V_t+h, k=V_t+2h and L=A:D^2+2D_xw.D_x. Then Lh=|D_xw|^2+tau|D_xxV|^2, LV_t=0, and L(V^2/2)=tau|D_xV|^2+k^2+2V D_xV.D_xw. These identities yield a fully checked weighted bound on a smooth spatially periodic slab: V_t+(3/4)|D_xV|^2<=C(M,tau)(t^(-2)+(T-t)^(-2)+1). It does not bound D_xV alone. Localizing in space introduces the precise uncontrolled terms in (A4)–(A5); the proof remains unpaid there.
2. **Fit-restricted route.** The exact all-scale fits imply uniform value moduli r(1+log(1/r)) in space and r(1+log(1/r))^2 in time for a bounded normalized family. Their dyadic spatial slope differences are only bounded by 3C0; they are not summable. This supplies no derivative modulus. The missing improvement must use the changed PDE.
3. **One-dimensional hodograph route.** Where a smooth solution's Hessian is invertible, its local Legendre transform, followed by r=q+p^2/2, satisfies W_pp+tau W_rr+W_r=0. The gradient-image domain and inverse map have no control from the stated hypotheses. This conditional identity does not treat arbitrary viscosity solutions.

Sánchez Morgado's [equation (4) and smooth periodic theorem](https://arxiv.org/abs/1712.10275v1) concern the matching operator but not arbitrary local solutions. Porretta's [equation (1.7), Theorem 3.4, Theorem 6.5 and Proposition 7.2](https://arxiv.org/abs/2203.04856v2) use a global planning problem; boundary data or an already obtained gradient bound enter the relevant conclusions. His time-local result controls a combination of gradient and log density, not a gradient independently of a density lower bound. Muñoz's [introductory formulation](https://arxiv.org/abs/2006.07367v2) corroborates this distinction; I did not import a theorem from its unread later sections.

## Precise remaining bridge

Either prove the estimate directly for all continuous viscosity solutions, or provide both:

* a genuinely local smooth-solution spatial-gradient bound and modulus controlled solely by oscillation, d and tau;
* local approximation/identification covering every continuous viscosity solution, with those same uniform estimates.

A proof restricted to variational or global smooth planning solutions does not cover the quantifier “every.” Passing an already common derivative modulus from smooth approximants to their uniform limit is elementary by integration on spatial segments; existence of those approximants and their estimates is the unsupplied part. A fit-specific version would suffice for the parent, but the logarithmic value estimates alone do not give it.

Reading limits and failed routes are in [reading-and-failures.md](../experiments/i234_viscous_local_regularity/reading-and-failures.md), sources in [literature.md](../sources/i234_viscous_local_regularity/literature.md), and provenance in [input-authentication.json](../experiments/i234_viscous_local_regularity/input-authentication.json). Only assigned files and fully read primary excerpts were written. No subordinate agents, research code, tests, scans, experiments, snapshots, seals, shared edits, staging, commits or publication were used.
