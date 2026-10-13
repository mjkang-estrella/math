# I230 — actual p-harmonic gradient convergence

**Verdict: unrestricted problem NOT CLOSED; no tenth independent finding.** There is a fully proved restricted actual-gradient rate, together with precise failures of the unrestricted anisotropic and local-excess routes. No gradient of a mollification is substituted for the actual p-harmonic gradient.

## Paid restricted estimate

For n>=2, 0<alpha<=1 and 0<m<=M, K>=0, there are explicit delta_0>0 and C<infinity depending only on alpha,m,M,K such that, for every p>=2:

* u is C² and p-harmonic on B1, has no critical points, and has convex strict superlevel sets in B1;
* v is C^{1,alpha} on B1, m<=|Dv|<=M and [Dv]_alpha<=K;
* ||u-v||_infinity=delta<=delta_0;

imply

    ||Du-Dv||_{L-infinity(B1/2)} <= C delta^{alpha/(1+alpha)}.

The approximation has no assumed uniform gradient modulus or quantitative gradient lower bound. Convex superlevels control the direction of its gradient from value comparisons. The actual p-equation gives nondecreasing |Du| along unit-speed ascending gradient flow, since (p-1)u_nn=-trace_{n-perp}D²u>=0. Forward and backward flow segments then bound its magnitude. The full proof, domain buffers and explicit constants are in [analytic-attempt.md](../experiments/i230_p_harmonic_gradient/analytic-attempt.md), Section 1.

For variational convex-ring potentials in dimensions n>=3, the known smoothness, nonvanishing and quasiconcavity of u_p, and nonvanishing of the infinity potential v, allow this lemma to be combined with the stipulated homogeneous C^{1,alpha_n} estimate. On every compact E inside the ring,

    ||Du_p-Dv||_{L-infinity(E)} <= C_E ||u_p-v||_infinity^{alpha_n/(1+alpha_n)}.

Bungert's value estimate and a fixed Lipschitz boundary extension give the actual rate

    O(p^{-alpha_n/(4(1+alpha_n))}).

Under the additional global positive essential infimum of |Dv| needed for Bungert's improved value estimate, the exponent becomes alpha_n/(2(1+alpha_n)). The constants depend on the ring and the interior compact set. This is not a uniform estimate up to the boundary.

Peng–Zhang–Zhou already prove qualitative C¹ convergence of these potentials in arbitrary dimension, using convex normals and one-sided slope estimates. The rate above quantitatively refines that argument using the stipulated Hölder bound. It is useful paid mathematics, but a standard transfer under the original contribution standard and therefore not nominated.

## Unrestricted route: the actual surviving viscosity

With epsilon=1/(p-2), the p-equation at nonzero test gradients is

    Delta_inf u + epsilon |Du|² Delta u=0.

The affine lift u(y)+b does not preserve it: the displayed operator has residual epsilon Delta u. In source cylinder coordinates

    u(z+r(sqrt(lambda)x,t))=u(z)+rc(t+lambda V(x,t)),

the exact equation is

    D²V[(D_xV,1+lambda V_t)]
      +(epsilon/lambda)[lambda|D_xV|²+(1+lambda V_t)²]
        (Delta_xV+lambda V_tt)=0.

Thus the parameter is epsilon/lambda, independent of r. I224's r/lambda selection cannot make it vanish. The regimes are:

* ratio ->0: the exact stipulated homogeneous limit;
* ratio ->nu>0: D²V[(D_xV,1)]+nu Delta_xV=0, a genuinely different equation;
* ratio ->infinity: only Delta_xV=0 follows at that scale.

The last equation plus all the inherited affine fits permits V(x,t)=sin t, with fitting constant C0=1. Hence that limit has no applicable affine Liouville theorem. This is an obstruction to the proof, not a counterexample to p-gradient convergence.

The finite-nu equation has strictly convex variational integrand exp((V_t+|D_xV|²/2)/nu). This density is also the actual compact-first-jet limit of the normalized p-energy. A smooth entire solution with globally bounded full gradient is affine, by differentiating this Euler equation and using the uniformly elliptic Harnack inequality. The inherited fits have not been shown to provide that extra gradient bound. The full fitted-class finite-nu rigidity step is unpaid.

When lambda/epsilon ->0, the alternative transverse width sqrt(epsilon)r formally and rigorously at convergent tests gives the full harmonic equation in (x,t). But the old source fit occupies a width sqrt(lambda/epsilon) shrinking to zero in those coordinates. Uniform boundedness and compactness on the wider cylinders remain unpaid.

## Independent variational attempt

Testing with eta²(u-ell), rather than eta^p(u-ell), removes the explicit p cutoff factor and gives the exact weighted estimate

    integral eta² (|Du|^{p-2}+|a|^{p-2}) |Du-a|²
       <=4delta integral eta |Deta| (|Du|^{p-1}+|a|^{p-1}),

where ell=a·x+b and ||u-ell||<=delta. It does not control the flux mass uniformly in p or yield unweighted pointwise control. The linearized flux at a nonzero affine slope has eigenvalue ratio p-1; a concrete two-direction perturbation makes its flux-angle coercivity decay like p^{-1/2}. This is not fixed by nonvanishing of the limiting gradient.

The precise unproved direct target is a bound C(delta+1/p)^theta for ||Du_p-Dv|| on B1/2 under nonvanishing C^{1,alpha_n} control only of v, without quasiconcavity or an assumed p-uniform gradient modulus. A fully general p-independent C^{1,beta} theorem would additionally require all critical-gradient and all scale regimes. None is asserted here.

## Reading and provenance

Read the actual pinned introduction, flatness and reduction contracts; the homogeneous Liouville statement was not silently applied to a viscous limit. Read primary excerpts of Bungert; Sobral–Teixeira–Urbano; Lindgren–Lindqvist; Peng–Zhang–Zhou (including its actual gradient convergence proof); and Li–Zhang's uniformly elliptic Harnack theorem. Exact scopes and limitations are in [reading-and-failures.md](../experiments/i230_p_harmonic_gradient/reading-and-failures.md) and [literature.md](../sources/i230_p_harmonic_gradient/literature.md). Provenance is in [input-authentication.json](../experiments/i230_p_harmonic_gradient/input-authentication.json).

I224 R/S and the supplied prior reviews were treated as supplied context. No I231 or live other-agent output was read. No subordinate agents, research code, tests, numerical experiments, parameter scans, snapshots, seals, shared edits, staging, commits or publication. Retrieval, page extraction, bounded source lookups and provenance hashes only. No claim of worldwide novelty or accepted-count change.
