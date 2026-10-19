# Frozen target T271D110

Research target only; not a theorem assertion, review verdict or nomination.

For every S in {1/2,1,3/2,...} and every Borel probability law nu on [1,infinity) such that integral a^q nu(da)<infinity for every real q>0, put independent identically distributed conductances a_e with law nu on all UNORIENTED nearest-neighbor edges e of Z^3. Write P for their product law. No finite upper bound on the support of nu is assumed. The law and S stay fixed in all limits.

On Lambda_N=[-N,N]^3 intersect Z^3, use free boundary and

H_(N,a) = - sum_{e={x,y} subset Lambda_N, |x-y|_1=1} a_e S_x dot S_y,
M_N = sum_{x in Lambda_N} S_x^z,
p_(N,a,beta)(h) = (beta |Lambda_N|)^(-1) log Tr exp[-beta(H_(N,a)-h M_N)].

The sought statement is: there is a deterministic finite convex S-Lipschitz pressure p_beta(h) such that, P-almost surely, p_(N,a,beta)(h) converges to p_beta(h) for every beta>0 and h in R; writing m_(S,nu)(beta)=partial_h^+ p_beta(0),

lim_{beta -> infinity} beta^(3/2) [S-m_(S,nu)(beta)]
   = zeta(3/2) / [(4 pi)^(3/2) sqrt(det D_(S,nu))].

Here D_(S,nu) is defined by the quenched diffusive limit of the variable-speed continuous-time random walk with generator

(L_(S,a) f)(x) = S sum_{y:|y-x|_1=1} a_{ {x,y} } [f(y)-f(x)].

Under diffusive scaling its limiting Brownian motion has covariance 2 D_(S,nu) per unit time. The matrix is deterministic and positive definite. It is the homogenized matrix, NOT the arithmetic mean of the bond weights. The statement includes the constant-law case, where D=S a I.

The order is N -> infinity at each fixed beta,h, then h down to zero through positive values, and then beta -> infinity. The result concerns the quenched pressure (logarithm before disorder averaging), the original quantum spin system at every fixed positive spin, and the entire ordinary beta limit. No uniform rate in nu is claimed. Any constants or thresholds in an author proof may depend on S and the full fixed law nu; no finite moment index alone is asserted sufficient. No small disorder, periodicity, bounded upper support, finite volume, annealed partition function, large-S or subsequence replacement is permitted.

Dependency contract: all pinned OpenAI statements AND proof operations used under their exact hypotheses at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. Every extension to the above random unbounded rates remains to be proved independently. The target is not claimed to follow merely from heat-kernel homogenization.
