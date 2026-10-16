# Original scope — discovery r7

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.

Initial status: DISCOVERY / UNRESOLVED; campaign remains 4/10.
Find and attempt one substantial analytic/probabilistic/geometric-analytic/dynamical consequence of openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, accepted true. No scope narrowing earns completion. No nested agents or writes outside this directory. All earlier vetoes in the assignment apply; in particular no maximal continuity, Hamiltonian span, crossing-number, kinetic, matrix-disk, or poly-Zp reuse.

First serious lane: stationary random-walk scaling for spherical critical FK planar maps at every fixed q>4, jointly with their Brownian CRT metric-measure limit. Exact model/clock/limit quantifiers will be fixed after reading the original source, BEFORE the proof attempt. Source discovery is not a theorem claim.

Any full result requires separate independent proof and contribution review; no count change, manuscript, Lean, upload, or submission here.

## Fixed full target F (before proof attempt)

For EVERY fixed q>4 and EVERY alpha in (0,1/2), sample the rooted n-edge spherical FK map with weight proportional to q^{k_M(A)+(|A|-|V(M)|)/2}, retaining all loops/multiple edges. Independently give EVERY edge resistance R with P(R>r)=r^{-alpha}, r>=1. Put m(v)=deg_M(v), INCLUDING loop darts. On real functions use E(f)=sum_{nonloop edges e=uv} R_e^{-1}(f(u)-f(v))^2, counting multiplicity, and tau_n=sup Var_m(f)/E(f), where Var_m(f)=sum_v m(v)(f(v)-sum m f/(2n))^2. On a one-vertex map define tau_n=0. This is the inverse first nonzero eigenvalue of the continuous-time generator Lf(v)=m(v)^{-1} sum_{e=vw, w!=v} R_e^{-1}(f(w)-f(v)); base degree, not conductance degree, is the speed measure.

Let xi be the EXACT critical finite-variance block offspring law (block:offspring) in the pinned source; write p_2=P(xi=2)>0, and T for its UNCONDITIONED Galton-Watson tree. Set K(q,alpha)=p_2 E|T|^alpha. The desired assertion, through ALL integer n, is

    P(n^{-1/alpha} tau_n <= x) -> exp(-K(q,alpha) x^{-alpha}) for EVERY x>0. (F)

No bounded block-size, offspring third moment, tree-only, bridge-only disorder, subsequence, changed speed-measure, alpha cutoff below 1/2, or conditional localization hypothesis may be inserted. All conductances remain independent on ALL edges. The original task's output standards apply. This target is distinct from the metric CRT theorem.

The ordinary-conductance walk limit was screened out BEFORE nomination as a likely technical assembly through source tree:paths. It is not a replacement theorem. F is now the fixed target; partial lemmas do not replace it.
