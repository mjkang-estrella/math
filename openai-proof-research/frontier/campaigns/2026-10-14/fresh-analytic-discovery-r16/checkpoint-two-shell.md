# Two-shell radial cluster mechanism (working proof)

Source family228; bounded-core manuscript fully read through all seven sections. No independent verdict. Intended new operation: realize two distinct temperature corners for one single-species radial potential, before using the source persistence operation simultaneously at two parameter neighborhoods.

Let Delta=10^-3, ell=exp(-t), s=exp(-6t), and take t large enough that 2(1+Delta)s<ell and 2(1+Delta)ell<1. The continuous nonnegative core has height t^2 for r<1 outside [s,(1+Delta)s] union [ell,(1+Delta)ell], zero on the middle thirds of both shells, linear shoulders inside each shell, and the same taper to zero on [1,1+1/t] as the source. It stays bounded by t^2 and supported in [0,2].

A free component (no pair at distance<1 outside these shells) is a clique: a length-two path has endpoint distance<1. Its inner-shell relation is an equivalence relation, since a length-two inner path has endpoint distance below ell. Each equivalence class has at most4 vertices by the source elementary Gram obstruction. Representatives from different inner classes have mutual distances in the outer shell, hence there are at most4 classes. Thus component size<=16. This argument also bounds every clique of the global good-pair graph by16, whether the full configuration is free or not.

Motzkin-Straus gives at most15m^2/32 good pairs on m vertices. In a small cell of diameter<1, bad pairs are at least m^2/32-m/2. Consequently D0=t^2/32, B0=t^2/2 replace source D0=t^2/8,B0=t^2/2. The same attraction row bound M=c_b t(A+1), with A=3/(2p), satisfies D0>=8M for large t. Density coercivity can use c=1/13824 (a conservative lower bound after216 cells per unit volume). All source thermodynamic/local-moment/range proofs depend on these margins and core support/supremum, not on having exactly one shell.

A free component with k inner classes and total M particles has 1<=k<=4 and k<=M<=4k. Integrating its root freely and its other outer representatives in radius O(ell), its remaining particles in radius O(s), gives volume <= V C^(M-1) ell^(3(k-1)) s^(3(M-k)), up to finite labeling factors. Its fugacity exponent is
M h-3(k-1)-18(M-k).
For h<=18 maximize M at M=k; for h>=18 maximize at M=4k. Maximizing k then gives only h,4h-9,4h-54,16h-225. The third is dominated. Hence the rooted-component count and source bad-particle deletion prove the upper bare-pressure limit
q_*(beta,h)=p max(0,h,4h-9,16h-225).
The lower bound realizes single particles, outer tetrahedra, and16-particle tetrahedra of inner tetrahedra. Relative volume exponents are0,9,225. Outer edges retain plateau margins since s/ell tends to0. Components are placed on asymptotically densest1-separated centers exactly as in source initial.tex. Finite combinatorial factors disappear after division by t. Thus convergence is uniform on compact beta,h sets.

With A=3/(2p), the ideal attraction sends each branch with particle multiplier m to
L_m=p[m h-b_m+(3/4) beta m^2], m=0,1,4,16, b=(0,0,9,225).
At lambda1=(1,-3/4), the active branches are0,1,4 and L_16=-45p.
At lambda2=(21/16,-27/16), the active branches are0,4,16 and L_1=-45p/64.
Both triples have noncollinear slopes v_m=((3/4)p m^2,p m). Choose disjoint small closed parameter balls with positive beta and with the fourth branch strictly inactive throughout each. Then the source optimizer-gap and energy-support arguments produce two exact local generating-support identities for sufficiently large fixed t, one around each triple.

Pending writing: full quantifier freeze after primary comparison; simultaneous iteration parameters and all-source proof adaptation explicitly; complete label combinatorics and hierarchy realization; no claimed result until this is written. Two triples predict density centers5p/3 and20p/3. Transition temperatures are only near1 and21/16 after finite-range realization, not exactly those values.
