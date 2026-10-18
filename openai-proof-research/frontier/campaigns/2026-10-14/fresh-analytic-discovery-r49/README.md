# T216A: critical XY magnetic amplitude

Myeongjin Kang. No affiliation. Original exposition CC BY 4.0; original code MIT. Author proposal for independent proof and contribution review. No acceptance or count is claimed.

For the nearest-neighbor cosine XY model on Z² at the pinned source's critical inverse temperature, write the interaction as

    b_c sum_{unordered nearest-neighbor edges} cos(theta_x-theta_y)
        + h sum_x cos(theta_x).

The field h is dimensionless and is not multiplied by b_c. Let p(h) be the thermodynamic logarithmic partition function per vertex and m(h)=p'(h) for h>0. The author proof establishes positive finite constants C_p and C_m=(16/15)C_p such that, along the full real limit h↓0,

    p(h)-p(0) ~ C_p h^(16/15)(log(1/h))^(1/15),
    m(h) ~ C_m h^(1/15)(log(1/h))^(1/15).

The unchanged exact target and its post-exploration freeze time are in [original-scope.txt](original-scope.txt). This continues the explicitly unresolved amplitude interface of analytic r48. It is not a relabeling of r48's technical two-sided comparison result. No magnetic correlation-length assertion is included.

Read the complete proof in this order:

1. [lattice-interface.md](lattice-interface.md): the finite multi-arc extension of the pinned source, the whole-plane neutral spin-field block limit, the boundary-inclusive pinned block limit, and the exact pressure-increment sandwich.
2. [continuum-boundary-pressure.md](continuum-boundary-pressure.md): the ultraviolet-normalized Dirichlet/neutral whole-plane pressure coefficient equality. This is an exact copy of the parent author's proof, with [parent-provenance.json](parent-provenance.json). It is author collaboration, not independent review.
3. [amplitude-assembly.md](amplitude-assembly.md): the full real field inversion, ordered limit sandwich, and convex secant argument for magnetization.

To identify the constant, set D=(-1,1)², K=2/pi, let a_n be the source's pinned center magnetization and write a_n~A_XY n^(-1/8)(log n)^(1/16). If R_D is the regular part of the Green kernel with singularity (2pi)^(-1)log(1/|z-w|), put kappa=exp(R_D(0,0)/(2K)). Let mu_* be ultraviolet-only whole-plane imaginary chaos with log-one covariance singularity, beta=1/2, and independent uniform phase. Then

    c_* = lim_{t→infinity} [log E exp(t Re mu_*(D))]/[4t^(16/15)]
         is in (0,infinity),
    C_p = c_* (A_XY kappa)^(16/15) (8/15)^(1/15).

The continuum coefficient exists by the corrected ABJJ tail theorem and an elementary Laplace principle. The proof does not rely on the erroneous exponent/tail inference in the older LSZW appendix, full-variance covariance monotonicity in an ultraviolet-only convention, or a simultaneous lattice/growing-tilt limit.

[source-map.md](source-map.md) records the exact stipulated source interfaces. [contribution.md](contribution.md) credits the classical and source operations and identifies the proposed additional mechanism. [reading-limits.md](reading-limits.md) records actual reads and the unresolved Gielerak1986 closest-antecedent retrieval limitation. A successful proof review alone cannot resolve that contribution question. [formal-plan.md](formal-plan.md) scopes feasible formal verification without representing imported analytic facts as proved.

The arithmetic diagnostic is nonproof and has deliberate failing controls. The integrity verifier requires an external SHA256 anchor, authenticates exact file and directory membership, and rejects links, nonregular entries and hardlinked files. Private source/primary bodies are excluded from Git and release. Parent author assistance and preceding technical results are not independent gates.
