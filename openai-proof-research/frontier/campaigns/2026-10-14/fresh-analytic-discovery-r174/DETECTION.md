# Detection attempts and exact unpaid comparison

The calculations in CARRIER.md and CHARACTERS.md isolate a concrete number: for a positive ordinary degree map f:N→S^d from a compact connected oriented ENR homology d-manifold, let

    f_*[R_N]⊗Q = μ(f,N) u_d in E_d(S^d)⊗Q.

A faithful Z_p action forces this number to vanish after averaging f. Ordinary degree remains positive under averaging. A contradiction thus requires a detection statement at this exact sheaf-theoretic interface. No such full statement was frozen in this round.

## Detection when there is a manifold chart

If N is a topological manifold, choose a small coordinate ball and collapse its complement to get a degree-one map π:N→S^d. Away from the collapsed value, the pushed orientation form is the ordinary sphere orientation form. A small contractible neighborhood of that value and the source's integral localization isomorphism give π_*[R_N]=u_d integrally. This does not need a triangulation of the entire manifold.

For any f of degree D, f and D_Dπ represent the same rational class in degree d. Apply the finite-polyhedron ENR retract and odd-sphere telescope to their difference/homotopy problem: after a common positive-degree postcomposition their maps are homotopic. Equivalently their maps to K(Q,d) are homotopic and the compact homotopy factors through a finite telescope stage; the finite model transfers this back to N. Proper covariance, the close-pair homotopy calculation, and rational degree action then give μ(f,N)=D. Thus removing a global triangulability hypothesis alone is already paid by the actual source operations and an ordinary local chart.

## Cell-like resolutions and products

Suppose ρ:Z→N is a proper cell-like resolution by a compact oriented topological d-manifold, with orientation normalized to degree one. Proper base change and acyclicity of the fibers identify Rρ_*R_Z with R_N. The trace/duality pairing agrees with the oriented pairing: the trace is normalized by the fundamental class, and the unit and orientation trace give the same local dualizing isomorphism. Consequently f_*[R_N]=(fρ)_*[R_Z], and the manifold calculation gives μ=D. No action is lifted through ρ.

There is a still stronger, simpler payment for this entire resolvable direction. The original product-decomposition proof establishes that the finite-dimensional cell-like image Y of an n-manifold, n≥3, has Y×R² a manifold. Its mechanism is explicit: local homology gives disjoint arcs; an extra line upgrades this to disjoint arc-disk approximation; another line separates disk interiors at distinct heights after separating their 1-skeleta. The cell-like approximation theorem applies to the product resolution. A faithful jointly continuous action of a locally compact second-countable Hausdorff group on connected Y acts trivially in the R² coordinates and remains faithful and jointly continuous on Y×R². The pinned full headline applies. This construction is already paid; no action lift and no orientation assumption are needed for this implication.

Version caution matters. The 1981 original also prints a broader Theorem 3.2 using an announced universal resolution assertion. It is not the result used here. The retained result is its Theorem 3.1 with an actual cell-like resolution; the later author survey states the product theorem with the resolvability hypothesis. The 1996 controlled-surgery discussion and its 2024 erratum were not completely recovered as a corrected proof package. Nothing here uses the obsolete unrestricted resolution assertion.

## Why the carrier retract does not finish detection

The split R_N | Rr_*R_P proves membership in T(S^d) after pushforward. It does not identify a symmetric form with a manifold orientation form. P need not be a d-homology manifold. The maps i,r do not come with a symmetric Poincaré equivalence identifying the pairings, and ordinary homotopy domination does not identify the fiberwise derived sheaves. Treating the retract as an oriented geometric resolution would erase exactly the missing operation.

The primary constructible-Witt comparison supplies L-classes for stratified/PL objects and compares constructible sheaf forms with classical L-theory. The pushed constant sheaf of an arbitrary continuous map from a nontriangulable ENR need not lie in that constructible category. The source's large T category was built precisely to contain more objects. Its 2-primary dense-inclusion estimate on finite test spaces is not a comparison functor from all ENR Poincaré data to the ordinary rational fundamental class.

The primary excisive chain model goes farther: singular chains form the required cosheaf object for compact ENRs, a chain diagonal supplies the symmetric structure, and local Poincaré duality on every open set gives nondegeneracy. The exact proof of its idempotent-completion comparison uses a Tate-cohomology defect. Those are compatible ingredients. What has not been constructed here is an orientation-preserving, proper-pushforward-compatible comparison from that excisive chain signature to the particular form [Rf_*R_N,α_f] in the source T(S^d), with its cutoff/germ quotient and real coefficient conventions. In particular, neither the top ordinary homology component nor a controlled resolution index has been identified with μ(f,N).

The prospective operation must do all of the following at once: carry the local chain duality to Verdier duality with D_{X,d}=[-d]D_X and the source biduality sign; preserve the actual compact-carrier retract and its symmetric summand, not just its K_0 class; commute with f_* and localization away from a contractible target open; and show that the resulting coefficient on u_d is nonzero for every oriented compact ENR homology d-manifold of the intended scope. A statement such as μ=D, or a correctly normalized nonzero local-index multiple of D, would suffice. Neither is proved by the retained calculations. The chain literature's compatibility makes this an open construction attempt here, not an obstruction or impossibility theorem.

Multiplying a compact N by a sphere can make its dimension odd (use S¹ when its dimension is even, S² when odd), retaining an ENR homology manifold and a faithful trivial-factor action. That observation does not repair detection, manufacture a resolution, or prove a reduction from arbitrary noncompact spaces. No theorem for all homology manifolds, arbitrary non-locally-compact groups, separately continuous actions, or general stratified spaces is claimed.
