# Annular height sectors: preselection calculation and exact gap

No target was frozen. This note does not nominate the finite calculation below, or a real-height, bounded-sector or conditional Gaussian variant. The older full integer annular-sector question remains unproved. The real-polytope comparison was explored because the source has a stronger differential shift operation there; it is not a replacement for the integer question.

## What the source actually supplies

Source232's October6 weighted integer manuscript, `09-annulus.tex`, builds its annular spin law by an ambient extension, authorized winding cuts, a one-white-region global flip and boundary slides. The cylinder has prescribed mixed boundary colors. These operations do not compare partition functions of all different integer values on an entire inner boundary. This is the same distinction explicitly identified in actual analyticr111 `pre-freeze-screen.md`, read before the present calculations.

The October6 real companion is stronger than a GFF statement alone. In `shift.tex` the displacement is averaged over near-saturated components; components meeting grounded sites receive displacement zero. The resulting field is feasible, its derivative has an edge-rank decomposition, and the estimates control its operator and Hilbert–Schmidt norms. Tangency to the fixed-boundary polytope gives the exact identities E div u=0 and E(div u)^2=E tr(Du)^2. A good-component cutoff, injectivity and a determinant expansion give a quantitative event-shift operation.

In `cell.tex`, `b:bulk`, `b:cell`, `b:response` and `b:gff` identify the stationary bulk driver, the linear flux j(q)=Aq, response with identical boundary data, and the Gaussian bulk field. The flux tests are compactly supported inside the domain. With v=2/sqrt(3), the source's normalization is sigma^2=(vA)^(-1). No assertion about the derivative of a partition function under a moving boundary is part of those read interfaces.

The strongest local-contact statement also matters. `foundations.tex`, `f:conditioned-sparse`, allows prescribed fixed pins in [-1/2,1/2], with the specified sign intervals. `f:reveal-obligation` explicitly distinguishes these fixed pins from revealed string values in [-1,1]. The one-sample bounded-data comparison `f:bounded` is stronger for averages but is not itself this near-contact estimate. Initial feasibility had treated “bounded boundary values” too broadly; this was corrected on the later foundations read, before any freeze.

## A finite calculation which identifies the missing term

Let G be a finite connected graph with nonempty disjoint vertex sets O and I. Set all heights on O to zero, and all heights on I to a common real number c. Other vertex heights x are free, of number m>=1. Impose |h_u-h_v|<=1 on every edge. Write

    P_c = {x: all these inequalities hold},  Z(c)=Vol_m(P_c).

Let d be the graph distance between O and I. The complete polytope P={(c,x):x in P_c} is bounded, by connection to O. If |c|<d, the prescribed values have Lipschitz constant |c|/d<1 on O union I. A finite metric Lipschitz extension supplies strictly slack inequalities involving free coordinates, so P_c has nonempty interior. Its volume is positive. Reflection gives Z(c)=Z(-c). Convex slicing and the usual integral log-concavity inequality give log-concavity of Z on its support. These facts do not determine Z.

Represent a fiber, without duplicate facet inequalities, as

    P_c={x:a_j dot x+b_j c<=1}.

For almost every c in the interior of its support, the ordinary moving-facet formula gives

    Z'(c) = - sum_j b_j/|a_j| * Area_(m-1)(F_j(c)).                 (1)

Terms with a_j=0 only delimit the c support and do not enter an interior fiber derivative. Formula (1) follows by differentiating on intervals with fixed face combinatorics: the j-th face moves normally at speed -b_j/|a_j|; edges and intersections of faces affect only second-order volume. There are finitely many exceptional parameter values, since the vertices of this polytope are given by finitely many affine systems. The one-dimensional case uses counting measure on endpoints.

For an inner-boundary edge, the upper constraint x_v-c<=1 contributes positive area, and the lower constraint c-x_v<=1 contributes negative area. If v has several inner-boundary neighbors, those constraints coincide: they must be grouped, not counted once per edge. Outer and internal edges have b_j=0. Thus the missing derivative is a signed boundary-contact flux, not the already identified bulk flux against a compact test.

One may express the same issue by a transport identity, without claiming such a transport has been constructed. Suppose a sufficiently regular vector field V=(1,U(c,x)) exists on a parameter slab and is tangent to its side facets. For a smooth F compactly supported in that slab the divergence theorem gives

    integral [F'(c)+F(c) div_x U(c,x)] dc dx = 0.

Disintegration and integration by parts then give

    E_c[div_x U]=Z'(c)/Z(c).                                    (2)

The right sign in (2) is positive. The source's E div u=0 is the fixed-fiber version with no c component. Reusing that zero after moving the inner boundary would delete exactly the term one needs to identify.

## Strong compatible reductions tried

For comparison, a quadratic graph field with density exp[-kappa/2 sum_edges(h_u-h_v)^2] has an exact answer. Let u be the discrete harmonic function with boundary zero on O and one on I, and put Cap_G=sum_edges(u_u-u_v)^2. Decompose h=xi+c u with xi zero on both boundaries. Discrete integration by parts kills the cross term, and translation has Jacobian one. Therefore

    Z_quad(c)/Z_quad(0)=exp[-kappa Cap_G c^2/2].                  (3)

This is an ordinary Gaussian decomposition, not a new deduction about hard heights. In the source scaling the corresponding coefficient would be kappa=vA=sigma^(-2). Establishing (3)'s limiting analogue for the hard model requires, for example, the boundary score in (2) to converge to -kappa Cap(D)c with enough integrated control, together with tails that justify normalization over all c. None was established here. The integer question requires its own exact sector ratios and summability, not a formal replacement of sums by integrals.

I tried the source's actual component displacement rather than rejecting all shifts on topology grounds. Keeping boundary sites separate, components touching only I can be assigned displacement one, those touching O zero, and ungrounded components a smooth interpolation. On a good event with no component bridging the boundary sets this suggests a cross-fiber map. This is a feasibility construction only: its near-boundary derivative and uniform conditional component estimates were not proved. The observation that a shared moving coordinate has many incident edges is not by itself an obstruction: small jumps and disjoint component supports could compensate for their number. Conversely, these possible compensations do not supply the boundary score or all-sector tails.

Subtracting c times a deterministic harmonic profile makes the pin values zero, but changes every edge constraint to an asymmetrically shifted interval. The source's “small linear tilts” concern density weights exp(Y), not a shift of all hard-constraint faces. Its fixed-polytope response is therefore not a direct theorem for this subtraction. No uniform comparison of the shifted hard constraints that recovers the exact order-one free energy was proved.

Two primary proof interfaces were checked. Miller, arXiv:1002.0381v2, Theorem1.2 and its final proof, uses harmonic coupling for uniformly strictly convex smooth potentials, with constants depending on curvature bounds. The hard constraint has a flat interior and infinite wall; a smoothing limit with uniform curvature hypotheses is not supplied. Miłos–Peled, arXiv:1404.5895v3, Sections2.1–2.2, Lemma2.10 and Lemma2.11, gives the stronger invertible addition algorithm, exact piecewise-triangular Jacobian change of variables and paired Jacobian lower bound. Its zero displacement on the prescribed pin set and event/Jacobian estimates do not calculate the desired moving-boundary normalization. We did not read their entire delocalization proof, and do not claim these are all possible reductions.

Finally, knowing every conditional field law given c cannot on its own identify the c law. Multiplying the joint density by an arbitrary positive weight w(c) leaves all normalized fiber laws unchanged and changes the sector weights. This is an information diagnostic, not a counterexample to the specified uniform hard model. Its normalization is fixed by that model, and remains to be calculated.

## Exact unresolved operation

The full missing operation is a simultaneous normalized-sector comparison for the actual hard model, with the correct capacity coefficient and summable tails over the entire allowed sector range, compatible with the conditional field limit. Neither fixed-boundary GFF convergence, the finite facet formula, local cross-fiber feasibility nor the Gaussian benchmark closes it. No local, real-valued, finite-sector, subsequence or conditional substitute is proposed. No full-target impossibility or contribution verdict is asserted.
