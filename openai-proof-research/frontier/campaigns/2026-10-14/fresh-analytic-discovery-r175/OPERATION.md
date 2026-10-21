# The operative comparison, carried to its remaining interfaces

These are prefreeze derivations. No result is nominated and no upstream proof is being audited. In particular, the source's full purely cosmetic surgery statement is accepted, not rediscovered.

## 1. Primary maps: a late read removes a false gap

The 2022 ribbon paper, in its actual v5 proof, expresses the double D(W)=Wbar∘W as surgery on h disjoint circles in

    X=(Y_-×I)#h(S^1×S^3).

The circles have homology classes [gamma_j]=tau_j+sum_i C_ij alpha_i, where tau_j lies in H_1(Y_-), and det C=±1 in the present case. Over Q the tau_j disappear, so their top exterior product equals ±alpha_1∧...∧alpha_h. The published proof then uses a loop-surgery formula for the relevant Floer theory. It is this operation, not a bare comparison of dimensions, that can supply a left inverse to the ribbon map.

Daemi–Miller Eismeier's actual March 2026 v2, §6.1 and §7.1, strengthens the available map interface. Irreducible chains are the image of the fundamental three-cycle u of SO(3) acting on the equivariant chain complex, shifted by three. Equivariant chain maps and homotopies restrict to that image. Corollary 7.2 therefore gives irreducible cobordism maps for pseudo-unobstructed cobordisms, functorially. This was read after the first topological/algebraic notes and is a real correction to the provisional map-existence concern, not an omitted assumption silently supplied later.

For our W, both boundary bundles are trivial, H^2(W;Z)=Z/2, and a splitting has classes x+y=0. Thus x=y, since this group has exponent two. The reducible flat connections are central. More generally the normal-index formula for a central-ended Abelian stratum has

    N=-2(x-y)^2+2(b_1-b^+)-2.

With b_1=b^+=0 and torsion x-y, N=-2, exactly the pseudocentral case allowed by that theory. In the actual W situation no noncentral free orbit is forced by the torsion data; the two central characters remain distinct. In either formulation the pseudo-unobstructed hypothesis is available. The same holds for Wbar and D(W). Therefore the conclusion is not “ordinary instanton maps on order-two homology spheres do not exist.” They do, by this primary mechanism.

For a central connection corresponding to x on an end, the restriction map H^2(W;Z)→H^2(Y_±;Z) is an isomorphism. The set of cohomology pairs in DME Proposition 6.6 has one element for matching central labels and none for mismatching labels. Thus the central part of the map is a signed permutation of these labels, without a factor two from arbitrarily merging them. This checks the central matching data; it says nothing by itself about invertibility of the irreducible part.

## 2. The loop-surgery route reaches an explicit identity

The identity one wants, with all fixed determinant transitions retained, is

    I_irr(D(W)) = ± I_irr(Y_-×I;1).

More precisely it would follow from the h-fold formula

    I_irr(X; mu(gamma_1)...mu(gamma_h))
       = ± I_irr(D(W);1),                         (L)

and the same formula for the standard cores alpha_i. Multilinearity over Q then gives the double identity, because det C=±1 and H_1(Y_-;Q)=0. This is stronger than importing a framed theorem and hoping that it descends to the desired complex.

The actual original surgery proof is available in Donaldson's book, printed pp.201–206, with its relative usage at pp.209–210. It cuts at S^1×S^2, perturbs the interval of Abelian characters to two central endpoints Gamma_0 and Gamma_1, and compares S^1×D^3 with D^2×S^2. The latter retains Gamma_0 only. The relevant cylinder transition has an S^2 of gluing directions and a translation parameter. The holonomy representative for the degree-three loop class has degree one on S^2×R; this is what identifies the surgery count with the loop insertion. The relative discussion retains the outer irreducible limits. Thus the needed local cap degree is already present in the primary proof; it is not a new winding construction.

There is also a usable dimension calculation for the extra two-central-end case. The successive circle surgeries may be ordered after unimodular changes of the relative handle basis. Their remaining free first homology has rank k=h-s after s surgeries, with torsion Z/2 and b^+=0. At a reducible the formal fixed-limit ASD index is 3k-3 at charge zero, and positive charge adds eight per unit. Both external central limits have h^0=3 and h^1=0. A break through such a reducible with irreducible external ends requires two nonconstant external trajectories. With the fixed-limit convention, their index lower bound is

    (3k-3)+3+3+1+1 = 3k+5.

This is the same exclusion window used in the primary ribbon Lemma 6.4, now with two possible central labels instead of one. The finite number of labels does not lower the index. At k=0 an actual central field has index -3, and the corresponding lower bound is five. For k≥1 the free Abelian character family has to be included; it cannot be replaced by two isolated connections merely because the outer ends have only two reducers.

The loop insertions have total degree 3k at that stage. For representatives supported on disjoint curves, a particle hitting a loop permits release of degree three but its position is constrained to that curve, of dimension one. Its net index loss is at least 8-3-1=4. A one-parameter sweep of those curves has position dimension at most two, still leaving loss at least three. Particles outside the entire sampling graph release no loop cut. These are the appropriate incidence calculations; the crude bound “arbitrary four-dimensional particle position plus arbitrary released insertion degree” would throw away useful support information.

These computations make a rational extension of the ordinary ribbon double identity plausible and close the finite-dimensional and central-label parts of the reduction. They are not a complete proof of (L) in the source's exact-support category. The common family must identify the geometric loop representatives with the primary mu classes, preserve the actual determinant-one lift on every S^1×S^2 cut, and identify the two endpoint maps and homotopies on the same chain models. In particular the choice of a lift/trivialization for the basepoint fibration in the book's holonomy argument cannot simply be assumed globally in an arbitrary new family. A rational representative or finite-multiplicity construction may address it, but that construction and its normalization have not been supplied here. Neither the primary existence theorem nor the index inequality alone proves this relative count identity.

The alternative character-variety proof in ribbon v5 §6.7 was read through its final paragraph. It proves triangularity for regular flat extension problems via a degree-±1 word map. Its discussion explicitly leaves a simultaneous time-independent perturbation/regularity issue unchecked. It is not legitimate to treat that discussion as a ready-made proof of a strictly triangular map in every perturbed problem. The completed surgery proof, rather than this conditional alternative, is the strongest reduction used above.

## 3. Transferring the closed source stack requires more than (L)

Suppose (L) and its fixed-determinant comparison are available. Then ALGEBRA.md supplies rational invertibility of F and Fbar, labelled cap nonvanishing once the labelled maps exist, and a finite odd-prime repetition preserving a nonzero ordinary pairing. CARRIER.md supplies the actual negative lattices, global characteristic lifts, unchanged positive sphere plumbings and increasing Dirac index. These are not the missing operations.

The source's abelian restrictions are local to the genuine J and -4 lens cuts. Those cuts and the sphere sweeps remain inside the original intervals; inserting W creates no new parameter boundary. Positive U neighborhoods lie in unchanged B H B macros. On compact W interiors, its H^2 has no free part, so no additional rational variable enters the square bounds. The source's finite-sample stabilizer detection can sample holonomies and spinors there: it is a finite-dimensional stabilizer statement, not a simple-connectivity assumption. Therefore a claim that W creates an unavoidable failure of local sampling would also be unsupported.

Nevertheless, a full transfer still needs a construction of ONE compatible library on the entire enlarged collection of compactified families. It must simultaneously give:

* the ribbon-double comparison and its loop-cut homotopies;
* the labelled returns T_L with the exact cap surface/point tests;
* the ordinary B H B and W product formula, including possible central breaks at every newly inserted long finite collar;
* the projected mixed-field equations on every genuine J face, with discarded R fields, their particles and all cutoff dependence actually absent from retained equations;
* the original local lens flip and its orientation comparison, with the cap parameter retained as the shared parameter; and
* the same protected zero-spinor link while the later mixed perturbations are installed.

The local lens normal operator, flux functional and asymmetric weight construction are not changed by replacing distant compact pieces. The remaining work is to prove the above common relative extension, not to invent a new lens gluing theorem. In particular choosing a generic perturbation for W separately, then independently invoking the source regularization theorem for its original product-identification stack, does not produce this common family. Its source theorem has that original stack as its domain. An extension to the proposed cobordism stack needs the stated argument and cannot be obtained solely by equal chi, sigma and lattice data.

No complete construction of this common library, its orientation-preserving comparison to the primary maps and its compactified boundary identity is present in this packet. This is the precise unpaid operation retained here. It is not a claim that such a construction fails, and not a claim that it would be a substantial new contribution once completed.

## 4. What the final boundary would say if that operation were closed

The source's zero-spinor count would be Omega≠0, n_D>0 and eta=n_D-1. The normal phase quotient is CP^eta. The actual character of the phase line is two, so the phase cuts have Euler pairing

    <(2h)^eta,[CP^eta]> = 2^eta.

This coefficient was also read in the original PU(2) link proof, including its obstruction-bundle version. With complex cokernel dimension c the calculation becomes

    <(2h)^(n_D-1) h^c,[CP^(n_D+c-1)]>=2^(n_D-1).

A nonzero ordinary count therefore gives a nonzero link count; arbitrary ordinary mapping degree has not been substituted for a character coefficient. In the source compactification the only other zero-dimensional ends are paired minimal trace-zero lens caps, canceled by the fixed local determinant flip and its full real orientation sign. Its complex Dirac factor contributes no additional sign. The resulting equality would be 0=±2^eta Omega.

This is the exact endpoint of the integrated ribbon-substitution reduction. The source proves this equality for a cosmetic identification. The present packet does not prove its extension to every W above. No conditional version is offered as a theorem, and no exact theorem is frozen.
