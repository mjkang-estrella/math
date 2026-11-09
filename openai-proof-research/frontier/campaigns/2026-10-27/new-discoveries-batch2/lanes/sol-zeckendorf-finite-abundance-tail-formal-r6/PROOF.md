# Finite dyadic proof and provenance

Let J=N/6, p=blockLower n and Y_j(w)=card(successSlots j w). Sum over the actual finite completeDomain with actual weights P N. For each prefix u of length 3j, every cylinder word has the same Y_j=y. A successful next block is exactly the subcylinder u++[C1,C1,C2]. Thus the next weighted sum on this cylinder is exactly

  2^(-y) * (cylinderMass N u - cylinderMass N (u++[C1,C1,C2])/2).

actual_early_success_lower gives subcylinderMass/parentMass≥p for j<J. actual_prefix_positive makes multiplication by parentMass legitimate. Hence this expression is at most the preceding cylinder moment times (1-p/2). Every complete word has ≥3J moves. The finite sum_fiberwise_of_maps_to identity, instantiated with take(3j) on actual completeDomain, regroups the complete sum without omission or duplication. Induct from moment0=P_normalized=1 to momentJ≤(1-p/2)^J. blockLower_bounds proves nonnegativity of the induction factor.

If Y_J<t, 1≤2^t*2^(-Y_J); multiply by P≥0 and sum. Extending from the bad-success filter to completeDomain only increases the nonnegative sum. The inherited actual_bad_marks_le_bad_success applies the global compression counting injection to transfer the bound to badMarksMass. Threshold zero is an empty event; input zero has only the empty word; zero probability summands vanish. No adaptive trials are assumed independent.

This is exactly root's rational dyadic-moment route, retained in frozen/root-route-STATUS.md and frozen/root-STATUS.md; r5's ordinary argument is retained verbatim in frozen/PROOF.md. Actual primary arXiv:2210.11038v1 Lemma 4.4 proof p19 supplies the triple mechanism; its independence sentence is not used. The certified endpoints concern the actual inherited simple-compression marks, without a new identification with the source's richer all-k partition. No asymptotic, uniform-law or mixing endpoint is asserted.
