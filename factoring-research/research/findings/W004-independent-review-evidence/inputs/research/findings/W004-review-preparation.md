# W004 — review preparation while construction remains live

2026-10-08. **Provisional reading notes, not an intake or acceptance.**
Verified new complete factoring complexity improvement: **NONE**.

The coordinator read the current 340-line construction draft, SHA-256
`f1aeab95c86e26c000ae45fc2ef762c4a377d3278e30c2d5f029f784d7e4d5c1`.
The task was independently confirmed running/working afterward. This is not
its final submission identity: it is incorporating the accepted W003 norm-gate
update. Do not freeze or review this version as though delivery were complete.
The linked test proposal and source-notes file were not yet present when
checked; no conclusions about them or source verification are recorded here.
The constructor retains ownership of all W004-biquadratic-* artifacts.

The draft's apparent contribution is an explicit reciprocal packet and its
remaining witness problem. Its assertions below are **review obligations**,
not coordinator-accepted theorems. The finished report, including the new
norm-gate packet, must be read in full and checked against these notes.

## Claims to check independently

1. **Paid selector and exceptional branches.** Check the eligible-prime count,
   exact range of the cited nth-prime bound, finite lexicographic pair search,
   CRT costs and fixed choice rules. Distinguish character counts of arguments
   from counts of polynomial values. Verify the height, nonsquare discriminant
   and distinct-quadratic-field proofs, including every early factor/root return.
   Keep the actual Norm2 construction cost, including its full lists, visible.

2. **Biquadratic structure and class tests.** Establish the degree-four field
   only after excluding rational squares s_i±2t, with Delta_i nonsquare.
   Distinct K_i alone does not imply disjoint L_i. Check the rational-norm
   compression identity and both signs when its trace expression vanishes;
   then prove the four rational square tests really decide the promised
   ordinary/twisted classes. Verify the cross-field cheap-root tests with
   reduced, unit denominators. Norm(alpha_i)=t^2 is essential to the claim
   that these two target classes have the same absolute-norm class.

3. **Reciprocal packet identity and extraction.** For coprime p,q>0, the draft
   uses rows (p,q),(tq,p) and asserts

       Q(alpha_i)=alpha_i*Lambda_i,
       Lambda_i=s_i*p^2*q^2-p^4-t^2*q^4.

   Check both coordinates of the identity, nonvanishing, the bit widths and
   all eight target choices. In one orientation the claimed criterion is
   Lambda_1=epsilon_1*h^2 with epsilon_1 in {1,Delta_1}, and
   Lambda_2=epsilon_2*k^2 with epsilon_2 in {s_2+2t,s_2-2t}.
   Validate actual field roots as well as class membership. Check the proof
   that reduced rational denominators divide units and the ordered row gcd
   rules before inversion. Coprimality of p,q and t being a unit must justify
   every assertion that a full row gcd cannot lead to an unhandled case.

4. **Witness geometry without an oracle.** Audit the claimed eight smooth
   projective genus-five curves, independence of their two quadratic covers,
   simple/disjoint branch loci, behavior at infinity and Riemann–Hurwitz count.
   Check the genus-one quotient and every restriction required to lift a
   rational quotient point: finite chart, nonzero rational-square coordinate,
   nonzero roots and unit packet image. No rank, rational point, generators,
   useful height bound or efficient point-search routine is supplied merely
   by writing down these curves.

5. **The weaker conic's exact scope.** Subtracting the two equations gives
   epsilon_1*h^2-epsilon_2*k^2=(s_1-s_2)*(pq)^2. Audit the claimed reduction
   to a root of R for witnesses with valid unit reductions. Distinguish this
   reduction from witness existence, an efficient solver, a general hardness
   lower bound, and the arbitrary conic problem. Nonunit and denominator
   cases must remain explicit; a trivial homogeneous point supplies no unit
   slope. A Norm2 output is not automatically the required conic witness.

6. **Complete finite program and failure-inclusive cost.** Check the fixed
   order of all preliminary tests, the M^2 scan, actual rational arithmetic
   widths, memory model and validation. For M=n^2 the claimed post-Norm2
   polynomial work says nothing about useful success mass. Audit the exact
   raw-word outer probability, including nonunits, zero, out-of-range words,
   repeated prime powers and independence from the hidden root conditional
   on R. Check the iid restart identity and the complete factor-tree bound.
   The reported O(N_0^(3/2) poly(log N_0)) reference envelope uses the old gcd
   branch and expensive Norm2 lists; it is neither an improvement nor a
   lower bound for alternative realizations.

7. **Accepted update versus genuinely new claims.** The final report must
   incorporate the accepted rows (t,u),(v,1) from the
   [norm-gate disposition](W003-normgate-disposition.md). They explicitly solve
   one field's twisted target. This packet differs from the reciprocal
   packet above; checking one does not check the other's proposed second-field
   criterion. Preserve the original brief and the in-flight update separately,
   and audit all added second-field selection, square tests and cost claims.

8. **Sources and any proposed experiment.** Verify cited primary passages at
   their actual scope, without importing general NFS smoothness or a cheap
   descent witness. Read the eventual test proposal before selecting it;
   require an exact falsifiable claim, fixed corpus/selector/cap, charged
   failures and a predeclared budget. No test has been authorized for execution
   by this provisional reading, and none has been run.

## Addendum: rotation-family draft

While the task remained running, the main draft grew to 385 lines. The
coordinator read its lines 115–345, including the new anchored rotation and
second-field equations. This additional reading is still provisional and
does not replace full final intake. Extend obligation 7 as follows:

- Check the exact cleared rotation A^2+B^2=s_j D^2, D=k^2+m^2, and the
  common integer rows (tD,A),(B,D). Distinguish an exhaustive rational
  parameterization up to the packet's sign symmetries from the chosen finite
  nonnegative parameter rectangle. Include the infinite parameter explicitly.
- Audit both coordinates of Q(alpha_i)=C_0+C_1 alpha_i and the factorized
  norm t^2*(C-e A^2 D^2)*(C-e B^2 D^2), with e=s_i-s_j and
  C=t^2 D^4-A^2 B^2. Check every zero/nonunit branch before reduction.
- When a norm-square test succeeds, the additional S or S/Delta_i square
  test is essential. Verify the actual field root, then its integral
  derivative-cleared representation. Do not reduce the displayed quotient
  by inverting h term by term; h can have a nonunit modular image.
- Check the pointed genus-one norm curve W^2=f_i(X)*f_i(s_j-X), its stated
  point (s_j/2,f_i(s_j/2)), and every remaining lift. In particular the point
  must satisfy X=u^2 and s_j-X=v^2, and the resulting packet must still be
  an actual square in the other field. The draft's genus-seven and
  genus-thirteen counts need separate branch, independence, pole and
  nonsingularity arguments; neither follows from the genus-one quotient.
- Audit the exact two coefficient equations for the other field's root,
  the claimed nonzero error of the simple conic points, and the restricted
  observation that a product of only the two unrotated packets cannot add
  a first useful target. None is a lower bound for broader row families.

## Delivery gate

On the terminal notification, consume task_status, read every final report
line and supporting source/test note, verify the input and delivery identities,
and preserve the submitted bytes. Only then launch a **new** T3 review task
with the frozen W004 brief, final report, accepted W003 dispositions, exact
in-flight update, these obligations and any remaining objections. These notes
do not replace that independent review. No mathematical execution, code or
Lean work was done in this preparation.
