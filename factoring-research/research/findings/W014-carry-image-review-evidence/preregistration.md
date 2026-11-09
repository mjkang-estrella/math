# W014 B: fixed exact algebra certificate, registered before execution

This is an exact branch certificate, not a performance experiment, parameter
search, prime sweep, degree sweep, or N-only factoring implementation. The
symbolic proof remains the authority for quantified conclusions. Inputs below
are fixed now; there will be no replacement instances or adaptive extension.

Use Python's standard library only, integer arithmetic throughout. One script
execution, a 10-second timeout, and no more than 10,000 recorded checks. Each
case retains all its checks and computed values; a failed check is recorded and
does not suppress other cases. Unexpected exceptions and unstarted cases must
remain visible. No timing comparisons or inferred success probabilities.

1. **Normalization.** M=12, P(h)=-13+18h^2, degree cap 2, offsets
   {-3,-1,0,1,2,3}; expected g=6, M'=2, r0=5, Q(h)=-3+3h^2.
   Check floors, Euclidean remainders and the full-image bijection using the
   12 original input residues and the 2 normalized residues. Also check the
   degenerate P=-13 with all nonconstant coefficients zero: g=12, M'=1,
   Q=-2, r0=11. No additional normalization instances.
2. **Small prime, nonunit derivative.** Q(h)=h^4+h^2, ell=2, d=4.
   Check R(x)=4x^3+2x at x=0,1,2,3 and s_max=3. Use the fixed x0=1,
   s=1, u=3 and V(t)=7t^2+16t^3+16t^4. Check the Taylor coefficient
   identity and the eight t residues modulo 8 for bijectivity of u*t+2V(t).
   Check the resulting coset 2+8*(Z/64Z) is in Q(Z/64Z).
3. **Small prime, constant polynomial function.** Q(h)=h^3-h, ell=3,
   d=3, x0=0, s=0. Check its formal primitive reduction has constant value
   zero modulo 3, its derivative at zero is -1, and the image modulo 27
   is exactly the nine multiples of 3.
4. **Large-prime lifting.** Q(h)=h^2, ell=7, d=2, k=2. Enumerate only
   the seven residues modulo 7 and 49 residues modulo 49. Check regular
   images {1,2,4}, all seven lifts of each, the image size 22 and both
   displayed large-prime lower bounds.
5. **CRT.** Q(h)=h^2, M=72=8*9, d=2. Check its full image is the
   Cartesian product under CRT of its images modulo 8 and 9, of sizes
   3 and 4, hence has size 12. Check C_2=24 and the stated global bound.
6. **Signed carry consumer and full collision.** N=35, alpha=2, M=2,
   P(h)=15-2h, X=5, H=1, q=1, E=1, B=2, R={1}, covered p=5.
   Check unit/order conditions, e=0, D=-47, true (k,j)=(0,1), signed
   giant exponent -46, global equality, the recovery coefficients
   [-70,24,-2], and roots {5,7}, only 5 in the block. Retain both giants
   and every index in the two baby chunks, including final-chunk padding.
7. **Bypassing component checks fails.** N=21, alpha=2, M=5, P=35,
   X=3, H=1, q=1, E=2, B=4, R={0}. beta=11 has global order 6 but
   component order 2 modulo 3. Check the gcd at j=2 returns 3. Deliberately
   record the unsafe global matches if that check were skipped: the true
   first tag is matched to j=0 instead of its local j=2 and neither global
   recovery has a root in the block. This is a negative control, not a
   failure of the guarded consumer.
8. **Powering can destroy order.** N=35, alpha=2, M=12, B=2.
   Check alpha has order 12, beta=1, and the first order-test gcd is N.
   Reject treating large order of alpha as a beta-order certificate.
9. **Separate normalization changes the shared base.** M=6,
   P1(h)=2h and P2(h)=3h. Check reduced denominators 3 and 2, unchanged
   image sizes 3 and 2, and distinct powered bases alpha^3, alpha^2 for
   alpha=2 modulo 35. No joint cost is inferred from separate normalization.
10. **Scope controls.** Fixed Q(h)=h^2 modulo 16 on the retained domain
    {0,4,8,12} has image {0}; fixed P(h)=16h modulo 16 has image {0}
    before normalization; fixed h^4 modulo 5 has image {0,1}. Also check
    Q(h)=h modulo 6 on {0,1} has two image elements, whereas the Cartesian
    product of its projections modulo 2 and 3 has four elements. These
    certify failures of omitted hypotheses, not of the stated theorem.

All expected conclusions were derived on paper before this registration.
Keep script, preregistration, stdout, stderr, run manifest and all case outcomes.
Hash the script before execution and all delivery files at completion. Do not
run shared solver/Lean checks; no shared implementation is being edited.
