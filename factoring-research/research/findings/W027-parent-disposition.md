# W027: exact envelope optimum, restricted to its representation

The independent [review](W027-optimal-envelope-review.md) was read in full.
Accept exact minimization of F(c)=cW+sum w_i*abs(centered_Q(c*d_i)) for
1<=c<Q by fixed-dimensional integer feasibility, recomputing errors from the
optimal c. Normalization preserves F/Q and yields the floored carry bound,
including zero. Every legal precision reduction and constant hybrid lies in
this search. **Verified complete factoring improvement: NONE.**

Scope and implementation repairs:

- The comparison class requires Q'>=ell and normalized c' an ell-unit.
  No claim is made against a no-filter Q'=1 representation.
- Substitute singleton coordinates and collect like monomials before
  minimizing. The fixed-basis weighted envelope is not a polynomial sup norm;
  the review gives a synthetic cancellation example where substitution helps.
- Also return the best c'=1 option by testing c=ell^(L-j) for 1<=j<=L.
  This costs O(LD) envelope arithmetic and preserves sharing that a general
  c' can lose. Smaller carry alone does not imply a cheaper joint evaluator.
- Only c and the coefficient quotients need be integer variables; the
  absolute-value auxiliaries can be continuous. The resulting D+1 integer
  variables give polynomial bit cost for fixed D, not constant time in N or
  a demonstrated practical solver. A second binary search can select the
  least optimal c for reproducibility.
- Freeze the selected representation during collision localization, as
  explained in [W026's disposition](W026-parent-disposition.md). Merely paying
  for reoptimization does not preserve the same product.

Resolve the review's residue question directly: up=vq modulo ell implies
vq-u=u(p-1) modulo ell. With u a unit it is a unit exactly when p!=1 modulo
ell. This concerns the retained witness; the integer exponent can be nonzero
even in a discarded residue class (the recorded p=7,q=11 example gives 54).
Negative multipliers have the same absolute envelope after sign changes of
the full expression and carry. This does not require identifying that change
with only a root-sign flip.

Evidence: three manifest entries match; the report entry does not match the
full delivered file because its disclosed final handoff paragraph was appended
after hashing. The exact preceding report prefix matches the listed hash.
The full delivered report hash is recorded in
[intake](W027-parent-intake-hashes.json). No external manifest anchor was
supplied. The review relies on its frozen W025 and frontier inputs, which
changed concurrently. No experiment or shared-code change occurred.

The optimum cannot beat the genuine width W/Q. Even ideal carry does not
improve the explicit-anchor one-fifth cost envelope. The useful next question
is whether one can evaluate the joint anchor family without generating every
anchor, while retaining a supplied shared c' when needed. No such complete
evaluator is provided here.
