# W026: accept affine admissibility with fixed-family recovery

The independent [review](W026-affine-exception-review.md) was read in full.
Accept the affine multiplier feasibility and common-valuation normalization,
and the exceptional-residue tree, with the following repairs. This is an
admissibility primitive; the generic size comparison already loses to constant
scaling. **Verified complete factoring improvement: NONE.**

- Use exact signed endpoints after x=j+ell*y. For n nonempty original integer
  points, D=ceil(log_ell n) gives at most (ell-1)D+1 retained intervals and
  at most 4D integer feasibility calls. Empty inputs produce the empty product.
- Failure of the sufficient pigeonhole condition does not establish ILP
  infeasibility. A constant-one fallback has its own width bound and need not
  satisfy the failed affine caps. At a singleton, use the original precision
  and exact signed carry interval; it can be empty.
- Construct the public leaf family before evaluating its product. During
  localization, keep multipliers, precision, coefficients and carry family
  fixed. Reacquisition is permitted during initial construction, or as a new
  complete search with its own proof; paying for it does not preserve an
  already detected collision. This also repairs the optional-reoptimization
  wording of W027.
- The explicit quartic cancellation additionally needs d4 divisible by H^4.
  A unit cubic quotient alone is insufficient. After substitution, reduce
  coefficients modulo the original Q to control operand widths.

The bad affine residue really can erase a covered witness, so the branch
fallback is necessary. The review's p=5,q=7,ell=3 example exhibits this. The
product cost and any carry inflation remain payable. The W020 expected-trial
interface applies to a fixed public family independent of its sampled base.

All 18 delivery payloads match the local manifest; no external manifest hash
was supplied. See [intake](W026-parent-intake-hashes.json). No experiment ran,
and no shared solver or Lean code changed. Preserve the report's counterexamples.

Constructive consequence: affine support recovery is available if a genuinely
short, structured multiplier is found. Generic coefficient volume does not
provide it. The remaining main-thread work is a paid joint evaluator or a
different factor-bearing invariant, not another unpriced multiplier oracle.
