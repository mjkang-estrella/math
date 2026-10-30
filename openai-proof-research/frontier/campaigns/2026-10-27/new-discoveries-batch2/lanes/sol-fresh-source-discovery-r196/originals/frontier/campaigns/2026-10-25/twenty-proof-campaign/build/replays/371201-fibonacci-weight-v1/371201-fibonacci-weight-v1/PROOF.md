# Weight preservation for modular recurrence periods

Let m,d be positive integers with d dividing m, and let ε be an integer. On X_s=(Z/sZ)² define T_s(a,b)=(b,a+εb). Its inverse is (a,b)↦(b−εa,a), so all states belong to permutation orbits. These orbits are exactly the recurrence periods up to cyclic shift: iterating a state produces consecutive entries of the scalar recurrence; returning to the consecutive pair is equivalent to repeating the entire sequence. The orbit cardinality equals the least positive return time, including fixed points.

Let π:X_m→X_d be coordinatewise reduction. It is a surjective additive homomorphism and πT_m=T_dπ. Consequently π maps each upstairs orbit onto a downstairs orbit. Surjectivity onto that orbit follows by lifting each nonnegative iterate of any image point.

For a downstairs orbit q, the inverse image π⁻¹(q) partitions into precisely the upstairs orbits mapping to q. All fibers of a surjective homomorphism between finite groups have the same cardinality k: translation by a lift of a target difference gives a bijection between any two fibers. Counting all states gives |X_m|=k|X_d|; counting only π⁻¹(q) gives |π⁻¹(q)|=k|q|. Therefore

\[
\sum_{p:\pi(p)=q}\frac{|p|}{m^2}
=\frac{|\pi^{-1}(q)|}{|X_m|}
=\frac{k|q|}{k|X_d|}
=\frac{|q|}{d^2}.
\]

The moduli are positive, so denominators are nonzero. This proves the source assertion for ε=1 and ε=−1, and the same proof works for any integer coefficient. It includes the constant zero period of length one. No claim is made about the source's other conjectures.

## Formal correspondence

`Period` is the quotient by actual permutation cycles. `period_eq_iff_iterate` connects quotient equality to time shifts; `orbitSize_eq_minimalPeriod` identifies the length. `orbit_sum_eq_preimage` proves the partition identity. `uniform_fibers`, `preimage_card`, and `total_card` prove the group-fiber count. `recurrence`, `reduction_surjective`, and `reduction_commutes` construct the concrete maps. `reduction_fiber_card` derives the value (m/d)². The final `fibonacci_weight_preservation` has no assumed orbit-counting or fiber-counting hypotheses.

## Attribution

This is a full formal verification of the orbit-counting proof already posted by **Shivam Patel**, MathDB solution b64f2547-2755-408d-8ca3-997917a47b33, 20 August 2026. The source target is Pudelko, [arXiv:2510.24882v2](https://arxiv.org/html/2510.24882v2), Conjecture17, equation(19). No mathematical novelty or priority is claimed. Source records and review are included separately.
