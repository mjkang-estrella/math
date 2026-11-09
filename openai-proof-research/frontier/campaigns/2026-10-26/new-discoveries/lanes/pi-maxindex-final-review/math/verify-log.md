# Independent math verification log (reviewer's own computations)

1. Exact Fraction sharpness check d=5..15: A_top+G_top-(m+3) = (m-1)^2/(4m^2+m) exactly
   for every d; A_sel<=A_top and G_sel<=G_top with equality (selections attain top sums);
   d=5: A=29/9, G=11/6, total 91/18 > 5. Witness satisfies bound at k=2d-5.
2. Random search (seed 7, 4000 probability vectors with two zero coordinates each,
   d=5..10): violations found exactly at k>=2d-4, none below (classification shape).
3. Dense-grid spot check d=5, k=5: max A+G = 4.5615 < 5 over 200k random vectors;
   unit vector 4.0; uniform-tail 2.5; witness 4.5556 < 5.
4. Hand re-derivation of every PROOF.md/paper step (incidence identity, c_i bounds,
   weighted bound, geometric Cauchy bounds, strict-gap algebra (2m-7)^2+36 and 3,
   high-max extras accounting, 2D Cauchy, sharpness algebra r=2m => (m-1)^2/(4m^2+m)):
   all confirmed; see review.md Gate 2.
5. Parent script scripts/check_bounds.py rerun: PASS (840 probability vectors,
   99 sharpness parameters, exact Fractions).

All computations independent of the parent's formalization; supporting evidence only —
the proof itself is the Lean development (Gate 3).
