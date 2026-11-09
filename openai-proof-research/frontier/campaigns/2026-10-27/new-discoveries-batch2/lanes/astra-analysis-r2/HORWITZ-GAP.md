# Unresolved Horwitz lead, zero credit

Primary: arXiv:math/0007095, Section 4, Conjectures 15--16, source pp12--13 visually inspected. Current publication identified as JMAA270(2002)499--518, DOI10.1016/S0022-247X(02)00083-5. The actual publisher request returned403; no bypass attempted. The 2000 preprint alone does not certify current novelty.

The source defines L(a,b)=(b-a)/(log b-log a), continuously extended at a=b, and the invariant L3 by repeated replacement with the three pairwise logarithmic means. Source Conj15 is U0<=L3<=U1 with equality only on the diagonal; Conj16 proposes U0(Tv)>=U0(v), U1(Tv)<=U1(v), with T the pairwise map. Definitions and both exact formulas are in saved source pp12--13. Source Theorem12 gives Conj16=>Conj15.

## Concrete mathematical reduction

For a repeated-input triple (1,1,t), t>0, t!=1, set l=(t-1)/log(t). Direct continuous divided-difference limits in the source formulas give

    U0(1,1,t)^2=(t-1)^2/[2(t-1-log t)],
    U1(1,1,t)=(t-1)^2/[2(t log t-t+1)],
    U0(1,l,l)^2=(l-1)^2/[2(log l-1+1/l)],
    U1(1,l,l)=(l-1)^2/[2(l-1-log l)].

All denominators are positive, from strict log x < x-1, its reciprocal form, and strict convexity of x log x. Both Conj16 inequalities on this family reduce to the SAME scalar inequality R(t)>=0:

    R(t)=(t-1)^2(l-1-log l)-(l-1)^2(t log t-t+1).

Indeed the lower-mean residual is

    R0=(l-1)^2(t-1-log t)-(t-1)^2(log l-1+1/l).

Their difference is exactly

    R0-R=(l-1)^2(t-1)*(log t-(t-1)/l)=0.

This equivalence is proved algebraically, but the sign R>=0 has NOT been proved here. It is only a one-dimensional subfamily, not the full target.

A formal Taylor calculation at t=1+h gives R=h^6/576-13h^7/4320+O(h^8); this agrees with the positive local direction. Save no all-t conclusion from this finite expansion. At t->infinity the paired U1 values have ratio tending1; absolute large-scale closeness makes naive double precision unsuitable.

## Experiments and limitations

checks/horwitz_explore.py sampled 500 deterministic log-scale triples (exp x,exp y,1), x,y in [-15,15], mpmath precision80. No numerical violation found, both for the pairwise map and 12-step intervals for L3. These are exploratory floating-point evaluations, not interval certificates or proof. The test knows no bound outside the sample.

## Next unresolved gap / falsifier

A strict negative value of the exact scalar residual R(t), with certified logarithm enclosures at a positive t!=1, would refute Conj16 without any coincident-input ambiguity (continuity also gives distinct nearby triples). It would not by itself refute Conj15. A positive solution of the scalar subproblem would still leave the all-distinct two-parameter problem and the source/publication/prior-art gate. Do not count either reduction or local series.

Closest body inspected: Pasteczka, Multivariable generalizations of bivariate means via invariance, DOI10.1007/s00010-024-01113-w. It develops the barycentric extension and preservation/comparison framework. It does not provide these explicit Stolarsky inequalities in the passages inspected. A complete all-citing-literature investigation is not claimed. Public registry filename/body keyword searches for Horwitz/Stolarsky/invariant logarithmic had no match in the saved snapshots; this is not a novelty certificate.
