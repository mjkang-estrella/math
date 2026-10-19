# Family168: parabolic and intermediate-kernel leads are paid

This is a pre-freeze primary-proof comparison, not a candidate theorem.

Source168 `thm:main` concerns every abstract Bruhat interval isomorphism in arbitrary Coxeter systems, including infinite and noncrystallographic systems. Its `cor:all-subintervals` already preserves the ordinary P and R polynomials on every subinterval. The operative proof in `05-comparison.tex` obtains the edge-image inclusion by localizing at root-plane primes, propagates nonnegative deficits through a transported edge schedule, uses reciprocity in both directions, and forces every intermediate deficit to vanish. It then recovers all terminal-kernel freeness by a reverse induction. These operations are stipulated inputs, not truth-audited here.

The first lead was a parabolic extension. Its strongest compatible existing reduction is **Barkley–Gaetz, arXiv:2404.04246v2**, Theorem1.6 and the full proof of Theorem3.3, not merely Deodhar's formula with an unjustified coset-preservation assumption.

Let `u,v in W^J` and let A be the atoms of `[u,v]` that lie in `W^J`. Their Lemma3.4 identifies the relevant coset portion intrinsically as

    u W_J intersect [e,v] = { y in [u,v] : no a in A satisfies a<=y }.

The proof uses monotonicity of parabolic projection and the length grading on the quotient interval. Thus an interval isomorphism preserving only these marked atoms already preserves precisely the summation set, and preserves the length difference by rank. Their Deodhar formulas then give

    R^(J,x)_(u,v) = sum_y (-x)^(rank(y)-rank(u)) R_(y,v), x=-1 or q,
    P^(J,q)_(u,v) = sum_y (-1)^(rank(y)-rank(u)) P_(y,v),

where y ranges over that intrinsically determined coset portion. Source168 supplies all ordinary polynomial equalities needed by these sums. This pays even the atom-marked refinement for both R parameters and for P with parameter q.

For P with parameter -1, the stronger marked-subset hypothesis that the isomorphism sends the whole `[u,v] intersect W^J` to its counterpart supplies the quotient subintervals. Apply the preceding R calculation on each such subinterval and use parabolic reciprocity and the strict degree bound. This is exactly Theorem3.3(c), with no additional compatibility issue remaining. Arbitrary Coxeter systems and all finite intervals are retained.

One must not assert that marking only bottom atoms also preserves `P^(J,-1)`. The primary's Remark1.5 gives the Boolean-rank-three S4 example with values1 and1+q. This is an existing counterexample to that stronger formulation, not a newly discovered obstruction or a candidate refutation.

The second lead was equality of ranks of intermediate sheaf kernels along transported schedules. The source's **`rem:terminal-ranks` already states and proves exactly that conclusion**, using the exact transition matrices and the same initial vector. Comparing only the source's headline KL theorem would miss this paid operation. Neither this statement nor a change of coefficient-ring dimension is selected.

The paper has one catalogue manuscript and no separate same-family catalogue companion. Its introduction, comparison/induction proof, corollary and final remark were read; the earlier dihedral/localization proof files were not fetched for this screen because their operations were used only as stipulated interfaces exposed in the read proof. No integral-coefficient, modular, unequal-parameter, or intersection-cohomology-ring analogue is inferred.

Primary proof: https://arxiv.org/pdf/2404.04246v2 . Read limits and exact byte hashes are retained separately. This is a proved compatible reduction, not a search-absence or worldwide-priority claim.
