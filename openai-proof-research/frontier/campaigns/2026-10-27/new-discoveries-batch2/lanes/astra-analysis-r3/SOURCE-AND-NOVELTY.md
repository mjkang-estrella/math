# Source and bounded prior-art audit, 2026-10-28 UTC

## Horwitz primary and scope

The actual cached [math/0007095v1 PDF](https://arxiv.org/pdf/math/0007095v1) pp12–13 and its extraction were read. Both complete pages were visually inspected using the existing r2 page renders. Conjecture 15 concerns all positive triples and equality only on the diagonal. Conjecture 16 concerns the two specified pairwise-map inequalities on all positive triples. The explicit U0 and U1 formulas, not a database paraphrase, define the quantities in the proof notes.

[Live arXiv abstract](https://arxiv.org/abs/math/0007095) still lists v1, submitted 15 July 2000, and JMAA270(2002)499–518. The publication is DOI10.1016/S0022-247X(02)00083-5. **The 2002 published body was not obtained/read.** Prior lane r2 records HTTP403 from the publisher. This limitation is inherited candidly; this lane did not bypass it or infer unchanged conjectures from metadata. It is a material gate if a result is eventually proposed.

The live [376978](https://mathdb.com/api/posts/376978) and [376979](https://mathdb.com/api/posts/376979) records were saved. Empty solution arrays/open labels are not treated as proof of novelty.

## Closest body actually inspected

[Pasteczka, Multivariable generalizations of bivariate means via invariance](https://link.springer.com/article/10.1007/s00010-024-01113-w), published online9September2024, volume99(2025)841–861: read Section2.1 Proposition2.1, Section3.1 Proposition3.2, Theorem1 and Proposition3.3 including their proofs. The results establish existence, uniqueness, preservation of symmetry/monotonicity/convexity/concavity, and comparison of barycentric extensions from comparable input means. They do not supply the particular U0/U1 Lyapunov signs in those bodies. Applying Proposition3.3 would require showing that U0/U1 themselves are appropriate invariant extensions, something not proved here and not assumed by the source. Thus no precise subsuming endpoint was established from this paper. This is NOT complete clearance of all comparison literature.

[Jarczyk–Jarczyk, Invariance of means, DOI10.1007/s00010-018-0564-5](https://d-nb.info/1167284534/34) was retrieved. Its table of contents and full-text term matches were inspected; the focus is two-variable invariance. No relevant all-triple result was identified, but the entire72-page proof content was not read. An initial mistyped DOI in a web request opened an unrelated Baron article; it was not used as evidence.

Horwitz's later [1208.1457](https://arxiv.org/abs/1208.1457), weighted quasi-arithmetic invariance, was located, but direct HTML/PDF requests for v2 returned404. Its theorem body was not read or used to clear the target. Those failed responses are saved and marked as failures in fetch logs; `horwitz2012.pdf` is an HTML404 body, not a PDF.

Bounded web queries included exact target phrases, Horwitz/Stolarsky/invariant-logarithmic combinations, Conjecture16, and mixed-mean comparisons. No public complete solution was located. Search silence is not novelty evidence, and no exhaustive citation, subscription-index, or public-registry coverage is claimed. Prior r2 registry observations are not a fresh registry audit by this lane.

## Secondary lead: Byczkowski–Małecki

Retrieved and read actual [math/0512294v1](https://arxiv.org/pdf/math/0512294v1) definitions and Section5 Conjectures5.1–5.2. The source has **rho=(n-2)/2**, unlike the r2-cached MathDB paraphrases' (n-1)/2. Correcting that is not a discovery. The source seeks F(k,-rho;k+n/2;z) zero-free in Re k>=-n/2-epsilon, in its intended ball domain0<=z<1. No counterexample by evaluating poles, unrelated z, or the database's wrong rho is proposed.

The [2007 publisher landing page](https://link.springer.com/article/10.1007/s11118-007-9050-8) was saved; its published PDF body was not read. A relevant actual followup body was read around equation4.6, printedp162: [Byczkowski–Chorowski–Graczyk–Małecki, Hitting half-spaces or spheres by Ornstein–Uhlenbeck type diffusions](https://www.impan.pl/shop/en/publication/transaction/download/product/86786). Its introduction says the older hypergeometric zero conjectures remain unsettled, and the proof around4.6 establishes a Legendre denominator zero-free region Re w>-(n-2)^2/8. The paper explicitly compares this with Conjecture5.2. This is prior partial progress; no claim is made that its different spectral parameter gives the full source strip. Any future approach must compare this actual result to avoid rediscovery.

A numerical complex-root exploration failed with mpmath `NoConvergence`, saved in `checks/hypergeom-failure.txt`. No zero-free conclusion follows. No discovery or exclusion proposed for this family.

## Other brief check

The r2 cached actual published Mittag–Leffler PDF was converted to text in this lane. Its closing Conjectures25–26 were read to consider it as a backup; no new proof or novelty assessment was obtained. A normalization objection to “log E is complete Bernstein” would concern a translation already discussed in the source and is not a qualifying refutation.

## Strongest objections

1. Fatal at present: neither H0 nor H1 is proved for all p,q>0. Exact finite interval checks cannot replace this.
2. A repeated-input/subfamily result or any of the helper envelope inequalities, on its own, earns no discovery credit. No one-variable result is represented as the all-triple endpoint.
3. The actual2002 Horwitz published body remains unread, and the bounded comparison search is incomplete. Even a mathematical proof would not yet have full source/novelty clearance.
4. The generic invariant-mean framework is known and credited. The reduction itself is elementary algebra, not a candidate outcome.
5. There is no literal-source Lean endpoint. Under the task instruction to start meaningful Lean only after a complete ordinary proof, no Lean files were created.
