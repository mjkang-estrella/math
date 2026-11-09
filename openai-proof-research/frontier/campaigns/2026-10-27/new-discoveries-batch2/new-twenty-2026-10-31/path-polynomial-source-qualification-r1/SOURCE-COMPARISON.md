# MathDB331498 source comparison

All references below are to actual cached or newly fetched bodies unless explicitly marked metadata-only. `source-passages.txt` preserves loci; `body-inventory.json` preserves page-indexed textual example/figure inventory. Frozen r254 paths are absolute in frozen-inputs.json and are dependencies, not copied recursively.

## Exact statement and notation

ABM arXiv:1312.4487 v1, v2, v3 all retain Section 6.3 P2, with the same Dyck vertical projection, corner statistic and reported test range. v3 is byte-identical to frozen abm-pdf.body. Target P2 and N1–N3 pages 32–33 were visually inspected. Earlier versions were target-section text-compared, not audited line by line in their entirety.

Kuszmaul arXiv:1510.00777 v1 Section 4 (printed p10) explicitly defines a=#N, b=#S, c=#E, d=#W. Consequently a=b=n, c=d=m. In v2 Section 4 (printed pp14–15), these become u=#N, d=#S, r=#E, l=#W, hence u=d=n and r=l=m. The old a,b,c,d persist in Conjecture 4.1 and a footnote. This is an evidenced version-history bridge, not a guessed ordering: a=u, b=d_v2, c=r, d_v1=l. Original ABM j=n is vertical semilength; horizontal semilength i=m; total loop semilength is m+n. ABM's weight a is a different use of the letter a: it equals secondary weight x, not a step count.

For any n,m>=0 and V of length 2n with n N and n S, every prefix having nonnegative vertical height, let Q(V,m) contain every quarter-plane loop with vertical projection V and m E,m W. Equivalently, sum shuffles of V with ALL horizontal Dyck words of semilength m, not a fixed horizontal projection. Define c(P)=#adjacent NW + #adjacent ES and G(V,m;x)=sum_{P in Q(V,m)} x^c(P). P2 asserts G(V,m;y-1) in N_0[y] for every V,m. Nonempty balanced positive vertical paths are Dyck paths; “positive” here permits height zero.

MathDB raw/literal record and results.json entry were read. The literal a,b,c,d are inherited from v1; there is no typo-only refutation. Version1 first-stated date does not supersede ABM's 2013 statement chronology.

## Known proofs and ranges

ABM Propositions19–20: arbitrary vertical projections with horizontally unrestricted walks; factorization by horizontal blocks and positivity of the general-loop generating function. Section4.5/Proposition22: upper-half-plane loops. Horizontal nonnegativity in Q(V,m) is an extra condition, and restricting a positive signed enumerator to a subfamily does not preserve positivity. P2 explicitly follows these proofs as a conjecture, not a corollary.

Kuszmaul Theorem2.16 proves the signed statistic distribution; v1 Theorem3.11 becomes v2 Theorem3.13, with toggle classes counted by Bin_j(2j). Theorem3.13 is positivity for ABSOLUTE SIGNED peak-count on a fixed pair of loop projections. Actual peak-count is a different statistic. v2 Conjecture4.2 is the missing positivity equivalence, not a theorem. Its verification is reported only for u,d,r,l<=5. Parity gives G1(-1)=G2(-1), hence b0 positivity, not all coefficients. The closing special case H=E^m W^m,V=N^n S^n makes actual and absolute signed counts equal; it does not prove all H for that V. Thus even restricting V to one mountain is not justified as globally solved by that paragraph.

P2 reported range in ALL THREE ABM versions: n=j<=5 AND m+n<=10. The inherited shorthand “n,m<=5” is incomplete: e.g. n=1,m=9 lies in the ABM range. (n,m)=(6,6),(6,7),(7,6) have total semilength 12,13,13 and are outside both reported ABM P2 and Kuszmaul Conj4.2 ranges while remaining inside P2. ABM Conjecture10 aggregated positivity checked through half-length100, and Conjecture13 refined only by counts through40; these are sums over V and do not test P2 at those sizes. Do not confuse aggregated data, P1 parity tests, and P2 tests.

N1 nonloop endpoints, N2 fixed BOTH projections, N3 V=SSNN are outside P2. The secondary x^2+12x+15 example is positive in x+1; it separates toggle-buildability, not positivity. These are source-owned controls with zero credit.

Elvey Price arXiv:1912.00056 Theorem2.11 proof compares growth rates via path classes; Section3 derives an analytic inequality for P(t). Its body explicitly says the three quarter-plane conjectures were not proved. Equality of radii and analytic inequalities cannot recover coefficients for each fixed V. No complete bridge from this paper to P2 was found.

## Material body gaps and visual limits

The ABM DOI's frozen HTTP200 response is 2687-byte landing HTML, not a journal proof body. Correct journal identifier from public publisher metadata is S019566981400136X, DOI10.1016/j.ejc.2014.08.024, EJC43(2015)131–164. This lane mistakenly tried a guessed PII S0195669814001541/pdfft; it returned403. That wrong-route response is NOT evidence that the correct ABM PDF is unavailable, nor a journal-body comparison. No retry or alternate publisher route was attempted after denial.

Secondary DOI10.1016/j.ejc.2016.09.007, EJC60(2017)100–113, PII S0195669816300841: pdfft returned403. No retry/bypass. Both journal proof bodies remain unread and no publisher-versus-arXiv identity is asserted. The arXiv latest versions are not automatically the versions of record.

ABM text inventory identifies Figures1–9 and B.10–B.12: stacks/arches (1–5), ratio/asymptotic plots (6–9), staircase/injection constructions (B.10–B.12). P2 section has no numbered figure/table; its negative examples are text, visually confirmed on32–33. Secondary has no numbered Figure/Table captions detected; its words/path diagrams and open-question example were reviewed textually, p15 visually. Full visual audit of every figure in every version, appendical injection diagrams, and successor figures was NOT completed. This remains explicitly open, particularly for missing journal versions. No claim of full illustration clearance.

Bounded live exact-title/DOI/positivity/proof/erratum/retraction searches (saved search-results.json and errata-search.json) located no full P2 resolution or withdrawal. These searches are not a complete citation index, Crossmark audit, or retraction-registry certification. A possible broader cited-work source, Bostan's HDR, surfaced but was not body-reviewed. No known proof/withdrawal STOP condition established; absence of a search hit does not clear those gates.
