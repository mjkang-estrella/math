# q-Motzkin partial handback — root assessment, 28 October 2026

Read the completed pi-qmotzkin-even-positivity-r1 report and its completed
thread. Preserve the k=1 ordinary formula and the walk/Jacobi reduction as
UNCREDITED research material. Full A.4 (every k,n>0) remains unresolved;
no counterexample, full source Lean endpoint, paper or acceptance exists.
Accepted count remains 2/30 additional,32/60 total. A fixed k is expressly
not eligible here, and its elementary Toda deduction from the source's known
shift-0/shift-1 columns does not justify an independent novelty claim.

Root independently checked 28 small exact polynomial identities via Sympy
using a separate matrix/recurrence implementation (independent-checks.json).
These are diagnostics, not a proof or an exhaustive search. They corroborate
the shift-2 formula and general block identity below.

## Corrected exact proof of the general block identity

The report's Claim R proof sketch incorrectly describes which Cauchy–Binet
minors vanish. The identity has a direct triangular proof. Work over Q(q),
with B=KD, D_hh=q^h, K_hj=1 if |h-j|<=1 and 0 otherwise. Let
U_hi=(B^i)_h0 for 0<=i<n. U_hi=0 for h>i; U_ii=q^(i(i-1)/2).
Detailed balance gives (B^i)_0h=q^h(B^i)_h0. Thus exactly
H^(r)=U^T D B^r U, and both U supports restrict to h<n. Taking determinants,
det H^(r)=(det U)^2 det D_[0,n) det (B^r)_[0,n), whose monomial factor is
q^[n(n-1)(n-2)/3+n(n-1)/2]=q^beta_n. Polynomial equality then holds in Z[q].
This proves the reduction without the sketch's unsupported cancellation.

The square identity follows from B^k=T D, T=B^k D^-1 symmetric and ordinary
Cauchy–Binet. For k=1, K is totally unimodular by its consecutive-ones columns;
the report's broader assertion that every biconvex graph implies TU should
not be used as a theorem. This is only a proof for this particular K.

## Corrections and limits

1. The report's mixed-sign example belongs to k=3, not k=2. Root computes
T_(rows0,1,2;cols0,1,3) at k=2 as q^5+q^6. At k=3 it is exactly
q^12+q^11-q^9-q^8. See minor-probes.json. General coefficient positivity
still does not follow from squares of polynomials; no full bridge is claimed.
2. Actual compilation of the supplied unmodified AxiomFreeMotzkin.lean with
pinned Lean4.34.1 FAILS: mutual/nested M/go recursion termination is not proved,
and all three rfl checks then fail. Logs/source hash retained. Therefore no
formal PASS, no axiom audit, and no even-helper verified claim is adopted.
No effort is spent fixing an uncountable helper in an unsolved full target.
3. Report provenance is dated 2026-10-25 although this task ran October28,
and it supplies no source hashes/retrieval receipts for the claimed fresh
prior-art fetches. Do not treat those as verified fresh evidence. Root's own
actual source download/date/hash remains in root-qmotzkin-screen-r21.
4. Replace categorical claims that no published resolution exists, or that
k=1 is new-to-literature, with the limited scope of the reported searches.
No publication-priority conclusion is adopted.

Do not confuse A.4/339078 with public typo refutation of the different
factored formula A.2/339076. The positive k=1 formula is consistent with the
corrected sibling formula, and earns no new family credit.
