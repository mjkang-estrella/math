# Two early zero-credit exclusions

## 1. One-crosscap Gram determinant

Actual primary: Christiana–Ibarra–Montoya-Vega, arXiv:2504.16439v1, Definitions3.1–3.2 and Conjecture3.5 pp4–5. For every integer n>=2, its specialized matrix on Mb_(n,1), of size C(2n,n-1), is conjectured to have determinant

    product_(k=2..n) (T_(2k)(d)-2)^C(2n,n-k)
  = product_(k=2..n) ((d²-4) S_(k-1)(d)²)^C(2n,n-k).

The source uses T0=2,T1=d and S0=1,S1=d, both with recurrence X_(j+1)=dX_j-X_(j-1). The matrix substitutes y=0,w=1 into the actual Klein-bottle gluing form; this is not an arbitrary principal submatrix of a generic Gram matrix. The later actual companion 2402.09704v2 (27Nov2025), Theorem6.7 and Conjecture6.9 pp15–16, still states the same residual determinant. Thus a later source version has been read, rather than relying on the April2025 label.

Concrete classical route: Morin-Duchesne–Saint-Aubin, arXiv:1203.4996v3 (26Feb2013), §2.3, Definition3.2 pp11–12, §4 opening p15 and Proposition4.3 Eq29 pp25–27. Their periodic link states with N sites and h defects have size C(N,(N-h)/2). Set N=2n,h=2, beta=d,v=1. Cutting the unique crosscap arc gives two inner-boundary defects. Conversely join the two defects through the crosscap; the noncrossing annular state recovers the unique one-crosscap diagram. No defects are labeled independently, so no factor2 is introduced.

Compare the pairings literally. If a gluing joins the two defects from one side to each other, the other side's defects also join each other: capping produces both an x-loop and a y-loop and is killed by y=0. Otherwise the defects connect across the gluing; capping yields a single w-loop, evaluated1. No annular essential closed loop can coexist with the surviving through strands; all remaining loops are contractible, evaluated d. This is exactly Definition3.2's periodic Gram form at v=1. The arbitrary winding weight disappears at v=1. The identification is by matching diagram bases, not a nontrivial matrix scaling.

Proposition4.3 therefore gives, up to sign,

    product_(j=1..n-1) (4-4cos²((j+1)Lambda))^C(2n,n-1-j),

with d=-2cos Lambda. Each factor is minus (T_(2j+2)(d)-2). The paper explicitly announces on p15 that its determinant equalities are up to sign; overlooking this would give the wrong sign already at n2. The sign is fixed by monicity: the diagonal term of each source entry is d^(n-1); any off-diagonal has smaller d-degree, because n-1 closed contractible loops require every ordinary arc and both defect endpoints to agree. Thus the determinant has leading coefficient1. The product of T_(2k)-2 is monic as well, so the plus sign is forced. Since d ranges over an interval, the trigonometric equality gives a polynomial identity. The source Lemma2.5 gives the S-version.

Conclusion: recommend routine classical-corollary EXCLUSION. This is an ordinary reduction, not an independent adversarial review or a claim that an earlier paper explicitly cites and answers the later conjecture. A reviewer should attack the basis/gluing identification first. No eligibility or priority PASS is claimed. Exact n2 determinant checked independently: d²(d²-4).

## 2. Hedgehog {1,2}-delay unimodality

Actual primary: Ibarra–Landry–Montoya-Vega–Przytycki, arXiv:2311.18059v1, Proposition2.5 pp7–8, Proposition2.8 pp8–9, Conjecture4.1 p12. For every n-ray star and every delay taking values in {1,2}, Q=p(q)[n-1]_q!, where p has 0/1 coefficients and degree<=n-1. All-zero p gives zero and causes no difficulty. Current arXiv record contains only v1; author publication listings report Contemporary Mathematics834(2026),95–108. That published body has not been obtained; no assertion of identical final wording.

Here is a complete elementary classical bridge, with no need to trust the source's lengthy coefficient display in Proposition2.8.

Let m>=2, p=sum_(i=0..m) a_i q^i with arbitrary a_i>=0, and b=[m][m-1]. For c=pb put D_t=c_t-c_(t-1), extending coefficients by0. The first differences of b are +1 at0..m-2, zero at m-1, and -1 at m..2m-2. Hence D_t>=0 for t<=m-1, D_t<=0 for t>=2m-1, and for m<=t<=2m-2,

    D_t = sum_(i=t-m+2..m) a_i - sum_(i=0..t-m) a_i.

This middle expression decreases with t. Thus the D_t have at most one positive-to-negative transition and c is unimodal. This includes m2 (the middle range has one term). The n1,n2 star cases are immediate; for n>=3 set m=n-1.

Finally multiplying ANY nonnegative unimodal polynomial a by [r] preserves unimodality. The first difference at k of a[r] is a_k-a_(k-r). If a has a mode j, this is nonnegative for k<=j and nonpositive for k>=j+r. Between j and j+r the first term decreases and the second increases, so the difference decreases and changes sign at most once. This elementary special case is the uniform-kernel instance of classical strong unimodality. Multiply p[n-1][n-2] successively by [1],...,[n-3] to get p[n-1]!. This closes every n and every literal source delay.

Conclusion: full ordinary source answer, but a routine combination of source Proposition2.8 and elementary unimodality preservation. Credit0, no nomination or formal investment. No claim that the exact endpoint was previously published. 49 fixed support checks corroborate the smoothing identity only; the argument above is universal.
