# Source, full target and disposition

**Disposition: unresolved; zero credit.** One source claim was selected, within the three-claim ceiling. This is an arithmetic polynomial irreducibility problem, distinct from concurrent structural r165. Sirola/Dumas remains classically excluded, Gatzweiler–Krattenthaler Conjecture4 remains the old r23 problem, and Ulas remains unresolved r161; none was reinvestigated.

## Literal statement and normalization

Yoshinori Kametaka, *On the Irreducibility Conjecture Based on Computer Calculation for Yablonskii-Vorobiev Polynomials Which Give a Rational Solution of the Toda Equation of Painlevé-II Type*, Japan J. Appl. Math.2(1985)241–246, DOI10.1007/BF03167047. Complete published six-page PDF obtained and text read. On p243 the author states that the corresponding F_n are irreducible through n<=23 and conjectures essential irreducibility for all. Section4 lists modular certificates through23; this is a known finite case, not novelty evidence. The abstract's shorthand about P_n is not the target.

Set P_0=P_1=1 and

    P_(n-1) P_(n+1) = t P_n^2 + 4(P_n')^2 - 4P_n P_n''.

Write d=n(n-1)/2, f=floor(d/3), g=d-3f (0 or1). In the source's equations(1.8),(2.1)–(2.3),

    P_n(t) = 4^f t^g F_n(t^3/4),
    F_n(X) = sum_(j=0)^f (P_(n,j)/4^j) X^(f-j),
    P_n(t) = sum_(j=0)^f P_(n,j) t^(d-3j).

The substantive target is: for **every integer n>=3**, the monic nonconstant F_n in Z[X] is irreducible over Q. The source convention treats F_0=F_1=F_2=1 separately; this removes units, not a substantive exception. No claim that F irreducibility alone implies irreducibility after cubic substitution is used.

## Actual later primary bodies and what they do

Kaneko–Ochiai, *On coefficients of Yablonskii–Vorob'ev polynomials*, J.Math.Soc.Japan55(2003)985–993, DOI10.2969/jmsj/1191418760: complete author-hosted published-text PDF read, especially Theorems1–3, determinant formula(7), Proposition10, Corollary12 and Remark14. Their normalization is

    T_0=1, T_1=z,
    T_(m+1)T_(m-1)=zT_m^2+T_m T_m''-(T_m')^2.

With n=m+1, the exact bridge is

    T_m(z)=(-1)^f z^g F_(m+1)(-z^3).

Indeed the jth descending coefficient changes by (-1)^j when the differential parameter changes from -4 to1. Equivalently obtain the identity by scaling the recurrence and its seed; the coefficient formulas above give it term by term. Determinant comparisons for m2..7 independently reproduce it; these finite checks do not supply a general irreducibility argument.

Roffelsen, *Irrationality of the Roots ...*, SIGMA6(2010)095: complete11-page PDF retained; Section2 proof read. His Q_m=P_(m+1), without changing the -4 parameter. Lemma1 proves 4^j coefficient divisibility; his constant coefficient valuation and Theorem2 exclude nonzero rational roots of Q_m. This does **not** establish irreducibility of F_n: a rational F-root corresponds to t^3=4r, not necessarily rational t. Nor does raw irrationality exclude factors of degree>=2. His post-Theorem2 question is about the stronger raw polynomial after removing z; it must not be silently substituted for the normalized target. His reported Kametaka index is also not used to override the original source's indexing.

Roffelsen, *On the Number of Real Roots ...*, SIGMA8(2012)099: actual published9-page body retained, Theorems2–5 and initial proof read. It proves real-root counts/interlacing, not Galois transitivity or rational irreducibility. Its solved real-root conjecture is not a second candidate here.

The original target is a published1985 version, not a mutable arXiv claim. No later complete irreducibility resolution was located in the bounded metadata and primary-body screen; this is not worldwide or independent eligibility clearance. Taneda's directly requested PDF returned an Incapsula challenge, preserved as bytes, and was not bypassed. Its full body is unread. Subscription indexes and a systematic citation crawl were not available/performed.

## Sustained route: Newton polygons across primes

For a monic F of degree f with nonzero constant, let N_p be its lower Newton polygon on (i,v_p([X^i]F)). Each edge with horizontal length l and reduced slope denominator b contributes l/b copies of b to a multiset A_p. In a rational factorization, a factor degree belongs to the subset-sum set of A_p: over Q_p, roots of each valuation occur in packets with total degree divisible by b, by the Newton polygon factor theorem. Thus a necessary condition for a proper factor of degree k<=f/2 is membership in **every** such set.

The bounded exact experiment computes P_n by division in Z[t], checks zero remainder and normalization, constructs all lower hulls for primes p<2n+2, and intersects allowable factor degrees. In every n3..48 this intersection is empty. Each polygon's vertices, all allowable small degrees and final intersection are in newton.json. The hull is additionally checked against every finite coefficient valuation, with strictly increasing slopes and full degree width. These calculations can certify individual finite cases using the classical theorem; they are not a full-scope result and receive no discovery credit.

A particularly informative existing case is n20, degree63. The7-adic polygon permits k in {7,14,21,28}; the19-adic polygon permits {6,19,25}. Their intersection is already empty. The latter polygon has vertices (0,10),(6,9),(63,0), so it contributes one packet6 and three packets19. This illustrates how intersecting primes can succeed even though no single prime has an irreducible reduction. It is not a new source outcome.

**Precise missing bridge:** prove a formula or sufficient lower bounds for *every coefficient valuation*, uniformly in n and suitable primes, and then prove that the resulting allowable degree sets have empty intersection for every n>=3. The explicit constant-term formula only supplies one endpoint. The first few coefficient formulas do not locate every hull vertex. Neither a uniform prime-selection theorem nor a uniform factor-degree contradiction has been established here. Extrapolating the46 computed cases would be invalid.

## Strongest countercases to shortcuts; failed routes

1. Fixed modulus2 is inadequate: the actual F_7 reduction factors into degrees3 and4 (checks.json). This is a route obstruction, not a rational factorization of F_7. In fact its7-adic polygon already certifies irreducibility.
2. Kaneko–Ochiai Theorem3 gives T_(ap)(z)=z^((ap)(ap+1)/2) mod p for every p>3, a>=1. Via the normalization bridge, F_(ap+1)(X)=X^f mod p. Since f>=5 for p>=5, this reduction is reducible. Every fixed p>3 fails infinitely often; every fixed finite set of primes greater than3 fails simultaneously at n=1+their product. The exact statement leaves modulus2 outside this simultaneous obstruction. Modulus3 is also degenerate via their Remark14; it is not a uniform irreducibility certificate. Thirteen finite p/m controls reproduce the collapse.
3. Irrational raw roots do not imply irreducibility. For H(X)=(X^2+1)(X^2+2), the polynomial256H(t^3/4)=t^12+48t^6+512 has no real, hence no rational roots, yet has the displayed rational factorization. This is a countercase to the proposed implication, not to Kametaka.
4. Constant endpoints alone do not fix Newton slopes. In X^6+5X^3+125, the5-adic interior point(3,1) lies below the endpoint line from(0,3) to(6,0), changing the packet degrees. The all-coefficient estimates cannot be omitted.
5. The root relations in Roffelsen Section3 are invariant under Galois action on the *whole* root set. Restricting a sum to roots of a hypothetical rational factor discards cross terms; no closed subsystem or contradiction was derived. Simplicity, interlacing and the Schur determinant are not irreducibility theorems for this specialization.

## Bounded novelty/history and current registries

Before primary retrieval, the complete qualified original-role SUMMARY/discovery/PROOF/review/DECISION index union from r157/r159/r162/r164 was refreshed for9 changed/new records. The raw union had1680 records; r159's exact original/copy qualification excludes80 generated echoes; two additional r111 review-core snapshots have explicitly identified original counterparts and are also excluded, leaving1598 originals. All original r111–r113 scientific records remain. Exact DOI/title aliases and word-boundary Kametaka, later Roffelsen/Ochiai and Yablonskii/Vorobiev spelling aliases produced no matches. No old mathematical problem was relabelled fresh. There was no date/whole-lane cutoff. See history-receipt.json and alias-final.json; role exclusions have original counterpart evidence in the inherited qualification.

Fixed observed public heads are Omega d36a58e865e46580f127ef7a09d64ccbc2370296 and OpenAI4eaee87548250b2682affda7d05d947c05554bae. The user-supplied Omega1b21... to observed head delta has7 files. Existing complete tree snapshots, inherited later deltas, current first1000 Problems entries and current OpenAI CONTENTS were screened. Actual current pinned public bodies for the closest polynomial irreducibility and generalized Wronskian paths were fetched/read: dbonacci irreducibility is for X^q-sum X^i with one outside root; generalized Wronskian nonvanishing has no rational-factor conclusion. Their hypotheses/conclusions do not settle this target. No exact public counterpart was identified. No claim that two bodies or path absence clears the entire registry is made. Older aa026->a19a and a19a->490f300-path caps persist; first1000 Problems entries also leave a listing gap. Fixed scope, no endless head chase. No Lean/manuscript authorized by these partial checks.
