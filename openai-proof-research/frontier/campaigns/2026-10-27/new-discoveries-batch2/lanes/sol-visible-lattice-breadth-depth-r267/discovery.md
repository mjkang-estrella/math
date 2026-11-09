# Full-scope visible-point investigation — unresolved

Target: Gabriel Khan, Mizan R. Khan, Joydip Saha, Peng Zhao, arXiv1909.01306v1, posted3 September2019, Conjecture11. Exact scope: positive integers 1<a<n-1, gcd(a,n)=1; P={t(1,0)+u(a,n):0<=t,u<=1}; V counts integer (x,k) in the strict interior with gcd(x,k)=1. Conjecture: n/2<V<3n/4. The displayed conjecture is on PDF page12; the r263 p11 locator points to its preceding discussion. No full proof or counterexample, and no PROOF.md.

## Model and exact identities

For each integer 1<=k<n, interior membership says ak/n<x<ak/n+1. Coprimality makes ak/n nonintegral, so the unique integer is x=ceil(ak/n). This independently proves Theorem4's model, including all boundary exclusions. Thus exactly n-1 points occur. No geometric approximation is involved.

Put A_d=#{interior points divisible in both coordinates by d}. Then A_1=n-1; A_d=0 for d>a. For d>=2, writing x=ds,k=dt gives

    A_d = sum_(s=1..floor(a/d)) [ floor(sn/a) - floor((ds-1)n/(ad)) ].

Indeed the inequalities become (ds-1)n/(ad)<t<sn/a. The upper endpoint is nonintegral: if a divides sn then a divides s, impossible since 0<s<a. Counting the integers gives the difference above, even when the lower endpoint is integral. Independently, setting r=nt_x-at with t_x=ceil(at/n) yields

    A_d = #{1<=t< n/d : 0 < d((-at) mod n) < n}.

For k=dt and x=ds, the condition is 0<ns-at<n/d; this interval contains at most one s. Its possible remainder is (-at) mod n. These formulas were checked against direct gcd counts. Möbius inversion gives the exact finite identity

    V = sum_(d=1..a) mu(d) A_d.

This is a usable global floor-sum formulation, not a solution. It is closely related to the source Theorem8 and earns no separate credit.

Boundary caution from actual-body screening: source equations9–11 introduce V+2 by counting the two primitive boundary points (1,0),(a,n), but the subsequent positive-k interval count omits (1,0). Its double sum equals V+1. For a2,n5 the column counts are2+2=4 whereas V=3. Consequently the literal phi/fractional-part formula derived from those positive-integer intervals needs -1/n rather than -2/n. This is a source boundary correction only, not a resolution or a nomination. Theorem7 agrees with the direct model. Proposition10 assumes both a and ceil(n/a) even, and bounds V by (3/4)a ceil(n/a), which may exceed3n/4; it cannot be substituted for the requested strict full upper bound.

## Mechanism1: inversion and complement symmetries

For b=a^-1 modulo n choose integer c with ab+cn=1. The integer matrix with columns (b,n),(c,-a) has determinant-1 and exchanges the two spanning vectors with (b,n),(1,0). It preserves gcd and interior membership; hence V(a,n)=V(b,n), exactly Proposition3's body proof. It is a true symmetry but gives no descent in n. In particular n=8t,a=4t-1 has gcd1 and a²=1 modulo n, so inversion fixes an infinite family with a/n tending1/2. It does not reduce all inputs to the source's fixed-a or sublinear-a asymptotic regime.

Reflection about the center sends p to C-p with C=(a+1,n). It cannot inject nonprimitive points into primitive ones. At a5,n14, p=(2,4) and C-p=(4,10) are distinct interior points and both have gcd2. The smaller a3,n8 case even has a nonprimitive fixed point (2,4). Complementing a to n-a also gives no rowwise primitive-cover argument: at a5,n13,k6 the two x values are3 and4, both noncoprime to6. These are failures of the mechanisms, not counterexamples to Conjecture11.

## Mechanism2: primitive rays and strict-surplus charging

Each interior point p has a primitive root q=p/gcd(p), also interior, because both spanning coordinates shrink while remaining strictly positive. For primitive q=(x,k), define r=nx-ak, so 0<r<n. Its interior multiples are precisely j=1,...,M(q), where

    M(q)=floor((n-1)/max(k,r)).

This follows from j k<n and j r<n, with both positive integers. Distinct primitive q give disjoint rays. Consequently

    n-1=sum_q M(q),  V=#q,
    B:=n-1-V=sum_q(M(q)-1).

Same-ray charging cannot give an injection of all nonprimitive points: a3,n7 has primitive q=(1,2) and two nonprimitive multiples (2,4),(3,6). In the known a=n-2 odd family the diagonal ray has order n/2 multiples, while other rays supply the compensating visible points. A successful argument must charge across rays, rather than bound each ray individually. The source Theorem2's proof supplies only two distinct rays away from the degenerate slopes, far short of this control.

**Missing universal ray lemma:** for every clean P above excluding a1,n-1,

    floor(n/4) <= sum_q(M(q)-1) <= floor((n-3)/2).

The two integer bounds are exactly sufficient for the two strict conjectured inequalities. No cross-ray injection, strict-surplus decomposition, or lattice fan identity establishing them has been obtained. This identifies the unresolved global step explicitly; it is not presented as a proved lemma.

## Mechanism3: parity, Möbius sums, and sustained obstruction analysis

Counting only even-even points would prove the upper bound if A_2>=floor(n/4). It fails systematically, not just sporadically: for a3,n=6m+2, m>=1, the column x2 contains k=2m+1,...,4m+1, hence A_2=m. This is below floor(n/4) for every m>=1 (already m1 gives1<2). The x3 column contributes A_3=2m-floor((4m+1)/3), with A_6=0. Therefore, by disjoint prime obstructions,

    V(3,6m+2)=3m+1+floor((4m+1)/3).

This exact infinite-family calculation shows why adding odd-prime charging repairs this particular obstruction while parity alone fails by a linear amount. It is not a replacement of the full quantifiers with fixed slope3. We pursued the resulting **full** Möbius sum above; its signed prime-overlap/discrepancy terms remain uncontrolled uniformly over a,n.

There is no valid universal substitution A_d≈n/d² with a small uniform error. For a=n-2 and odd n, the diagonal ray alone gives A_d>=floor((n-1)/(2d)) for all d in range. Already d3 has a linear excess over n/9. Nor can absolute divisor-error bounds in Theorem8 prove strict linear margins when a is comparable to n: the crude O(a log a) error is not o(n). Inversion's central fixed family prevents converting that fact into uniform applicability of Corollary9. A required uniform *signed* floor-discrepancy bound, including thin rational slopes and their inverse classes, is the analytic alternative to the missing ray lemma. Neither equidistribution nor average density supplies it.

## Validation and status

Exact model/symmetry scan:36,632 admissible pairs, n<=350, no conjecture violations. Independent column/Möbius/residue checks n<=75, floor/ray checks n<=90, and infinite-family diagnostics m<=200 pass. The universal formulas and obstruction arguments above are proofs; finite checking supplies no proof of the conjecture. Grid review is separate and receives zero credit. Classical adaptation remains a strong objection to any future proof based only on these standard identities; source Theorems3,4,7,8 already supply most of the scaffolding. Current external prior-art clearance is incomplete.
