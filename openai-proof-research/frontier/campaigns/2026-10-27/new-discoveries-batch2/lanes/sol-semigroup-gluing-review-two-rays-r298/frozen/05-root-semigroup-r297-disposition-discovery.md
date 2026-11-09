# Two empty supports: universal ordinary proofs

For every integer triple a>=12, a<b<d<2a, gcd(a,b,d)=1, neither 4a=3b nor 4a=3d can generate a 3-permutation semigroup in Ugolini Definition 1.1. These proofs cover the entire supports, hence also all r294 retained strata and vertices. They do not rely on a bounded scan or on completeness of the r294 arrangement. They are restricted, uncredited progress; root alone may adopt them. No full classification or novelty claim follows.

## Common exact gap structure

Let C=<3,4>={0,3,4} union [6,infinity), k>=4, gcd(k,m)=1, m>=3k+1. Consider G=<3k,4k,m>. Every integer n has a unique representation n=jm+kz with 0<=j<k, z an integer. It belongs to G iff z belongs to C. Indeed any nonnegative representation has m-coefficient j+lk, l>=0, and thus z is in C+lm, a subset of C because m>=13 belongs to C. Conversely z in C gives the required representation.

The largest gap on the ray j is jm+5k. Consequently F=(k-1)m+5k, and the COMPLETE positive gaps reflected about F have offsets

    i*m+k*h, 0<=i<k, h in {0,3,4} union {6,7,8,...},

retaining only F-offset>0. This includes all negative z and all exceptional z=1,2,5, so it omits no lower gap. It also proves conductor F+1. A conventional Apéry table modulo 3k is obtained by taking, for each 0<=j<k, the three values jm+k*c with c=0,4,8. Their residues are distinct: j is fixed modulo k, then c runs through all residues modulo3. These are minimal because subtracting 3k would require c-3 in C, which fails for 0,4,8. Its maximum is (k-1)m+8k, again giving F.

For n>=0 define

    R(n)=sum_{j=0}^{k-1} N(floor((n-j*m)/k))-1,
    N(z)=0 if z<0, otherwise z+1-1[z>=1]-1[z>=2]-1[z>=5].

This counts positive members <=n exactly. Thus R(n) is their one-based rank when n belongs to G.

## Boundary lemma, explicit aligned triples

If h is a positive gap and h-2,h-1,h+1,h+2 are positive members, put r=R(h-1). If r=1 mod3, the consecutive positive members (h-1,h+1,h+2) start at rank r and repeat a residue. If r=2 mod3, (h-2,h-1,h+1) start at rank r-1=1 mod3 and repeat a residue. Thus a 3-permutation semigroup requires R(h-1)=0 mod3. This gives constructive failed successive aligned triples, not merely selected bad residue triples.

For two isolated gaps h'<h the rank difference R(h-1)-R(h'-1) is the number of positive members in [h',h). We will count this interval exactly, including its lower gap.

## Support 4a=3b

Put a=3k,b=4k,d=m, so 4k<m<6k, k>=4 and gcd(k,m)=1. The top reflected offsets through 4k are exactly 0,3k,4k; the next possible offset m exceeds 4k. Therefore the gaps F and F-3k each have two consecutive positive members on BOTH sides: the neighboring distances are at least k>=4, and above F all integers are members. Positivity F-3k-2>0 follows already from k>=4,m>=4k+1.

There are no gaps strictly between F-3k and F. The rank difference is 3k-1=2 mod3. It cannot be zero at both boundaries. The boundary lemma explicitly supplies a failed triple in [F-3k-2,F+2]. This excludes every primitive pair, independent of its initial residues.

## Support 4a=3d

Put a=3k,d=4k,b=m, so 3k<m<4k and gcd(k,m)=1. The top reflected offsets through 4k are EXACTLY 0,3k,m,4k: any i>=2 contributes >=2m>6k, while the next h is6. Initial generators are the first three positives, since d<2a. If their residues repeat, they are already a failed triple at rank1. Otherwise k and m are nonzero modulo3 and opposite to each other.

If e=m-3k>=3, F and F-3k are isolated gaps with two positive integers on each side. There is no gap strictly between them and the same difference 3k-1 excludes the pair.

It remains e=1 or2. We use F and F-4k instead, whose intervening gaps are exactly F-3k and F-m. The upper neighboring distance of F-4k is k-e; its lower neighboring distance is at least2k, as the next offset is6k (m+3k>6k,2m>6k). For e=1, k-e>=3. For e=2, primitivity forces k odd; since k>=4 this gives k>=5, again k-e>=3. Both boundaries are isolated and positive. The interval [F-4k,F) has length4k and exactly three gaps, hence its positive count is 4k-3=k mod3. Initial distinctness gave k!=0 mod3, a contradiction. This covers both endcases, including their primitivity exclusions, without assuming the internal gaps are isolated. The resulting failed triple lies in [F-4k-2,F+2].

check.py:construct computes R, chooses these two boundaries, and returns the explicit failed triple with its starting rank. Its exact construction is universally justified above. Independent Boolean DP checks its successiveness and rank on 1,792 pairs on the first support and 896 on the second, including all primitive pairs with 4<=k<=54. These regressions support the implementation; the proof has no k bound.

## All source intersections

All sixteen generator formulas were transcribed directly from the frozen Ugolini page2 table. For each support substitution gives an affine equation C*q+D=0 in the SOURCE parameter q. checks.json records all32 equations, exact rational roots, integer/parameter-domain tests and resulting triples. No equation vanishes identically, and none has a retained primitive triple with a>=12. The complete root table is in intersections.md. Thus there are no source exceptions, persistent or isolated, to dispose of in the retained domain. This computation is separate from the exclusion proof, which rules out every pair directly.

## Next support investigated: 3a=b+d

Write b=a+t,d=2a-t, 0<t<a/2, gcd(a,t)=1. Cancelling a mixed copy of b and d replaces it by3a. Therefore an Apéry-minimal element uses only b or only d (and no a). In residue jt modulo a, 0<=j<a, the exact minimum is

    A[jt mod a]=min(j*(a+t),(a-j)*(2a-t)),

with j=0 interpreted as0. Further pure coefficients differ by multiples of a and increase strictly. This gives conductor, membership and ranks without a growing horizon. It is a universal reduction, not a closure: a failed aligned successive triple outside all sixteen families still needs proof. No disposition is claimed for this or the four other residual supports.

Five remain: 2a+2b=3d; 3a=b+d; 3a=2d; 3a+b=3d; 4a+b=3d. The AP support retains its earlier independent review; no redundant full AP replay was performed. Counts remain9/39/next40.
