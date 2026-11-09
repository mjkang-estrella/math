# Universal closure of the support 3a=2d

Scope: a>=12, a<b<d<2a, gcd(a,b,d)=1, and 3a=2d. Write a=2s,d=3s,b=2s+e, with s>=6, 1<=e<s, gcd(s,b)=1. Then <a,b,d> is a 3-permutation semigroup if and only if

* e=2, s=6q+1, q>=1 (H8,q), or
* e=1, s=3q+2, q>=2 (H11,q).

This is a restricted ordinary theorem, uncredited and subject to independent review. It does not resolve full Conjecture5.1.

## Exact gluing, gaps, Apéry and ranks

Let C=<2,3>=N\{1}. Every integer n has a unique expression n=jb+sz, 0<=j<s, z integer. Membership in G is equivalent to z in C. For any representation by the three generators the b coefficient is j+ls with l>=0; replacing ls copies adds lb to z. Since b>=13 belongs to C, this proves necessity; sufficiency is immediate. Thus F=(s-1)b+s. The COMPLETE positive gaps are

    F-ib-sh >0, 0<=i<s, h in {0,2,3,4,...}.

Indeed on a ray the missing z values are1, -1,-2,..., and reflection changes z to1-h. The Apéry set modulo2s consists of jb and jb+3s for 0<=j<s, since {0,3} is Ap(C,2). Distinctness modulo2s and minimality follow by first reducing modulo s, then modulo2. Its maximum gives the same F.

For n>=0 its positive membership count is

    R(n)=sum(j=0..s-1) N(floor((n-jb)/s))-1,
    N(z)=0 (z<0), N(z)=z+1-1[z>=1] (z>=0).

All boundary witnesses below use this exact rank, never an unaligned selection of residues.

## Isolated boundary mechanism

If h is a gap and h-2,h-1,h+1,h+2 are positive members, let r=R(h-1). If r=1 modulo3, (h-1,h+1,h+2) starts at rank r and repeats a residue. If r=2 modulo3, (h-2,h-1,h+1) starts at rank r-1 and repeats a residue. Therefore every such boundary in a 3-permutation semigroup has r=0 modulo3. For two boundaries the rank difference equals the exact member count in the intervening half-open interval.

## Initial residues and lower edge strips

The first three positive members are 2s,b,3s since d<2a. Their distinct residues require s!=0 modulo3 and b=s modulo3, hence e=-s modulo3. For e=1 this gives s=2 modulo3 and s=3q+2 with q>=2. For e=2 it gives s=1 modulo3; primitivity forces s odd, hence s=6q+1 with q>=1. The source identifications are exact, and source sufficiency follows from frozen Ugolini arXiv1609.01133v2 Lemmas4.8(2,4),4.11(2,4), whose actual statements were read. No numerical extrapolation supplies sufficiency.

## Interior e>=3 and f=s-e>=3

The reflected offsets through4s are EXACTLY 0,2s,b,3s,4s. For i>=2 the offset is at least2b>4s; for i=1 its next allowable h is2, giving b+2s>4s; the i=0 list is immediate. The next offset after4s has distance at least min(e,s)>=3. Consequently F,F-2s,F-3s,F-4s are isolated boundaries with two members on either side: the successive displayed distances are2s,e,f,s. Positivity follows from F-4s-2 >= (s-1)(2s+1)-3s-2 =2s^2-4s-3>0 for s>=6.

Between F-2s and F there are2s-1 members, forcing 2s=1 modulo3. Between F-4s and F-3s there are s-1 members, forcing s=1 modulo3. These are inconsistent. At least one of the four ranks is nonzero modulo3; the boundary mechanism explicitly returns a failed successive aligned triple. This proves universal exclusion of the entire interior.

## Upper edge strips f=1 or2

Assume initial residues are distinct, otherwise they already witness failure. Since e=s-f=-s modulo3, we have 2s=f modulo3. When f=1, s=2 modulo3 and s>=8; when f=2, s=1 modulo3 and gcd(s,f)=1 implies s>=7. In both cases s>3f.

Write each sum as cs-jf, with j the b coefficient and c-3j in <2,3>. All sums in increasing order through rank12 are

    2s; 3s-f,3s; 4s; 5s-f,5s;
    6s-2f,6s-f,6s; 7s-f,7s; 8s-2f.

This list is exhaustive: c=0..8 and 0<=j<=floor(c/3) can be inspected using c-3j!=1; the inequalities s>3f order these layers strictly. For c>=9, cs-jf >= c(s-f/3) >=9s-3f>8s-2f. The rank10 triple is therefore exactly (7s-f,7s,8s-2f). Its last two entries have residue difference s-2f=0 modulo3 because 2s=f modulo3. It fails universally. This completes all outside cases.

## All source intersections and first residual

check.py independently transcribes all16 page2 generator formulas and solves each support equation over exact rational source parameters. checks.json records64 rows:32 old exclusions and16 for EACH new target, including persistent and isolated intersections, source domains and retained-domain checks. There are no retained isolated exceptions to the two persistent families on either new support. H1 and H10 are the persistent intersections of 3a=b+d; H8 and H11 are those of 3a=2d. H11 requires q>=2 after a>=12. This table must be consulted before any use of a guessed survivor list.

For 3a=b+d write b=a+t,d=2a-t, 0<t<a/2,gcd(a,t)=1. Cancelling mixed b,d replaces them by3a. Thus the exact Apéry formula is A[jt mod a]=min(j(a+t),(a-j)(2a-t)), 0<=j<a. A pure coefficient can always be reduced modulo a, which strictly reduces its value. Membership is n>=A[n mod a], rank is sum over residues of max(0,1+floor((n-A[r])/a))-1, and F=max A-a. These give a complete exact diagnostic for every parameter. The switch index is floor((2a-t)/3). They do NOT yet prove that every t>=3 fails, nor exclude wrong residue classes for t=1,2 without using the initial triple.

Precise unresolved obligation: universally, for all a>=12, 3<=t<a/2, gcd(a,t)=1, construct a successive rank1-mod3 failed triple (or produce an outside-family counterexample). The finite checks here through a=120 are evidence only. Also still open here:2a+2b=3d,3a+b=3d,4a+b=3d. No full PROOF is claimed.
