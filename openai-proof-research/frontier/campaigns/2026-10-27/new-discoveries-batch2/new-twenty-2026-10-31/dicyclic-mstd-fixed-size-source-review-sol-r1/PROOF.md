# Independent ordinary proof for 373070
Reconstructed personally from the literal and disclosed mechanism before opening FULLCANDIDATE or author ordinary routes. This is independent verification, not independent invention.

Fix an integer m >= 2. Put r=m-1 and K_m=max(3,2r+1,2^m). For each integer n>=K_m, work in Dic_(4n) with rotations a^t (t modulo 2n), nonrotations a^t b, and relations b^2=a^n, ba^t=a^(-t)b. The source normal forms give two disjoint cosets, each with unique exponents modulo 2n; in particular a has order 2n. Set R={a^i:1<=i<=r}, f_j=a^j b and A_j=R union {f_j}, for j modulo 2n. As r<n and n>2r, R has r distinct rotations and A_j has exactly m elements.

All products, including repeated entries and both mixed orders, are as follows:
R R={a^s:2<=s<=2r}; f_j f_j=a^n;
R f_j={a^(j+i)b:1<=i<=r}; f_j R={a^(j-i)b:1<=i<=r}.
Every integer in [2,2r] is a sum of two integers in [1,r]. This interval has 2r-1 distinct residues modulo 2n. The residue n is outside it, since 2r<n<2n. Each mixed interval has r distinct residues; a coincidence between j+i and j-k would force i+k=0 modulo 2n, whereas 2<=i+k<=2r<2n. Thus the mixed intervals are disjoint for every j, including intervals crossing the modular origin. Rotation/nonrotation disjointness now gives |A_j A_j|=(2r-1)+1+2r=4r.

For the source's right inverse convention A A^(-1), f_j^(-1)=a^(j+n)b: multiplication in either order with f_j gives a^(2n)=1. The four pair types give
R R^(-1)={a^s:-(r-1)<=s<=r-1}; f_j f_j^(-1)=1;
R f_j^(-1)={a^(j+n+i)b:1<=i<=r}; f_j R^(-1)={a^(j+i)b:1<=i<=r}.
Every integer in the first interval is a difference of two indices in [1,r]. Its length is 2r-1<2n, and it already contains 0, so the singleton identity contributes nothing new. Each mixed interval again has r elements. Equality between j+n+i and j+k modulo 2n would imply n+i-k=0 modulo 2n. But n-r+1<=n+i-k<=n+r-1, an interval strictly within (0,2n), so equality is impossible. Hence |A_j A_j^(-1)|=2r-1+2r=4r-1. This uses neither commutativity nor translation invariance.

Consequently every A_j is MSTD. Distinct j modulo 2n give distinct subsets because the unique nonrotation f_j determines j. Thus S_Dic_(4n)(m)>=2n; no exact count of all MSTD subsets is asserted. Since n>=2^m and m>=2, 2n>=2^(m+1)>2^(m/2) as real numbers. This proves the literal strict inequality for every fixed m and every sufficiently large integer n, of either parity. For r=1 the rotation intervals are the singleton {2} and {0}, and the same bounds/disjointness arguments apply without exception. K_m is a positive integer and already enforces n>=3. This solves Conjecture 6.2 in the supplied original scope, not the majority/proportion Conjecture 6.1.

Ordinary proof PASS is independent of literature novelty, source-final equivalence, significance, formalization, and campaign acceptance. No mathematical program or formal tool was used.

## Presentation and dependency bridge
The normal forms and order can also be checked without reading the cited external Lemma 2.6. On pairs (u,e) with u modulo2n and e in {0,1}, put (u,e)(v,f)=(u+(-1)^e v+n e f, e+f modulo2). This is associative: the signed v,w terms agree, and modulo2n the sign on n is immaterial; the remaining cocycle identity follows from e f+(e+f-2ef)g=f g+e(f+g-2fg). The identity is (0,0), and inverses exist: (-u,0) for (u,0), and (u+n,1) for (u,1). The generators (1,0),(0,1) satisfy the presentation, have the stated powers, and generate all4n distinct pairs. Conversely the presentation reduces every word to a^u b^e with 0<=u<2n and e=0,1 using ba=a^(-1)b and b^2=a^n. Therefore the presented group has exactly4n elements and the two unique normal-form cosets used above. This is a symbolic argument, not a program or enumeration. It derives all used group identities internally. Source Lemma1.3's external citation is not a missing dependency of this proof.

The primary PDF glyphs of Definition1.1 p1, multiplication and inverse-product definitions/presentation p2, Lemma1.3/normal forms p3, size-count notation p4, and Conjecture6.2 p18 were personally viewed. They agree with the literal used here. In particular the source uses a1 a2^(-1), permits a1=a2, and prints a^n=b^2, not b^2=1. Source header is9Feb2026. No assertion of final-version equivalence is made.
