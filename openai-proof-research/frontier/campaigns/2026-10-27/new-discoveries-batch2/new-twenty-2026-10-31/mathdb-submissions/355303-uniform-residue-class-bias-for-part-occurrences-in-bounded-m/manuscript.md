# Uniform occurrence bias in partitions with bounded multiplicities

## Abstract

For partitions in which every part occurs fewer than k times, let D_k(r,t;n) count all occurrences of parts in residue class r modulo t. We give an exact coefficient proof of the two assertions of Jackson and Otgonbayar's Conjecture1.4: D_k(r,t;n)>=D_k(s,t;n) for k>=3,t>=6,1<=r<s<=t,n>=1, and strict inequality for k>=2 and n>max(t+3,16). The proof combines a positive paired-multiplicity polynomial, disjoint geometric chains, explicit strict-support constructions and an exact finite certificate. Four exceptional adjacent comparisons for distinct partitions are handled by minimum-part injections on unrestricted odd-part residual partitions. The accompanying unchanged Lean sources have passed a complete independent fresh replay; this manuscript is a new exposition requiring a separate manuscript review. Worldwide priority is not certified.

<a id="s1"></a>
## 1. Statement, conventions and source binding

Let P_k(n) be the partitions of n with each positive part occurring strictly fewer than k times. The empty partition is permitted when n=0. Define

    C_k(a;n) = sum_{lambda in P_k(n)} multiplicity_lambda(a),
    D_k(r,t;n) = sum_{lambda in P_k(n)} #{occurrences x in lambda : x mod t = r mod t}.

An occurrence is counted with its multiplicity. In particular, two copies of a part contribute two, and representative t denotes residue0. The term k-regular follows the cited source's bounded-multiplicity convention. It does not mean exclusion of parts divisible by k.

**Theorem.** For integers t>=6 and 1<=r<s<=t:

1. If k>=3 and n>=1, then D_k(r,t;n)>=D_k(s,t;n).
2. If k>=2 and n>max(t+3,16), then D_k(r,t;n)>D_k(s,t;n).

These are exactly the two clauses of [JO22, Conjecture1.4, p5]. The source abstract on p1 explicitly defines regularity by multiplicity<k. Both pages were freshly rendered from the owned source PDF and visually checked for this manuscript. The retained MathDB355303 target-only record points to the same paper and states these quantifiers. Its1916-byte projection has SHA256 `04a58a2d43009ac953efcc52e68f6f054ab6adda253c3f07e20e0f09961c0a0c`; it is a retained snapshot, not a live MathDB access or current open-status assertion. The definition in `RBCountDefs` and the fully expanded theorems `RB355303.original_weak`/`original_strict` use literal Mathlib `Nat.Partition.countRestricted` and multiset occurrence counts with these same conventions. An independent final replay checked that binding. No changed normalization, repaired domain, or finite-parameter substitute is used.

<a id="s2"></a>
## 2. Exact generating functions

We work in Z[[q]]. Coefficients of negative degree are zero. All infinite products below are coefficientwise: degree n depends only on factors with positive sizes<=n, so no analytic convergence is involved. Put

    B_h = 1+q^h+...+q^((k-1)h),
    A_h = sum_{0<=i<k} i q^(ih),
    P = product_{h>=1} B_h,       g_c = 1/(1-q^c).

Selecting the multiplicity i_h of each size h gives a weight-preserving bijection from tuples 0<=i_h<k, sum h i_h=n, to P_k(n). Thus the unmarked series is P and

    C_k(a;q) := sum_n C_k(a;n)q^n = A_a product_{h!=a}B_h.             (2.1)

The coefficient i in A_a retains the multiplicity mark. This is an enumeration argument on the actual partition multisets, not a transport of a statistic through the unmarked Glaisher bijection.

Pair i copies of a and j copies of a+1 with the reversed multiplicities. For i>j their contribution to A_a B_(a+1)-A_(a+1) B_a is

    (i-j)q^((i+j)a+j)(1-q^(i-j)).

Consequently

    F_(k,a) = sum_{0<=j<i<k} (i-j)q^((i+j)a+j) sum_{0<=e<i-j}q^e,
    A_a B_(a+1)-A_(a+1)B_a = (1-q)F_(k,a),
    C_k(a;q)-C_k(a+1;q) = (1-q)F_(k,a) product_{h notin{a,a+1}}B_h. (2.2)

F has nonnegative integer coefficients and contains q^a with positive coefficient, from i=1,j=0. This is the common source of strictness. The only signed factor in (2.2) is initially1-q.

<a id="s3"></a>
## 3. Disjoint chains and coefficient support

Call c a primitive k-root when c>=1 and k does not divide c. Each positive integer belongs to exactly one chain c,kc,k²c,... with primitive c: repeatedly divide by k while possible. Distinct primitive chains are disjoint. Finite telescoping gives

    product_{j=0..J} B_(c k^j) = (1-q^(c k^(J+1)))/(1-q^c),

and hence the full chain contributes g_c. If one element x=c k^v is removed, the remaining chain contributes

    g_c (1-q^x)/(1-q^(kx)).                                      (3.1)

These are identities degree by degree, obtained from finite products before taking any stabilized coefficient. Selected chains must avoid both marked sizes in(2.2); selected isolated factors must be distinct and outside all selected chains. After extracting them the complementary product has nonnegative coefficients and constant coefficient1. Thus a nonnegative extracted kernel positive at degree n gives a positive coefficient of the whole difference at degree n. One may also ignore a remaining nonnegative factor of constant coefficient1 when proving a lower bound.

For L=pu+qv with u,v>=0 and p,q>=1, the elementary coin identity is

    (1-q^L)g_p g_q
       = (sum_{i=0..u-1}q^(pi))g_q
           + q^(pu)(sum_{j=0..v-1}q^(qj))g_p.                    (3.2)

Here the q in the subscript q is an integer denomination; the formal variable is unchanged. The identity follows by splitting1-q^(pu+qv) into (1-q^(pu))+q^(pu)(1-q^(qv)). Its coefficients are nonnegative. In particular it is positive at pi+qj whenever0<=i<u,j>=0. An additional g_c permits any further increment c l. The notation in later constructions is therefore:

    x=pu+qv,       n-a=pi+qj+c l,       0<=i<u, j,l>=0.           (3.3)

When c is absent omit c l. Extract the punctured root1 chain, whose missing element is x=k^w in{a,a+1}, and the intact primitive p,q,c chains. Formula(3.1) cancels1-q in(2.2), leaving

    F_(k,a)(1-q^x)g_p g_q [g_c] g_(kx)                           (3.4)

times a nonnegative complementary factor. Hence(3.3) proves positivity; g_(kx) may be left at degree0. Every use below verifies that p,q,c are distinct, primitive, different from1, and avoid the other marked size. Previous elements of the root1 chain lie below a, because k^(w-1)<a in all cases used.

If p,q are coprime positive integers, every m>=(p-1)(q-1) is pi+qj for0<=i<q,j>=0: choose i with pi=m mod q; the bound forces the resulting multiple m-pi of q to be nonnegative. This supplies conductors24 for pairs in{2,3,5,7} and120 for pairs in{3,5,7,11,13}.

We will also use a short-window proof: if every integer in[m0,m0+q-1] has form pi+qj+c l with i<I, then adding q proves the same assertion for every m>=m0. The following explicit windows are all that occur in the exceptional cases. The entries list (i,j,l) for consecutive m starting at m0.

| (p,I,q,c,m0) | Window witnesses |
|---|---|
| (5,3,3,7,5) | (1,0,0),(0,2,0),(0,0,1) |
| (5,3,2,2,5) | (1,0,0),(0,3,0) |
| (2,3,3,3,5) | (1,1,0),(0,2,0),(2,1,0) |
| (5,1,3,11,24) | (0,8,0),(0,1,2),(0,5,1) |
| (2,1,5,7,24) | (0,2,2),(0,5,0),(0,1,3),(0,4,1),(0,0,4) |

For (p,I,q,c,m0)=(2,1,3,c,24), c in{5,7,11,13}, take i=0. The witnesses (j,l) at m=24,25,26 are respectively:

    c=5:  (8,0),(5,2),(7,1);
    c=7:  (8,0),(6,1),(4,2);
    c=11: (8,0),(1,2),(5,1);
    c=13: (8,0),(4,1),(0,2).

In the second and third table rows, c=q merely repeats the same geometric increment; it does not require extracting another chain. The two multiples of q combine.

These tables are explicit constructive arithmetic, not assumed eventual support.

<a id="s4"></a>
## 4. Weak adjacent comparisons

We first prove C_k(a;n)>=C_k(a+1;n) for every k>=3,a>=1,n>=0, and the same assertion for k=2,a>=5. If n<a+1 the right count is0. Otherwise use(2.2).

For a>=2 with neither a nor a+1 a positive k-power, the full primitive root1 chain is intact and contributes g_1. It cancels1-q, leaving F times nonnegative factors. The qualification a>=2 is essential: at a=1 the marked size1 itself lies in the root1 chain, even though1 is not a positive power k^w with w>=1. The case a=1 is treated explicitly below.

If x=k^w is one marked size and k>=4,a>=2, extract the punctured root1 chain and roots2,3. They are primitive. The other marked size is not divisible by k, so it meets either such chain only if it is its initial root. The only obstruction is k=4,a=3,x=4, where3 is marked. Outside that case x>=4 has a representation2u+3v: take (u,v)=(x/2,0) for evenx, or((x-3)/2,1) for oddx. Equations(3.2),(3.4) prove nonnegativity. In the obstructed case use root2 alone: (1-q^4)g_2=1+q² is nonnegative, and all other factors are nonnegative.

For k=3 write F=F_(3,a)=q^a+2q^(2a)+2q^(2a+1)+q^(3a+1). If x=a=3^w, a is odd and>=3. The numerator G=(1-q^a)F, after division by1-q², is nonnegative by grouping

    G=(q^a-q^(3a))+(q^(2a)-q^(3a+1))
          +(q^(2a+1)-q^(3a))+(q^(2a+1)-q^(4a+1)).               (4.1)

Each pair has equal parity, nonnegative exponent difference, and lower exponent first. If x=a+1=3^w and a>=8 is even, use

    (1-q^(a+1))F=(q^a-q^(3a+2))+(q^(2a)-q^(3a+2))
                     +(q^(2a)-q^(4a+2))+(q^(2a+1)-q^(3a+1)). (4.2)

The intact primitive root2 chain supplies the division by1-q². At the remaining a=2,x=3, root2 is marked. Instead extract roots4,5,7. Direct multiplication gives

    (1-q³)F_(3,2)g_4 g_5 g_7
       =q²g_4g_7+2q⁴g_5g_7+q⁵g_4g_7,                         (4.3)

which is nonnegative. The punctured root1 chain also leaves g_9, a nonnegative factor.

For a=1 set H_k=q sum_{j=0..k-1}q^(2j)-kq^k. The finite marked-factor identity is

    C_k(1;q)-C_k(2;q)=P H_k/(1-q^(2k)).                         (4.4)

For oddk>=3,

    H_k=sum_{d=2,4,...,k-1} q^(k-d)(1-q^d)^2,

and for evenk>=4,

    H_k=q^(k-4)H_4+sum_{d=5,7,...,k-1}q^(k-d)(1-q^d)^2.

Let D=(1-q)(1-q²)(1-q³). For even d, cancel one1-q^d against1-q² and apply(3.2) to the remaining1-q^d with denominations1,3. For odd d>=3, cancel one factor against1-q and apply(3.2) with denominations2,3. Thus(1-q^d)^2/D is nonnegative. Moreover

    H_4(1-q^6)=D Q_4,
    Q_4=q+q²+3q³+3q⁵+q⁶+q⁷.                                  (4.5)

For k>=4 the full P contains the distinct primitive chains1,2,3, so(4.4)-(4.5) prove nonnegativity. For k=3 the unmarked root1 tail starting3 and the roots4,5, with(2.2), give the explicitly nonnegative kernel(q+q²)g_4g_5. This avoids treating3 as a primitive root disjoint from1.

Finally take k=2,a>=5 with a marked power x=2^w. Then x>=8 and roots3,5 are intact. Every x>=8 lies in the semigroup<3,5>: for x mod3 equal0,1,2 use v=0,2,1 and u=(x-5v)/3. These u are nonnegative (the first eligible value with remainder1 is10). Equation(3.2) proves the weak inequality. The four pairs a=1,2,3,4 are not asserted weak at every n; their negative initial terms are retained and handled in Section6.

<a id="s5"></a>
## 5. Five uniform strict-support regions

We prove strict adjacent comparison throughout the five regions below. Every construction uses the same C_k and F_(k,a), so no comparison of an unrelated rational surrogate is substituted for the marked count. Sections5A-5E together leave only the finite box of Section7 and the low binary pairs of Section6.

<a id="s5a"></a>
### 5A. All k>=2, a>=24, n>=a+5

First suppose neither marked size is a positive k-power, and put m=n-a. If5<=m<=23 and m is not a k-power, the single unused factor B_m supplies q^m, since m<a and m is outside the root1 chain. If m=k^v and k>=3, instead use the two distinct factors B_2 and B_(m-2). Neither size is divisible by k, hence neither is a positive k-power; both are positive, distinct and<a. For k=2 the only powers in[5,23] are8 and16, represented instead by3+5 and3+13. In each case these unmarked isolated factors multiply the positive q^a term of F, giving a positive q^n term after root1 cancellation. Each used factor is different from the marks and from every other factor.

For m>=24 select two intact chains with roots among{2,3,5,7}. To justify selection, start with{1,2,3,5,7}. At most one member is divisible by k. Among the remaining primitive members at most one chain can hit either marked size: a marked size here is>=24>7, so a hit has positive exponent and implies k divides that mark; k cannot divide two consecutive marks, and uniqueness of primitive roots excludes two roots for the same mark. Excluding1 removes at most one further member. At least two roots remain. Their conductor is at most24, so m=pi+qj and F g_p g_q has positive q^(a+m) coefficient. All complements are nonnegative.

Now let x=k^w be a marked size; necessarilyw>=1 and x>=24. Use the punctured-chain kernel(3.4).

* If k=2 then x>=32. Choose(p,q,c)=(5,3,7), v=(2x) mod5 and u=(x-3v)/5. We have x=5u+3v, 0<=v<=4 and u>=3. The first window of Section3 represents every m>=5 with i<3<=u. The roots3,5,7 are primitive, distinct, and smaller than the other marked size>=31, hence intact.
* If k=3 then x>=27 is odd. Choose(p,q)=(5,2), u=3, v=(x-15)/2. Thus x=15+2v and u=3. The second window, with c=2, represents every m>=5. Repeating q as the incrementc simply combines its two nonnegative multiples; only the two disjoint roots5,2 are extracted. Both are intact.
* If k>=4 choose(p,q)=(2,3). For evenx put(u,v)=(x/2,0); for oddx put((x-3)/2,1). Hereu>=3. The third window represents all m>=5 with i<3, using c=3 only as a second multiple of q. Again only the two roots2,3 are extracted; both are intact.

In all three cases the preceding root1 element x/k is below a, the other marked size is not in any selected chain, and (3.3)-(3.4) give strictness at every n>=a+5.

<a id="s5b"></a>
### 5B. a=1, k>=3, n>=17

Extract the root1 tail starting at k, which avoids1 and2. Its product is g_k. Equation(2.2) becomes

    (1-q)F_(k,1)g_k = H_k g_1 g_2.                              (5.1)

At k=3 extract also primitive roots4,5. Since

    H_3=(q+q²)(1-q)(1-q²),

the resulting nonnegative kernel is(q+q²)g_4g_5. Every n>=17 has n-1>=16>=(4-1)(5-1), so its q g_4g_5 term alone is positive.

At k=4 extract root3 and the isolated factor B_5=1+q⁵+q^10+q^15; these are disjoint from the tail4,16,... and the marks. By(4.5) the kernel is Q_4 g_6 B_5. Decompose

    Q_4=q(1+q+q²)+q⁵(1+q)+(2q³+2q⁵+q⁷).

Every term is nonnegative. For n=17,...,22, respectively choose exponents in the first two summands as

    17=5+6*2, 18=5+1+6*2, 19=1+6*3,
    20=1+1+6*3, 21=1+2+6*3, 22=5+6*2+5.

The exponent of B_5 is either0 or5, within its allowed range. Adding6 preserves these choices, proving positivity for every n>=17.

For oddk>=5 write k=2s+3,s>=1. Extract root3 in addition to the root1 tail. The recursion H_k=q²H_(k-2)+q(1-q^(k-1))² gives a sum of two nonnegative kernels:

    q² H_(k-2)g_1g_2g_3
       + q B_(k-1)(size1) B_((k-1)/2)(size2) g_3.               (5.2)

Here B_M(sizeh)=sum_{i=0..M-1}q^(hi); the letterM denotes the finite range, not the original multiplicity parameter. The first summand is nonnegative by the odd square decomposition of Section4. In the second, take exponent i=(n-1) mod3 from B_(k-1)(size1), exponent0 from the other finite factor, and3 floor((n-1)/3) from g_3. Because i<=2<k-1 this is allowed, giving a positive coefficient.

For evenk>=6 write k=2t+6,t>=0. The same recursion gives

    q² H_(k-2)g_1g_2g_3
       +q B_(k-1)(size1)(1-q^(k-1))g_2g_3.                    (5.3)

The first term is nonnegative by(4.5) and the even recursion. Since k-1=2(t+1)+3, the second term is nonnegative by(3.2) with u=t+1>=1,v=1. Choose the same i=(n-1) mod3 in the finite factor and the supported coin term 2*0+3 floor((n-1)/3). This proves strictness. Thus everyk>=3, including the small bases3,4, is covered without cancelling a nonexistent unmarked part1.

<a id="s5c"></a>
### 5C. k=3 with a or a+1 a positive3-power

For a>=24 Section5A applies, and a=1 is already Section5B. The only remaining positive-power pairs are a=2,3,8,9; this follows from3^1=3,3^2=9,3^3=27.

For a=2 use the explicit nonnegative kernel(4.3). At n=17,18,19,20 its first/last terms supply respectively

    17=5+4*3, 18=2+4*4, 19=5+7*2, 20=2+4+7*2.

Adding4 proves positive support for all n>=17; no use of the middle2q⁴g_5g_7 term is needed.

For a=3 extract the punctured root1 chain and roots2,5. Direct polynomial cancellation gives

    (1-q³)F_(3,3)g_2g_5
      = q⁵(1+q+q²+q³+q⁴)g_5+(q³+2q⁷+q^11)g_5.               (5.4)

The first term is positive in every degree n>=5 by n=5+((n-5) mod5)+5 floor((n-5)/5), so in particular every n>=17.

For a=8 or9 put x=9 and use(p,q,c)=(5,2,7),u=1,v=2. Thus x=5+2*2. The selected roots5,2,7 are primitive and avoid8,9 or9,10. If m=n-a is even write m=2j. If odd write m=2j+7; for n>=17 its least possible odd value is9, so j>=1. Taking i=0<u in(3.3) proves positivity. This completes the entire k=3 exceptional region with threshold n>=max(a+5,17).

<a id="s5d"></a>
### 5D. Nonexceptional a>=2, any k>=2, n>=a+120

Cancel root1 as in Section4. From the five primes{3,5,7,11,13}, at most one is divisible byk; the chain of each marked size removes at most one further primitive root. Therefore at least two distinct primitive roots p,q remain, and neither chain meets a mark. Their conductor is at most(11-1)(13-1)=120. Every m=n-a>=120 is pi+qj, so the q^a term in F multiplied by g_p g_q proves strictness. This argument also works when a is small: it excludes a chain by its complete primitive-root identity, not only by comparing initial root sizes.

<a id="s5e"></a>
### 5E. Exceptional2<=a<=23, k!=3, n>=a+24

For k=2 assume a>=5; the lower pairs are in Section6. If x=2^w is marked then x=8 or16, hence a in{7,8,15,16}. Use(p,q,c)=(5,3,11). The decompositions are8=5*1+3*1 and16=5*2+3*2, so u>=1. The fourth window of Section3 represents every m>=24 with i=0<u. The intact third chain is11, not7: when a=7 or8 a root7 claim would collide with a marked size, and when a=15 or16 the chain rooted7 is unnecessary. Roots3,5,11 are distinct, odd, and avoid both marks. This explicitly preserves the reviewed root11 repair.

For k>=4 the only collision of the standard roots2,3 with the other mark is(k,a)=(4,3). Then x=4, and use roots2,5,7 with x=2*2+5*0. The fifth window represents every m>=24 with i=0<2, so(3.3) applies.

Outside that case use p=2,q=3. Select c among{5,7,11,13}, avoiding divisibility by k and avoiding the other marked size. At most one candidate is divisible byk and at most one equals the other mark; at least two choices remain, so one can be chosen explicitly, for example the smallest surviving candidate. This is enough to exclude all later hits as well: the other mark differs by1 from a k-power and is not divisible byk. For evenx use u=x/2>=2,v=0; for oddx use u=(x-3)/2>=1,v=1. The last four windows of Section3 give all m>=24 with i=0<u. All roots are primitive, distinct and intact. This proves the entire exceptional small-a tail, without assuming a uniform root7 chain.

<a id="s6"></a>
## 6. The four low binary pairs

### 6.1 Exact marked identities and residual partitions

For k=2, P_2(q)=product_{h>=1}(1+q^h)=product_{c odd>=1}g_c by disjoint binary chains. Define

    R(q)=product_{c odd>=9}g_c,
    r(m)=[q^m]R, with r(m)=0 for m<0.

Thus R counts partitions into odd parts>=9 with UNRESTRICTED multiplicities. It does not count distinct odd parts. This correction to the earlier outline is forced by the actual checked definition `RBAbsorb.Residual` and by the chain identity itself.

For distinct partitions each part is either absent or occurs once, so

    C_2(a;q)-C_2(a+1;q)
      = P_2(q) q^a(1-q)/((1+q^a)(1+q^(a+1))) = T_a(q)R(q),

where regrouping the odd-root1,3,5,7 factors gives

    T_1=q(1-q)g_3g_4g_5g_7,
    T_2=q²(1-q²)g_4g_6g_5g_7,
    T_3=q³(1-q⁴)g_8g_6g_5g_7,
    T_4=q⁴(1-q⁴)g_8g_10g_3g_7.                                 (6.1)

For example dividing g_1 by(1+q)(1+q²) gives g_4 in the first identity. For the next three, replace1/(1+q^h) by(1-q^h)g_(2h) and cancel the appropriate odd-root factors. These are identities of the literal marked difference, not positivity assertions about T_a alone.

### 6.2 Exact coefficient certificate for the four rational kernels

Let c_a(n)=[q^n]T_a. Their denominator exponent lists, numerator shifts, and periods are

| a | h_1,h_2,h_3,h_4 | numerator q^a-q^(a+delta) | P_a |
|---|---|---|---|
|1|3,4,5,7|delta=1|420|
|2|4,6,5,7|delta=2|420|
|3|8,6,5,7|delta=4|840|
|4|8,10,3,7|delta=4|840|

The certificate gives c_1(2)=c_2(4)=c_3(7)=c_3(12)=c_4(8)=-1 and all other coefficients nonnegative. Here is a finite, reproducible description of its ENTIRE all-tail argument. Expand D_a=product_i(1-q^(h_i))=1+sum_{j>=1}d_jq^j. With c(n)=0 for n<0, the equation D_a T_a=q^a-q^(a+delta) uniquely fixes every coefficient by

    c(n)= [n=a]-[n=a+delta]-sum_{j>=1}d_j c(n-j).              (6.2)

The finite literal arrays contain this recurrence for every0<=n<7P_a. For0<=n<3P_a the arrays check nonnegativity except the listed negative indices. For each0<=r<P_a the four coefficients at r+3P_a,r+4P_a,r+5P_a,r+6P_a have all four initial forward differences, of orders0,1,2,3, nonnegative.

Each h_i divides P_a. The sums h_1+h_2+h_3+h_4 are respectively19,22,26,28. Multiplying T_a by(1-q^(P_a))^4 gives a polynomial of degrees1663,1662,3341,3340 respectively, each<4P_a: replace each ratio(1-q^P)/(1-q^h) by its finite geometric polynomial and retain the numerator. Therefore the fourth forward difference of c(r+P_a u) is0 for all u>=0. On the tail beginning at3P_a the exact Newton formula is

    c(r+P_a(u+3)) = b_0 + binom(u,1)b_1
                            +binom(u,2)b_2+binom(u,3)b_3,     (6.3)

where b_i is the ith initial forward difference at r+3P_a. The four certified nonnegative b_i prove the infinite tail; the finite prefix handles all earlier degrees. Formula(6.2), the stated bounds, and the exact arrays in the unchanged canonical modules define a finite arithmetic certificate, rather than an unspecified numerical sweep. Its recurrence and all comparisons were kernel-reduced during the independent replay. The arrays are packaged as source, not as an oracle or an extra hypothesis.

For transparency, the first25 coefficients, n=0,...,24, are:

    a=1: 0,1,-1,0,1,0,0,0,1,0,0,1,0,1,0,1,1,0,1,1,1,1,1,1,1
    a=2: 0,0,1,0,-1,0,1,1,0,0,0,0,1,1,1,0,0,1,1,1,1,1,1,1,1
    a=3: 0,0,0,1,0,0,0,-1,1,1,1,1,-1,0,0,1,2,1,1,0,0,1,1,2,2
    a=4: 0,0,0,0,1,0,0,1,-1,0,1,0,1,1,1,0,0,1,0,1,2,1,1,1,1.

Combining these values with all-tail nonnegativity gives the coefficientwise lower bounds T_a>=L_a, with the negative atoms retained:

    L_1=q+q⁴+q⁸+q^11-q²,
    L_2=q²+q⁶+q⁷+q^13-q⁴,
    L_3=q³+q⁸+q⁹+2q^16+q^21+q^23-q⁷-q^12,
    L_4=q⁴+q⁷+q^10+q^17-q⁸.                                    (6.4)

Every exponent of L_a is<25. Thus the displayed25 values verify its finitely many nonzero inequalities; beyond that range the right-hand lower-bound coefficient is0 and the certified nonnegativity applies. Multiplication by the nonnegative R preserves these bounds coefficientwise.

### 6.3 Minimum-part injections absorb every negative atom

For fixed n,d let F(n,d) be the residual partitions of total weight n-d, empty if d>n. Then |F(n,d)|=r(n-d). When d<n each such partition is nonempty; let w be its least part, including its multiplicity if repeated.

There is an injection

    F(n,d) -> F(n,d+2) disjoint_union F(n,d+9).                 (6.5)

If w=9 delete one9, landing in the second summand. Otherwise w>=11; replace one least w by w-2, landing in the first. The result still has odd parts>=9. The lowering map is injective because its new least part w-2 occurs exactly once: all old remaining parts are>=w. Thus recover w by adding2 to the least part and restore it. Deletion is injective by restoring9. The summand tag distinguishes the two cases even if their resulting untagged partitions could coincide.

Similarly there is an injection

    F(n,d) -> F(n,d+4) disjoint_union F(n,d+9)
                              disjoint_union F(n,d+11).       (6.6)

Delete a least9 or11 into its tagged summand; otherwise w>=13 and lower it by4. The new minimum is again unique and the same inverse argument proves injectivity. Repeated old minima cause no ambiguity: precisely one chosen occurrence is removed, and every other occurrence stays strictly above the new one. Therefore, for d<n,

    r(n-d)<=r(n-d-2)+r(n-d-9),
    r(n-d)<=r(n-d-4)+r(n-d-9)+r(n-d-11).                       (6.7)

No claim about an injection on partitions with distinct odd parts is used.

Apply the first inequality with d=2,4,7 for L_1,L_2,L_3. For L_3 also apply the second with d=12; its target shifts16,21,23 are disjoint tagged terms, and the two copies of shift16 in L_3 pay the two separate demands. For L_4 use the first inequality with d=8. When n>=17 all these d are<n. Subtracting the absorption inequalities from(6.4) gives

    [q^n]T_1R >= r(n-1)+r(n-8),
    [q^n]T_2R >= r(n-2)+r(n-7),
    [q^n]T_3R >= r(n-3)+r(n-8),
    [q^n]T_4R >= r(n-4)+r(n-7).                               (6.8)

These are the explicit surplus bounds, not just nonnegativity.

A single odd part gives r(m)>0 for oddm>=9. For evenm>=18 use the two parts9 andm-9, allowing the repeated pair9+9. Thus every right side in(6.8) is positive for n>=17. For the first bound at n=17 use r(9); at evenn use r(n-1), and at oddn>=19 use the even argument n-1>=18. In the second bound use r(n-7) for evenn and r(n-2) for oddn. In the third use r(n-3) for evenn and r(n-8) for oddn. In the fourth use r(n-7) for evenn and r(n-4) for oddn. Each chosen argument is odd>=9 except the explicitly treated first-bound odd case. This proves all four native adjacent differences strictly positive at every n>=17.

<a id="s7"></a>
## 7. Exhaustive finite closure and global strict adjacency

Let E(k,a) mean that a=k^e or a+1=k^e for some e>=1. We claim

    C_k(a;n)>C_k(a+1;n) whenever k>=2,a>=1,n>=max(a+5,17).     (7.1)

If a>=24 use5A. If a=1 use5B or the binarya=1 case of Section6. For2<=a<=23, the binary casesa<=4 are in Section6, and the k=3 exceptional cases are in5C. All other nonexceptional degrees n>=a+120 are in5D; exceptional degrees n>=a+24 withk!=3 are in5E. Thus exactly the following finite comparisons remain:

    2<=k<=143, 2<=a<=23, (k=2 implies a>=5), not(k=3 and E(k,a)),
    max(a+5,17)<=n<=a+23   if E(k,a),
    max(a+5,17)<=n<=a+119  otherwise.                           (7.2)

Why is the upper k bound sufficient? These intervals have n<=142. If k>143, every partition of n has each multiplicity<=n<143<k, so its C_k and C_143 counts agree. A small-a exceptional pair already forces k<=a+1<=24; hence for k>143 the comparison lies in the nonexceptional case and is exactly the corresponding k=143 comparison. There is no unbounded computational search left.

The certificate for(7.2) concerns the ORIGINAL finite marked polynomials, not a conditionally assumed table. In Z[X] define

    U_(k,h)=sum_{j=0..k-1}X^(jh),
    V_(k,h)=sum_{j=0..k-1}jX^(jh),
    P_k=product_{h=1..142}U_(k,h),
    M_(k,a)=V_(k,a)product_{1<=h<=142,h!=a}U_(k,h).

For all n<=142, [X^n]M_(k,a)=C_k(a;n). The exact finite identity

    (1-X^a)(1-X^(ka))M_(k,a)
       =[X^a-kX^(ka)+(k-1)X^((k+1)a)]P_k                     (7.3)

follows from the finite geometric sum and its marked derivative. It gives the sparse recurrence, with negative-index coefficients0,

    m_a(n)=m_a(n-a)+m_a(n-ka)-m_a(n-(k+1)a)
             +p_k(n-a)-k p_k(n-ka)+(k-1)p_k(n-(k+1)a).       (7.4)

All marked indices on the right are smaller than n, so induction proves that any supplied row satisfying(7.4) is the actual marked row, rather than external unchecked data.

For completeness, the unmarked-row compression is also exact. Put Q=P_143. Through degree142 this is the unrestricted partition product. If D_H=product_{h=1..H}(1-X^h), finite telescoping yields

    D_H product_{h=1..H}U_(k,h)=product_{h=1..H}(1-X^(kh)).

The constant coefficient of D_H is1, so convolution-coefficient induction permits cancellation through a prescribed finite degree. Consequently

    P_k = Q product_{h=1..floor(142/k)}(1-X^(kh))   mod X^143. (7.5)

Q itself is supplied by142 geometric stages. Equivalently its Hth row is obtained by summing the previous row at n,n-H,n-2H,... for0<=n<=142. The certificate first identifies these rows from the stage equations, then each short signed-numerator product in(7.5), then the marked rows via(7.4), and finally checks m_a(n)>m_(a+1)(n) at exactly the predicate(7.2). Every endpoint is inclusive as displayed. The source declaration `RBSharedClosed.full_table` discharges that predicate on these original M polynomials; it is not the earlier one-premise conditional assembly.

This is a computer-assisted finite part of the proof. Its reproducible certificate consists of exact integer literals, recurrence equalities, and the explicitly bounded comparisons, all included in the portable unchanged source package and checked by kernel reduction during the independent replay. The mathematical justification for trusting finite rows as coefficients is(7.3)-(7.5) and the stated induction, not agreement with a floating-point computation. Together with the five constructions and Section6 it proves(7.1) for every natural parameter in its range.

<a id="s8"></a>
## 8. From adjacent sizes to residue classes: proof of the theorem

Every positive size in residue classr, represented by1<=r<=t, is uniquelyr+jt,j>=0. Consequently

    D_k(r,t;n)=sum_{j>=0}C_k(r+jt;n),                           (8.1)

a finite sum because C_k(a;n)=0 whena>n. For k>=3, Section4 gives each adjacent comparison for all degrees. Telescope fromr+jt to s+jt and sum(8.1). This proves the first clause.

For the strict clause n>max(t+3,16) means n>=t+4 andn>=17. Every a betweenr ands-1 satisfiesa<=t-1, hence n>=a+5. Formula(7.1) therefore gives C_k(r;n)>C_k(s;n) by telescoping the j=0 term. Every j>=1 comparison is nonnegative: whenk>=3 use Section4; whenk=2 all its adjacent starting sizes are>=r+t>=7, within the proved binary weak rangea>=5. A positive j=0 difference plus nonnegative remaining differences gives D_k(r,t;n)>D_k(s,t;n). This completes both literal clauses, including residue representative t, all unbounded k,t and the strict threshold stated in the source.

<a id="s9"></a>
## 9. Prior work, attribution and bounded contribution assessment

Jackson and Otgonbayar [JO22, Theorem1.1 and Corollary1.2] establish the fixed-k,t marked-occurrence asymptotic and eventual bias toward smaller residue representatives. Their Theorem1.3 proves weak ordering for2<=k,t<=10 (alln>=1 fork>=3, n>=9 fork=2) and strict ordering forn>=17. The source pages1,4,5 were personally visually checked for the definitions, finite parameter bounds and exact conjecture. The source's Section4.3 obtains effective per-parameter analytic cutoffs followed by finite checks; the prior qualification inspected its Bessel estimates and parameter-dependent starting range. Eventuality for each fixed parameter does not itself prove the uniform all-parameter statement above.

Craig [C22v5, Theorems1.1–1.2, Corollary1.3], in the distinct-part case, gives an explicit circle-method error estimate forn>400t²/3, eventual ordering for eacht, and weak ordering for2<=t<=10,n>8. The ownedv5 pages2–3 were personally rendered and checked here. These are relevant marked-statistic results, but do not supply our all-t strict threshold or the all-k weak statement. The source's changes between versions are a reason to bind the inspectedv5, not an allegation about its correctness. Craig v5, footnote2 on p2, already reports numerical observations of the small distinct-part exceptions appearing in Section6; no novelty is claimed for those exceptions. The native Jackson–Otgonbayar remark on p4 also establishes the sharpness of the strict threshold, exhibiting equality at n=t+3 for k=2.

The two later Jackson–Otgonbayar works [JO-U22, Theorem1.1] and [JO-N23, Theorem1.1] concern k-indivisible partitions, where no part is divisible byk. The first gives a coprime-k,t asymptotic involving digamma values and the representative of k^(-1)r modt; the second proves the corresponding No Ties assertion. Their owned primary pages2 were personally rendered and checked. Equal UNMARKED partition products, or the Glaisher bijection between the two partition classes, do not preserve the occurrence statistic. The k-indivisible ordering need not be the ordering of integer residue representatives. Thus these theorems are not a full marked bounded-multiplicity comparison or a proof of the finite uniform boundary.

Heim–Neuhauser [HN24, Theorem2.2] prove an all-k classification of the unmarked product inequality p_k(a)p_k(b)>p_k(a+b), with specified equality and reverse exceptions. The ownedv1 p5 was personally rendered and checked. An inequality between numbers of partitions is different from an adjacent size-occurrence inequality within the same partition class, and no complete implication to(7.1) or the native threshold is supplied by the inspected theorem.

Our methods are classical in their basic ingredients: finite generating functions and marking, Euler/Glaisher chain telescoping, positive geometric sums, coprime numerical-semigroup conductors, minimum-part injections, forward differences and the Newton basis, and exact finite arithmetic certificates. We claim no novelty for these tools, for a helper theorem, for an isolated finite computation, or for writing a Lean formalization alone. The contribution assessed in the owned independent qualification is their complete target-specific combination: all-parameter marked positivity, the four exact binary identities with negative-atom absorption, uniform strict-support constructions, and the exhaustive finite reduction recovering exactly the source boundary.

The strongest contrary novelty case remains real: an existing full adjacent marked-count/support theorem, or an authenticated complete standard specialization of classical results to all these parameters, would subsume the result. Neither the inspected native per-parameter algorithm nor the four inspected companion scopes provides that full bridge. The owned2026-11-16 qualification and root adjudication therefore recommended BOUNDED SUBSTANTIAL for the corrected WHOLE result, conditional on its full verification; they did not award component credit or certify worldwide priority. Their then-pending formal table/replay tasks have since completed, but their bounded literature coverage is not thereby enlarged.

The qualification compared released statement/definition/family fields for114 credited results, with mixed lexical and personal scope review, rather than114 proof audits. Its closest partition-family comparisons were colored binary valuations, unrestricted aggregate partitions, and composition/down-set injections, none supplying this marked endpoint. Current-registry metadata records the OpenAI/math head4eaee87548250b2682affda7d05d947c05554bae; a head identifier and selected statement catalogue are not a semantic audit of all registry proof bodies. Unread publisher-final versions, unlocated subsequent work, deleted histories and unindexed literature remain limits. No new network or search was performed while authoring this manuscript, and no current-live MathDB solution status is asserted.

<a id="s10"></a>
## 10. Formal certificate, independent replay and trust limits

The authoritative source index contains332 canonical Lean modules. This authoring task rehashed every one against that index and found all332 byte-identical; it changed no mathematical source. Two independent audit sources and a version-probe source are additional owned evidence, not extra canonical proof modules. The paper-to-definition/proof map is `crosswalk.json`.

The final independent replay report records that all332 canonical modules were freshly compiled from independently extracted sources starting with an empty local build, each followed by a separate `leanchecker` kernel check. The resumed run completed the remaining positions and compiled/checked independent `RBReplayUnconditional` and `RBReplayAxiomMap` audits. The fully expanded original weak and strict declarations are closed and use literal Mathlib partitions. The reported transitive closure audit covered68,573 constants and found only propext, Classical.choice and Quot.sound, with no unsafe or partial constant. Four compiler-generated RBPrefix helper declarations named with the _unsafe_rec suffix carry partial flags outside this proof closure; none is reachable from the proof. Their presence and the safe kernel definitions are disclosed in the independent audit.

The pinned environment is Lean4.34.1 and mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. `pins.json` retains exact binary hashes and dependency metadata. The trust base includes those Lean/kernel/leanchecker binaries, prebuilt upstream mathlib/Batteries/other oleans, and the kernel's GMP-assisted integer literal operations. The independent lane did not rebuild all upstream dependencies or attest their source-to-olean provenance. `leanchecker` uses the same Lean kernel; it is a separate replay, not a different foundational system. The independent axiom-map audit traverses imported declaration types/values and inductive/constructor/recursor dependencies, whereas author `#print axioms` metadata alone is a weaker check. These limits remain explicit.

The replay used670 of its original768 formal markers without a budget reset. Marker#612 was interrupted with UNKNOWN outcome and no receipt/output/olean; it remains charged and preserved. Position305 was then compiled under a new retry label and separately checked, followed by all remaining modules and audits. Thus the complete successful332-module map does not convert interrupted#612 into a PASS. The new resumed receipts report maximum wall33.83seconds and sampled groupRSS3.03GB, within their unchanged formal caps. No new formal call was made for this manuscript.

All prior/root/current process deviations remain UNWAIVED. The replay report records missing earliest position0–9 driver logs, the version-probe olean, an author-side f003 failure, interrupted#612, a documentary parsing failure followed by a corrected audit, direct-shell inspection commands, oversized displays and scratchpad helper texts. It distinguishes full kernel replay from selective manual body reading. This authoring task also preserves its own oversized/truncated inventory displays, without claiming their missing displayed text as personally read. Source hashes and a passed kernel do not erase those deviations or replace independent review of this prose.

<a id="s11"></a>
## 11. Portable source package and manuscript review boundary

The accompanying `proof-package.zip` contains this manuscript, `crosswalk.json`, the MG-resolution record, all332 unchanged canonical sources in their indexed order, both independent audit sources, exact source/export indexes, pinned environment metadata, retained target-only statement/provenance, prior qualification and final replay reports, and a standard-library extraction verifier. The source archive is portable; it is not a claim that a full upstream toolchain rebuild or an offline hermetic dependency bundle has been supplied. The extraction verifier checks source hashes without invoking Lean, running mathematical experiments, or contacting the network. The earlier source-appendix paper is retained as evidence outside the canonical source count; readers need not use a50MB source dump as a substitute for the arguments in Sections2–8.

This manuscript was prepared after the full replay and is an AUTHOR exposition. A fresh independent reviewer must check Sections5–6 against the unchanged code, the native binding in Section1, the bounded attribution in Section9, and package extraction before any acceptance action. The present work changes no campaign count and makes no publication claim.

<a id="refs"></a>
## References and exact inspected versions

* [JO22] Faye Jackson and Misheel Otgonbayar, *Biases among Congruence Classes for Parts in k-regular Partitions*, [arXiv2207.04352v1](https://arxiv.org/abs/2207.04352v1), submitted2022-07-10; internal manuscript date2022-07-12. Definition in abstract; Theorems1.1,1.3, Corollary1.2, Conjecture1.4, Lemma3.1 and Section4.3. The inspected PDF hash is ac58acf3e8b77762b81300c9a8c99f9da98bc74a3f0ada3a9263e54fdd47a8a8. Official metadata authenticated by the prior qualification listed onlyv1; no publisher-final identity is inferred.
* [C22v5] William Craig, *On the Number of Parts in Congruence Classes for Partitions into Distinct Parts*, [arXiv2110.15835v5](https://arxiv.org/abs/2110.15835v5),2022-07-22. Theorems1.1–1.2 and Corollary1.3; inspected ownedv5, not an authenticated publisher-final body. The prior qualification identified the publication DOI [10.1007/s40993-022-00355-4](https://doi.org/10.1007/s40993-022-00355-4); that publisher-final body remains unread.
* [JO-U22] Faye Jackson and Misheel Otgonbayar, *Unexpected Biases between Congruence Classes for Parts in k-indivisible Partitions*, [arXiv2207.06365v1](https://arxiv.org/abs/2207.06365v1),2022-07-13, Theorem1.1. Owned author manuscript; publication-list metadata identifies J.NumberTheory248(2023),310–342, DOI10.1016/j.jnt.2023.01.006; the final publisher body was not compared.
* [JO-N23] Faye Jackson and Misheel Otgonbayar, *Parts in k-indivisible Partitions Always Display Biases between Residue Classes*, [arXiv2305.05753v1](https://arxiv.org/abs/2305.05753v1),2023-05-09, Theorem1.1. Owned author manuscript; publication-list metadata identifies J.NumberTheory261(2024),299–311, DOI10.1016/j.jnt.2024.02.003; final publisher body not compared.
* [HN24] Heim–Neuhauser, *Inequalities for k-regular partitions*, [arXiv2406.10987v1](https://arxiv.org/abs/2406.10987v1),2024-06-16, Theorem2.2. Ownedv1; publication lead DOI [10.1007/s40993-025-00684-0](https://doi.org/10.1007/s40993-025-00684-0); the publisher-final body was not authenticated here.

