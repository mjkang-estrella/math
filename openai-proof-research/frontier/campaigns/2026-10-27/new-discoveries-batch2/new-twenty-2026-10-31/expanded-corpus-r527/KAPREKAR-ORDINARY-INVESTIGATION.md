# MathDB 353105: full ordinary proposal, unqualified

Author-only ordinary proof, not independent PASS, scientific acceptance, novelty clearance, or credit. No formal execution. One prospective family comprising all four clauses, not four results.

## Exact object and statement
Fix an integer base b>=2. Let s_b(v) be the sum of the base-b digits of the nonnegative integer v. Put F_b(u)=#{v>=0:v+s_b(v)=u}, and K_b(n)=min{u>=0:F_b(u)=n}. All these minima exist by the source recurrences. Our theorem is exactly the four formulas in originals/353105.jsonl, with ht(K_b(n)), not the source's abbreviated ht(n). There is no claim about the digit-rearrangement Kaprekar map.

Define integer towers T_0=1 and T_{j+1}=b^(T_j). For u>1 and h>=2 the source height convention is equivalent to
                  ht_b(u)=h iff T_{h-2}<u<=T_{h-1}.             (H)
Indeed repeated logarithms preserve strict inequalities until they first reach (0,1]; equality at a tower boundary belongs to the shorter height. Every K used below is >b, so the source's problematic assertion of uniqueness at u=1 is immaterial and is not exploited.

## Primary dependencies actually read
Alekseyev and Sloane, On Kaprekar's Junction Numbers, arXiv:2112.14365v2, 13 March 2022, acquired through guarded https://arxiv.org/pdf/2112.14365. Actual current official record lists v1 and v2, with no displayed journal reference. An independent author delivery https://neilsloane.com/doc/colombian.03.12.2022.pdf was acquired and its material statements compared; it also prints Conjecture 28 and the same obstruction discussion. This does not certify equality with the journal final. Search identifies Journal of Combinatorics and Number Theory 12:3, 115-155, with inconsistent secondary year labels 2020/2022/2023; actual publisher final remains unacquired/unread.

The relevant statements and proof passages of Theorems 8-18 and 20 and Section 10 were read as PDF-extracted text. No whole-article or visual-glyph audit is claimed. Source theorems are attributed inputs, not new deductions or independently reconstructed certificates.

Write E(n) for the common leading exponent in all K_i(n), and alpha=1 for even b, alpha=1/2 for odd b. Theorem 15 gives, for n>=2,
             b^E(n)<K(n)<=K_i(n)<alpha*b^(E(n)+1).             (B)
Equation (44) and Theorem 18 give, with c=ceil(n/2), f=floor(n/2),
       (b-1)E(n)=min_i [K_i(c)+K_{-i-2}(f)+2].              (R)
Theorem 18 also makes E strictly increasing on n>=2. Theorem 27 makes K strictly increasing, but only monotonicity from E and (B) is needed for filling intervals. Initial values (Theorems 9,10, (55), and Theorems 16,17) are
 E_2(2)=2, E_2(3)=7, E_2(4)=12;
 K_3(2)=4, K_3(3)=28, E_3(5)=17, E_3(6)=29;
 even b>=4: E(2)=2, E(3)=b+3;
 odd b>=5: E(3)=2, E(4)=4 if b=5 and 3 if b>=7.
For base three the latter E values follow exactly from (K(3)+K(2)+2)/2 and K(3)+1. They are symbolic deductions, not numerical tests.

For every t>=2, (R),(B) imply
 E(2t)<[2alpha*b^(E(t)+1)+2]/(b-1).                        (U)
For n with ceil(n/2)>=2, (R) gives
 E(n)> b^(E(ceil(n/2)))/(b-1),                            (L)
because every first summand is >=K(ceil(n/2))>b^E. This remains true when floor(n/2)=1, since all K_i(1) are nonnegative. No enumeration of residues is needed. These two scalar inequalities are the entire bridge past the source recurrence.

## Even b>=4
For k>=1 set U_k=E(2^k). We prove U_k<=T_k-1. At k=1, 2<=b-1. If this holds at k, (U) gives
 U_{k+1} < (2T_{k+1}+2)/(b-1) <= T_{k+1}-1.
The last inequality is equivalent to (b-3)T_{k+1}>=b+1. Here T_{k+1}>=b^b and b>=4, so it holds, for instance from T_{k+1}>=b+1 and b-3>=1.
For k>=2 let L_k=E(2^{k-1}+1). We prove L_k>=T_{k-1}+1. Initially L_2=b+3>=b+1. The next left endpoint has ceiling-half 2^{k-1}+1, so (L) gives
 L_{k+1}> b^(T_{k-1}+1)/(b-1)= b*T_k/(b-1)>=T_k+1,
since T_k>=b-1.
For 2^{k-1}<n<=2^k, k>=2, monotonicity and (B) now give
       T_k < b^(L_k) < K(n) < b^(U_k+1) <=T_{k+1}.
Thus (H) gives height k+2. For n=2 directly b<K(2)=b^2+1<b^b=T_2: b^2+1<b^b for b>=4. The height is 3, also the claimed formula. This proves clause (iii).

## Odd b>=5
For k>=2 we prove E(2^k)<=T_{k-1}-1. The initial E(4)<=b-1 is given above. In (U), 2alpha=1, so induction gives
 E(2^{k+1})<(T_k+2)/(b-1)<=T_k-1.
The last inequality is (b-2)T_k>=b+1; b>=5 and T_k>=b suffice.
For k>=2 prove E(2^{k-1}+1)>=T_{k-2}+1. At k=2 this is E(3)=2. The step follows exactly from (L): b*T_{k-1}/(b-1)>=T_{k-1}+1 because T_{k-1}>=b-1.
For 2^{k-1}<n<=2^k the resulting bounds are
                     T_{k-1}<K(n)<T_k.
The height is k+1. At n=2, 1<K(2)=b+1<b^b and K(2)>b, so more precisely T_1<K(2)<T_2 and its height is 3? This reveals an issue: the claimed clause (iv) gives 2 for n=2.

## CRITICAL FIDELITY CHECK -- PROPOSAL FAILS
The preceding line is an indexing error in the proposed odd-base invariant translation, not a mathematical counterexample. Under (H), height 3 corresponds to T_1<u<=T_2. But the source explicitly states ht(K(2))=3 for every b>=3, while Conjecture 28(iv) prints ceil(log2 2)+1=2. Likewise K(3)=b^2+1 has height 3, whereas ceil(log2 3)+1=3. The n=2 branch is a genuine printed endpoint discrepancy.

Recheck (H): ht defined as one more than logarithm count; for b+1, log_b(b+1)>1, second logarithm is in (0,1), so height is 3. There is no convention giving height 2 while preserving the displayed definition. The original MathDB literal includes n>=2 and reproduces this endpoint.

More substantially, for odd b>=5 and k>=2 the interval bounds above T_{k-1}<K(n)<T_k give height k+1, as desired. Thus the corrected odd-base theorem for n>=3 follows, but the literal full conjunction is false already at n=2 in every odd b>=5. This is a SOURCE ENDPOINT CORRECTION, zero discovery credit. No full survivor is proposed. The source itself explicitly states the contrary initial height in (91)'s preceding sentence, so no claim of a significant new counterexample is justified.

## Base two, retained to document the sustained route
For k>=2 prove E_2(2^k)<=T_{k+1}-3. Initially 12<=16-3. If T=T_{k+1} and E<=T-3, the exact recurrence and (B) give
 E_2(2^{k+1})=2K(2^k)+2<2^(E+2)+2<=2^(T-1)+2<=2^T-3,
because T>=16 implies 2^(T-1)>=5.
For k>=2 prove E_2(2^{k-1}+1)>=T_k+2. Initially 7>=4+2. The exact recurrence gives E at the next left endpoint >=K at the preceding left endpoint +2>2^(T_k+2)+2>=T_{k+1}+2.
Consequently T_{k+1}<K(n)<T_{k+2} on 2^{k-1}<n<=2^k, k>=2. Height is k+3. The n=2 case K(2)=5 lies between T_2=4 and T_3=16, giving height4. This proves (i), conditional only on the attributed exact source recurrence.

## Base three, retained
Let B_j=E_3(5*2^j), j>=0. Prove B_j<=T_{j+2}-1. Initially 17<=27-1. The exact recurrence E_3(2t)=K_3(t)+1 and (B) imply
 B_{j+1}<T_{j+3}/2+1<=T_{j+3}-1,
since T_{j+3}>=4.
Let A_j=E_3(5*2^j+1). Prove A_j>=T_{j+2}+1. Initially 29>=27+1. The exact recurrence or (L), at the next left endpoint, gives
 A_{j+1}>3^(T_{j+2}+1)/2=(3/2)T_{j+3}>=T_{j+3}+1.
For 5*2^j<n<=5*2^{j+1}, the resulting bounds are T_{j+3}<K_3(n)<T_{j+4}, hence height j+5. This is ceil(log2(n/5))+4. For 3<=n<=5, use K_3(3)=28>27=T_2 and K_3(5)<3^18<3^27=T_3, giving height4 as required. Thus (ii) holds under the attributed source recurrence.

## Significance/adversarial outcome
The sustained four-regime route reduced all intended clauses to scalar invariant regions for the source's exact recurrence; it did not require a new digit-combinatorial mechanism. Even leaving the source's explicit endpoint contradiction aside, this is a concrete routine-adaptation objection: (R),(B), initial values and the above elementary tower margins suffice for the corrected statement. The contrary case is that the authors explicitly raised the full height question and identified the two obstacles; the threshold margins do answer those obstacles. However the exact assigned full conjunction is already false by an explicitly source-known endpoint. Recommend zero and no review/formal dispatch. The corrected theorem and its proof are retained, not offered as a substitute target or credited special case.

No FULLCANDIDATE survivor exists. This file retains the complete attempted argument and the decisive self-correction, rather than hiding the failed qualification.
