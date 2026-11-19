# A partition-statistic inequality from Harada's conjecture

Implementation paper v1, 2026-11-14. MathDB working ID 358145. This paper supplies an ordinary proof and accompanies a literal Lean certificate. Novelty, contribution, significance, current prior art, raw MathDB statement authentication, full101 comparison, independent endpoint review and independent extracted replay remain held. Formalization itself earns no new mathematics credit; credit remains 0, counts 62/80 NEW and 101 total.

## Statement and source correspondence
For a partition lambda=(lambda_1>=...>=lambda_L>0) of n, let h_j be its jth column height, extended by zero, and put T(lambda)=sum_i(i-1)lambda_i and
Psi(lambda)=choose(L,2)+T(lambda)+sum_{j>=1}h_j h_{j+1}.
Let p(n) count all partitions, including p(0)=1, and D(n)=choose(n,2)p(n)-sum_{lambda|-n}Psi(lambda).

**Theorem.** For every integer n>=7, D(n)>0.

The primary source is Sugimoto Masahiro (Masahiro Sugimoto), *Harada's conjecture II for the finite general linear groups and unitary groups*, arXiv:2304.10708v3, 26 January 2024, https://arxiv.org/abs/2304.10708v3 (owned acquisition URL https://arxiv.org/pdf/2304.10708). Definitions of rows and conjugates are on p3, Psi is equation (3.2) on p5, and the theorem is precisely Conjecture 5.2 on p11. Pages 1,3,5,11 were rendered and visually inspected in this implementation on 2026-11-14. Other pages were not fully read. The owned PDF SHA256 is 945d3f7aad6096f7c6f647c4fe05730fb1aa5e592efefa36ab23400d34d51028. No current online or journal-final identity was checked; no external request was made.

In Lean, rowsEquiv identifies Nat.Partition n with positive weakly decreasing lists of sum n. T uses zero-based zipIdx, giving exactly i-1. column counts parts >=j; column_missing makes every j>n vanish, so psi's range n truncation is exact. SourceBridge supplies length_rows, column_rows, and arbitrary zero-tail extension. The unchanged D, Target and IntegerTarget retain strict positivity and all n>=7; conversion from integer n uses n.toNat, valid because n>=7. No group-integrality conclusion is asserted.

## Weighted moments and the actual convolution
Write m_a for the multiplicity of part a and s=sum_a m_a(m_a+1)/2. Counting box pairs gives 2T=sum_j h_j^2-n. Also sum_j h_j m_j=(L^2+sum_j m_j^2)/2: expand L^2 and use h_j=sum_{a>=j}m_a. Since h_{j+1}=h_j-m_j, substitution into Psi gives the pointwise identity Psi=n+3T-s.

Use formal series over Q, P=product_{a>=1}(1-x^a)^(-1). Every coefficient calculation below has finite support; at degree n all indices and multiplicities can first be truncated at n. The normalized generating series for s is sum_{a,t>=1}t*x^(at), because (1-y)sum_{u>=0}choose(u+1,2)y^u=y/(1-y)^2. At degree k its coefficient is sum_{at=k}t=sigma(k), the sum of positive divisors of k. Marking one box gives n*p(n)=sum_{k=1}^n sigma(k)*p(n-k): equivalently, formally differentiate the finite Euler product and use xP'=P*sum_a a*x^a/(1-x^a). Thus total s=n*p(n), total Psi=3*total T, and
2D(n)=(n^2+2n)p(n)-3*sum_lambda sum_j h_j^2.
No external weighted-moment theorem is assumed.

Let E(W)=P^(-1)*sum_lambda W(lambda)x^|lambda|. Geometric moments give E(m_a)=A_a, E(m_a^2)=A_a+2A_a^2, E(m_a*m_b)=A_a*A_b for a!=b, where A_a=x^a/(1-x^a). Expanding n=sum_a a*m_a and h_j=sum_{a>=j}m_a in the preceding identity gives
2*sum_n D(n)x^n=P*[sum_a ((a^2-3a)E(m_a^2)+2a*E(m_a))+sum_{a<b}2a(b-3)A_a*A_b].
The coefficient of x^(at) in E(m_a^2) is 2t-1 for t>=1. Hence, defining
c(k)=sum_{a,t>=1,at=k}[(a^2-3a)(2t-1)+2a]+sum_{a<b,t,u>=1,at+bu=k}2a(b-3),
we obtain the exact identity 2D(n)=sum_{k=1}^n c(k)p(n-k), including n=0 by empty sums. All differences in weights are integers; only 2t-1 is natural subtraction in the certificate. This is exactly the frozen canonical coefficient, not an assumed replacement kernel. The finite Lean layer-cake/marked-part and single/double weight-fiber bijections prove these same coefficient calculations without analytic convergence.

## Signs of the canonical coefficient
For fixed k>=3 let S(k,a) be the single-size t sum. For a>0 at most one t satisfies at=k. If a=1 its selected weight is 4-4k, so S(k,1)>=-4k. For a=2 the selected weight is 6-2k, so S(k,2)>=-2k; an empty fiber is zero. For a>=3 every weight is nonnegative. At a=k the sole solution t=1 has weight k^2-k. Adding 4k to the a=1 fiber and 2k to the a=2 fiber makes all fibers nonnegative; retaining a=k proves sum_a S(k,a)>=k^2-7k.

The mixed weight 2a(b-3), with 1<=a<b, is negative only at a=1,b=2, where it is -2. For fixed t at most one u satisfies t+2u=k. There are at most k t values, so the mixed sum is >=-2k. Consequently c(k)>=k^2-9k for k>=3; it is strictly positive for k>=10. Direct finite evaluation of the displayed definition gives
c(0..12)=(0,0,-2,-4,-4,2,16,38,80,128,210,280,448).
Together these prove c(k)>=0 for every k>=5, keeping every negative low degree. The appendix contains kernel-reducible finite certificates for these evaluations, including all five degrees 5..9; no numerical oracle is used.

## Elementary uniform ratio
We prove 2p(n)<=3p(n-1) for every n>=7. The exhaustive finite certificate below covers 7<=n<=174. For n>=175 assume the inequality at every earlier index >=7. Subtract 3/2 times the divisor recurrence at n-1 from that at n. Reindexing gives exactly
n*p(n)-(3/2)(n-1)p(n-1)=sigma(n)+sum_{j=1}^{n-1}sigma(n-j)[p(j)-(3/2)p(j-1)].
The j>=7 brackets are nonpositive. From p(0..6)=(1,1,2,3,5,7,11), the first six brackets are (-1/2,1/2,0,1/2,-1/2,1/2). Since 0<=sigma(k)<=k(k+1)/2<=k^2 for k>=1, the right side is at most (5/2)n^2. The boundary sigma(n) is retained.

Put t=floor((n-1)/20). Choose the multiplicities of 2,3,4,5,6 independently in {0,...,t}; their total weight is <=20t<=n-1. Fill with ones. Distinct choices give distinct partitions, hence p(n-1)>=(t+1)^5>=(n/20)^5. For n>=175, 3n^3>=3*175^3=16078125>16000000=5*20^5, so (3/2)p(n-1)>(5/2)n^2. This pays the extra (3/2)p(n-1) needed to replace (n-1) by n on the recurrence's left side, and proves p(n)<=(3/2)p(n-1). Strong induction proves the uniform ratio. No analytic partition estimate, BO inequality, Lehmer theorem or assumption on ratio monotonicity is used.

## Generic margin and conclusion
Let q:Nat->Nat be monotone, positive everywhere, and satisfy 2q(r)<=3q(r-1) for r>=7. Let C(q,n)=sum_{k=1}^n c(k)q(n-k). For n>=13 retain exactly k=2,3,4,6,7. Every omitted product is nonnegative (k=1 has c=0, and all other omitted k>=5). Thus
C(q,n)>=-2q(n-2)-4q(n-3)-4q(n-4)+16q(n-6)+38q(n-7).
Put F=q(n-7). Five ratio steps, at n-2,...,n-6 (the last >=7), give q(n-2)<=243F/32, q(n-3)<=81F/16, q(n-4)<=27F/8. Monotonicity gives q(n-6)>=F. Substitution, with negative weights retaining their correct inequality direction, gives C(q,n)>=(81/16)F>0. Equivalently 16C(q,n)>=81q(n-7).

For q=p, adjoining a part one proves monotonicity, the all-ones partition proves p(r)>=1, and the previous lemma proves the ratio hypothesis with no residual assumptions. The exact source convolution gives D(n)>=81p(n-7)/32>0 for n>=13. For 7<=n<=12, D=(6,43,120,279,551,1056), respectively, by the exact coefficient convolution and bounded-partition recurrence. These six values complete the proof for every natural n>=7. Any integer n>=7 is its nonnegative natural representative, proving the stated integer endpoint.

## Finite certificates
Let b(n,k) count partitions with parts <=k. Deleting one k, when present, proves b(n,k)=b(n,k-1)+b(n-k,k) for 0<k<=n. Also b(0,k)=1, b(n,0)=0 for n>0, and b(n,k)=p(n) if k>=n. These identities determine every number used below by integer addition, starting at the two boundary conditions. The appendix supplies every intermediate equality as explicit proof terms, not just terminal table numerals. All ratio bases 7..174 occur; M=3p(n-1)-2p(n) is positive in each row. The n=175 row is diagnostic only and is not an induction base.
n | p(n) | M (when n>=7)
---|---:|---:
0 | 1 | -
1 | 1 | -
2 | 2 | -
3 | 3 | -
4 | 5 | -
5 | 7 | -
6 | 11 | -
7 | 15 | 3
8 | 22 | 1
9 | 30 | 6
10 | 42 | 6
11 | 56 | 14
12 | 77 | 14
13 | 101 | 29
14 | 135 | 33
15 | 176 | 53
16 | 231 | 66
17 | 297 | 99
18 | 385 | 121
19 | 490 | 175
20 | 627 | 216
21 | 792 | 297
22 | 1002 | 372
23 | 1255 | 496
24 | 1575 | 615
25 | 1958 | 809
26 | 2436 | 1002
27 | 3010 | 1288
28 | 3718 | 1594
29 | 4565 | 2024
30 | 5604 | 2487
31 | 6842 | 3128
32 | 8349 | 3828
33 | 10143 | 4761
34 | 12310 | 5809
35 | 14883 | 7164
36 | 17977 | 8695
37 | 21637 | 10657
38 | 26015 | 12881
39 | 31185 | 15675
40 | 37338 | 18879
41 | 44583 | 22848
42 | 53174 | 27401
43 | 63261 | 33000
44 | 75175 | 39433
45 | 89134 | 47257
46 | 105558 | 56286
47 | 124754 | 67166
48 | 147273 | 79716
49 | 173525 | 94769
50 | 204226 | 112123
51 | 239943 | 132792
52 | 281589 | 156651
53 | 329931 | 184905
54 | 386155 | 217483
55 | 451276 | 255913
56 | 526823 | 300182
57 | 614154 | 352161
58 | 715220 | 412022
59 | 831820 | 482020
60 | 966467 | 562526
61 | 1121505 | 656391
62 | 1300156 | 764203
63 | 1505499 | 889470
64 | 1741630 | 1033237
65 | 2012558 | 1199774
66 | 2323520 | 1390634
67 | 2679689 | 1611182
68 | 3087735 | 1863597
69 | 3554345 | 2154515
70 | 4087968 | 2487099
71 | 4697205 | 2869494
72 | 5392783 | 3306049
73 | 6185689 | 3806971
74 | 7089500 | 4378067
75 | 8118264 | 5031972
76 | 9289091 | 5776610
77 | 10619863 | 6627547
78 | 12132164 | 7595261
79 | 13848650 | 8699192
80 | 15796476 | 9952998
81 | 18004327 | 11380774
82 | 20506255 | 13000471
83 | 23338469 | 14841827
84 | 26543660 | 16928087
85 | 30167357 | 19296266
86 | 34262962 | 21976147
87 | 38887673 | 25013540
88 | 44108109 | 28446801
89 | 49995925 | 32332477
90 | 56634173 | 36719429
91 | 64112359 | 41677801
92 | 72533807 | 47269463
93 | 82010177 | 53581067
94 | 92669720 | 60691091
95 | 104651419 | 68706322
96 | 118114304 | 77725649
97 | 133230930 | 87881052
98 | 150198136 | 99296518
99 | 169229875 | 112134658
100 | 190569292 | 126551041
101 | 214481126 | 142745624
102 | 241265379 | 160912620
103 | 271248950 | 181298237
104 | 304801365 | 204144120
105 | 342325709 | 229752677
106 | 384276336 | 258424455
107 | 431149389 | 290530230
108 | 483502844 | 326442479
109 | 541946240 | 366616052
110 | 607163746 | 411511228
111 | 679903203 | 461684832
112 | 761002156 | 517705297
113 | 851376628 | 580253212
114 | 952050665 | 650028554
115 | 1064144451 | 727863093
116 | 1188908248 | 814616857
117 | 1327710076 | 911304592
118 | 1482074143 | 1018981942
119 | 1653668665 | 1138885099
120 | 1844349560 | 1272306875
121 | 2056148051 | 1420752578
122 | 2291320912 | 1585802329
123 | 2552338241 | 1769286254
124 | 2841940500 | 1973133723
125 | 3163127352 | 2199566796
126 | 3519222692 | 2450936672
127 | 3913864295 | 2729939486
128 | 4351078600 | 3039435685
129 | 4835271870 | 3382692060
130 | 5371315400 | 3763184810
131 | 5964539504 | 4184867192
132 | 6620830889 | 4651956734
133 | 7346629512 | 5169233643
134 | 8149040695 | 5741807146
135 | 9035836076 | 6375449933
136 | 10015581680 | 7076344868
137 | 11097645016 | 7851455008
138 | 12292341831 | 8708251386
139 | 13610949895 | 9655125703
140 | 15065878135 | 10701093415
141 | 16670689208 | 11856255989
142 | 18440293320 | 13131480984
143 | 20390982757 | 14538914446
144 | 22540654445 | 16091639381
145 | 24908858009 | 17804247317
146 | 27517052599 | 19692468829
147 | 30388671978 | 21773813841
148 | 33549419497 | 24067176940
149 | 37027355200 | 26593548091
150 | 40853235313 | 29375594974
151 | 45060624582 | 32438456775
152 | 49686288421 | 35809296904
153 | 54770336324 | 39518192615
154 | 60356673280 | 43597662412
155 | 66493182097 | 48083655646
156 | 73232243759 | 53015058773
157 | 80630964769 | 58434801739
158 | 88751778802 | 64389336703
159 | 97662728555 | 70929879296
160 | 107438159466 | 78111866733
161 | 118159068427 | 85996341544
162 | 129913904637 | 94649396007
163 | 142798995930 | 104143722051
164 | 156919475295 | 114558037200
165 | 172389800255 | 125978825375
166 | 189334822579 | 138499755607
167 | 207890420102 | 152223627533
168 | 228204732751 | 167261794804
169 | 250438925115 | 183736348023
170 | 274768617130 | 201779541085
171 | 301384802048 | 221536247294
172 | 330495499613 | 243163406918
173 | 362326859895 | 266832779049
174 | 397125074750 | 292730430185
175 | 435157697830 | 321059828590


## Formal realization and dependencies
The full final source is in EXACT-LEAN-APPENDIX-v1.md, not merely linked filenames. Its 45-module ordered graph starts with the unchanged canonical coefficient and source partitions, proves finite multiplicity/layer-cake and marked-part bijections, derives source_D_convolution, proves DP equivalence and the six finite bases, then the direct canonical coefficient bound and generic margin. The separate elementary Euler/injection/finite-certificate chain establishes uniform_ratio. HaradaFinal instantiates the generic hypotheses with actual p and combines the two ranges, then applies target_iff_integer. All source proofs have been freshly compiled together against ONE coefficient definition; no compatibility assertion relies only on equal names.

The actual closed declarations are Harada.target_proved : Harada.Target and Harada.integerTarget_proved : Harada.IntegerTarget. Target unfolds to forall n:Nat, 7<=n -> 0<D(n); IntegerTarget unfolds to forall n:Int, 7<=n -> 0<D(n.toNat). There are no free sequence, statistic, kernel, source-bridge or ratio hypotheses. HaradaFinal's transitive #print axioms output gives exactly propext, Classical.choice, Quot.sound for both endpoints. It separately passes leanchecker. Standard dependencies are Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 plus the eight library paths in the appendix's pinned PINS.json. Executable and supplied metadata hashes matched; upstream olean provenance is trusted under the grant, not fully re-attested.

The prior BO-free ordinary/source review is an owned inherited report, fully read here, not a new independent review of this final endpoint. This implementation is neither an independent acceptance replay nor a novelty/contribution decision. The appendix was extracted to a documentary directory and all 54 included files (45 Lean modules plus helpers/pins) compared byte-for-byte against production, without rerunning Lean. A future reviewer needs a fresh build/cache and at least 90 formal calls to compile and separately kernel-check every module; preserve all caps and allocate contingency explicitly.

## Hostile self-review and limitations
All negative degrees are included; all five ratio steps satisfy the threshold; n=13 is covered; the entire 7..12 interval is separately checked. The factor 2 belongs to the actual source identity, so its positive convolution proves strict D positivity. The ratio induction retains sigma(n), pays the extra 3p(n-1)/2, uses only earlier ratios, and includes every base 7..174. Missing columns and the empty partition are explicit. Pointwise Psi identities and summed moment identities are not conflated. Partial primary reading is confined to the four inspected pages and short header metadata. No journal-final/current-prior/raw/full101/registry claim follows. Process defects, including oversized documentary displays and an accidental root-directory filename listing, are recorded unwaived in FORMAL-HANDOFF-v9.md; a mathematical certificate is not a clean-process verdict.
