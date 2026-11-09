# Literal no-resolution: Problem 27 remains unsettled in this lane

Source: Rampersad–Stipulanti, JIS 21, Article 18.9.1, published December 5, 2018, pp8–10 and Problem27 p20. The current journal PDF is byte-identical to the inherited r237 source (SHA256 160ab6ffbbbbea8a12d6f597f1acf8d1fdeb80968a02a39d715fda72a15bba84). Define D(X)=sum d_n X^n in F2[[X]], d_n=v2(n+1) mod2. Since d_0=0,d_1=1, its unique compositional inverse U has D(U(X))=X=U(D(X)). This is not reciprocal inversion. Let a_j enumerate u_m=1 and b_j enumerate u_m=0, each increasing and indexed from zero. Problem27 asks whether b is k-regular over Z for SOME integer k>=2. Source terminology “characteristic sequence” here means enumeration, not binary indicator.

Proposition10 gives u_0=0,u_1=1,u_(2n)=0,u_(4n+1)=u_(2n-1) (n>=1),u_(4n+3)=u_n. Proposition25 concerns the binary Fibonacci indicator x; Corollary26 proves a is not k-regular for every k>=2. Proposition18 supplies a mod3 in alternating Fibonacci-length runs; taking changes recovers x shifted by two. Remark28 instead uses u_(2n+1)=bs_(n+1) and a_n=2*l_(n+1)-1, where l enumerates Baum–Sweet ones. Merta1803.00292v1 Theorems2.5–2.6 prove l mod2 is a shifted Fibonacci word and l is nonregular in every base. That is not a theorem about b. Merta1810.03533v3 treats other inverse sequences, with prime-uniform conjectures2.15–2.17. No inspected body supplies a full answer to Problem27.

## Exact compression and rank recursion

Put v_n=u_(2n+1). Every pair of consecutive indices (2n,2n+1) has a zero at 2n. If v_n=0, both indices are zero and the gaps from 2n through to 2n+2 are 1,1. If v_n=1 the only gap is 2. Thus g_n=b_(n+1)-b_n is EXACTLY the infinite concatenation h(v), h(0)=11,h(1)=2. It takes values {1,2}. Set R(t)=sum_(0<=i<t) v_i, and Z(t)=2t-R(t). The pair starting at 2t starts at zero rank Z(t):

    b_(Z(t))=2t;
    if v_t=0, b_(Z(t)+1)=2t+1.

These disjoint blocks exhaust all zero ranks. Equivalently b_n is obtained by inverting the strictly increasing block-boundary sequence Z(t). This is an exact recursion/algorithm, NOT a finite kernel module: inversion of this automatic summatory function is the unresolved step.

A one at a_j has j preceding ones, so exactly a_j-j preceding zeros, ending at a_j-1. Consequently g has value2 precisely at c_j=a_j-j-1. Therefore g_(c_j)=2 and c_(j+1)-c_j=a_(j+1)-a_j-1. This is a rank compression, not an affine subsequence in j, so standard regularity closure cannot transfer the source's nonregularity of a to b.

## Ordinary partial obstruction: only powers of two can survive

This is not a full source-question resolution and receives no credit. From Table1 p14, adjoin a leading-zero state S to the binary MSB acceptor for a. Its 2-uniform morphism is

    S->S2, 2->34, 3->56, 4->32, 5->35, 6->87, 7->86, 8->88.

Code states2,6 by1, the others by0. Every state occurs in the fixed point starting at S; adding S makes leading zeroes harmless. The resulting coding is u, because the table accepts precisely the canonical representations of one positions, with S coding the integer zero. In a uniform fixed point, the pair at indices2n,2n+1 is the substitution image of its state at index n. Hence v is obtained by coding a state by the output of its right child. The resulting NONERASING gap morphism H is

    H(S)=H(3)=H(4)=H(7)=2;
    H(2)=H(5)=H(6)=H(8)=11.

Thus g=H(sigma^omega(S)). All images have length1 or2; there is no erasure. The substitution's adjacency matrix has row sums2 (or column sums2 with the transpose convention), spectral radius2, and all letters occur, so this is a pure 2-substitutive source.

By Proposition16 of the original, the number of ones of u with binary length m is F_(m-1)-1 for even m>=2 and F_(m-1)+1 for odd m>=1. In particular the cumulative count through length m is O(phi^m), phi=(1+sqrt5)/2<2. There are infinitely many ones, e.g. u_(4n+3)=u_n iterated starting at n=1. Thus c is infinite and has density0: c_j=a_j-j-1 and j/a_j tends0. The indicator of c cannot be ultimately periodic, since an infinite ultimately periodic set has positive density. So g is not ultimately periodic.

Suppose b is k-regular. Proposition3(5) of the original makes g k-regular; because g is bounded, Proposition3(3) makes it k-automatic. Its uniform-morphism representation is a coding of a pure k-substitutive fixed point (all occurring letters can be retained). Durand, arXiv1010.4009v1, Theorem16 p11, applies to two multiplicatively independent Perron numbers and two NONERASING morphisms of substitutive words. The actual statement, supporting Corollary6 and proof context were inspected; it does not require primitive substitutions here. Integers2,k are Perron numbers. If k is not a power of2, unique prime factorization makes them multiplicatively independent. Apply Theorem16 with sigma's fixed point and H on one side, the k-uniform fixed point and its coding on the other: g would be ultimately periodic, contradiction. Hence b cannot be k-regular for any nonpower-of-two k.

If b were 2^r-regular, g would be 2^r-automatic and therefore 2-automatic (Proposition3 base-power equivalence). Its partial sums b would then be 2-regular. Conversely a 2-automatic g yields 2-regular b by summation. Thus existence in ANY base is now equivalent to 2-automaticity of this explicit g. This is still a yes/no question, not its answer.

## Sustained base-2 routes and precise missing lemma

1. The eight-state nonuniform gap coding supplies a concrete transducer route. Prefix counts of each state are linear representations, but solving Z(t)<=n<Z(t+1) introduces rank carries. No bounded set of carries or finite Z-module has been established.
2. The source's Fibonacci mechanism concerns a mod3. For compressed exceptional positions, c_j+j+1=a_j; the addition of the enumeration index j prevents turning that modular obstruction into a fixed-index factor of g. Automaticity of an indicator alone never permits selecting its jth one by a regular index operation.
3. Long gaps in c offer a more pointed obstruction. Diagnostics find first new distances 5,11,17,35,65,131,257,515,... . Beginning with t=3, the first record has a_j=5*2^t-3, j=2F_(t+2)-2, c_j=5*2^t-2F_(t+2)-2; the distance is 2^t+1 for even t and 2^t+3 for odd t. These are OBSERVED formulas only. A viable proof route would establish the exact FIRST-occurrence characterization at every t from L_a={11}*1 union 1{1,00}*0{11}*1, then show that if g were automatic, that relation would force an impossible finite-state encoding of the Fibonacci-sized displacement. Neither the all-t extremal lemma nor that pumping argument is proved here. They are explicit missing lemmas, not hidden assumptions.
4. Kernel diagnostics at depths<=4 in bases2,3,4,5,7,8 are saved. For base2 the numbers of distinct length128 prefixes are1,2,4,8,16. These finite prefixes are NOT an infinite-kernel proof. No modular calculation proves nonautomaticity.
5. A strengthened closure bridge is FALSE: a nonerasing image of an automatic word need not be automatic in the same base. The original paper itself supplies a concrete control. The original period-doubling word d is automatic and has pairs (0,1-d_n); applying the same pair-gap calculation to its zero enumeration z gives gaps J(d), J(0)=2,J(1)=11. Proposition5's actual proof identifies these gaps with Thue–Morse run lengths and proves their nonautomaticity in every base. Thus variable-length images of lengths1,2 are already enough to break automaticity; our explicit H cannot be declared automatic by a closure assertion. Also the guessed simple dyadic recursion b_(2n)=2b_n fails at n=1 (b_2=3,2b_1=4). These controls prevent false finite-module shortcuts.

The precise remaining endpoint is: prove or refute 2-automaticity of H(sigma^omega(S)). A proof of nonautomaticity must be infinite (for instance the first-record/pumping lemma); a yes answer must give actual finite kernel closure. No PROOF.md, Lean, manuscript, nomination or discovery credit is produced.
