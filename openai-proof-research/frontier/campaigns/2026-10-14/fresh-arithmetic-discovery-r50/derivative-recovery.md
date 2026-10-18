# Exact derivative recovery, and a false sufficient second-moment bound

The parent suggested examining this recovery route. The identity itself is the biased version of Harsha–Klivans–Meka's Section8 reduction; their actual primary PDF/extracted text852–976 and145–180 were read during this continuation. No new attribution is claimed for the identity or the Cauchy reduction.

Set Q_i=(P(X_{-i},+1)-P(X_{-i},-1))/2 and g_i=sign(Q_i), with sign(0)=+1. Let Y_i=(1_{Xi=+1}-p_i)/sqrt(p_i(1-p_i)); define S=sum_i Y_i g_i. Conditional on all other coordinates, E[f Y_i]=sqrt(p_i(1-p_i))(f(+)-f(-)). If the endpoints differ, their orientation equals sign(Q_i), including either zero endpoint under the stated sign convention. If Q_i=0 they cannot differ. Therefore exactly

W:=sum_i sqrt(p_i(1-p_i)) I_i=(1/2)E[f S].

The diagonal terms in E S^2 sum to n. For i!=j, condition on all other coordinates and write Q_i=A+R Xj and Q_j=B+R Xi, where R is the common mixed derivative. Integration over Xi,Xj gives

E[Y_i Y_j g_i g_j | X_{-ij}]
 =sqrt(p_iq_i p_jq_j) (g_i(+)-g_i(-))(g_j(+)-g_j(-))
 =4sqrt(p_iq_i p_jq_j) 1_{A_ij}1_{B_ij}.

Here A_ij and B_ij mean that the respective derivative sign functions change across their remaining coordinate; the differences have the same sign as R whenever nonzero, and R=0 makes both zero. Thus all cross terms are nonnegative and

E S^2=n+8 sum_{i<j}sqrt(p_iq_i p_jq_j) Pr(A_ij intersection B_ij).

A bound E S^2<=C d^2 n WOULD suffice by Cauchy. It is FALSE, even at fair bias and degree two. This is a failure of a sufficient proof mechanism, not of T127N49.

## Exact counterexample to that sufficient bound

For every even n>=2 let Z=sum_i Xi with independent fair signs and take P=Z^2, whose multilinearization has degree2. One may instead take P=Z^2+epsilon for any epsilon>0 to remove zeros; the derivative signs are unchanged. Then Q_i=2 sum_{j!=i}Xj and g_i=sign(Z-Xi). Since Z is even, if Z>=2 every g_i=+1; if Z<=-2 every g_i=-1; and if Z=0 then g_i=-Xi. Consequently

S=|Z| when Z!=0, and S=-n when Z=0.

Write b_n=2^(-n) binom(n,n/2). The exact formulas are

E S^2=n+n^2 b_n,
E |S|=2n b_n,
E S=0.

For the middle identity use E|Z|=n b_n for even n, obtainable by telescoping k binom(n,k) terms on the positive half of the binomial law. Since b_n~sqrt(2/(pi n)), the second moment grows like n^(3/2), whereas the first absolute moment has the desired sqrt(n) scale. Here f=+1 everywhere, so W=0 and exact recovery retains complete cancellation. Bounding E[fS] through the raw second moment loses that cancellation.

## Actual closest primary comparison and remaining obligation

Harsha–Klivans–Meka, Theory of Computing10(1),2014, Theorem8.2 and Lemma1.7 proof, introduce derivative signs and the same uniform recovery. Their bound is (E|S|)^2<=2 sum_i AS(g_i)+n, obtained by passing through E S^2 and separate derivative sensitivities. Their introduction says that improving the FIRST-ABSOLUTE-MOMENT expression to O(n) when the g_i are linear threshold functions would imply the quadratic Gotsman–Linial bound. It does not claim the now-refuted raw second-moment bound. The PDF text has damaged absolute-value glyphs in places; the subsequent Cauchy step distinguishes the two quantities explicitly.

For the unchanged target, it would suffice to prove E|S|<=C d sqrt(n) uniformly over all product biases, but this stronger sufficient statement has not been established. It is not a replacement freeze or an asserted equivalent reformulation. Alternatively one might directly control E[fS] using integrability of the derivative field and its correlation with f. Separate source127 influence bounds, scalar restrictions, and the cross-filtration trace energy do not supply that joint estimate. No full target proof or full target counterexample is claimed.

Remark8.3 was also read: it gives a block-parity family showing the separate-influence Lemma1.7 estimate is sharp from those bounds alone. That higher-degree example is credited, and is different from the degree-two raw-second-moment counterexample above. Neither establishes or refutes T127N49.
