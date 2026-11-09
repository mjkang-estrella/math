# 349146: uniform ordinary construction draft, no Lean certificate

This is a second, UNFORMALIZED lead, not an accepted solution. Source Definitions 1–2 reduce the question to a balanced vertex labeling with a suitable number of crossing edges; orientations of distinct crossing edges can be chosen independently. Current arXiv v3 and the published Springer abstract retain the 3k+1 conjecture. The v1 arbitrary-bijection proof was not used. Literature on hypercube bisection spectra has not been exhausted, so eligibility is not cleared.

Here is a proposed complete ordinary construction for every dimension d = 3k+1. The small dimensions d = 1,4,7 are handled by the trivial edge and the explicit independently checked cut witnesses in outputs/cube-4.json and outputs/cube-7.json. The source itself also supplies dimensions 4 and 7. The argument below handles all d >= 10.

Write m=d-1, H=2^(m-1), M=d*2^m (the edge count of Q_d). Then 3 divides m and m>=9. Since M is divisible by 4 but not 3, define

z = 2 floor((M+2)/6),     C=M-z.

The integer z is even, C is even, C is 2 modulo 4, and the three desired arc counts (z,C/2,C/2) differ by at most 1. These assertions follow by writing M=12a+4 or M=12a+8. Also |C-2M/3| <= 1.

If m is odd put delta=0. If m is even put delta=2d-4=2m-2. Define

B = (C-delta-2^m)/2,     r=floor(B/m),     b=B-mr.

Here 0<=b<m. When m is even, B and b are even (because C and delta are both 2 modulo 4). Thus choose q=1 when m-b is even, and q=2 otherwise. In the second case m is odd and b is even. In both cases

t=(qm-b)/2

is an integer with 0<=t<=m and 1<=q<=2.

We first build an UNBALANCED cut of size B in Q_m. Let O and E be its odd- and even-parity vertex classes, each of size H. We will take a set consisting of r odd vertices S and q specified even vertices e_1,...,e_q. Choose the even vertices at pairwise distance 4, so their m-element neighbor sets are disjoint. Arrange S to contain exactly t vertices from the union of these neighbor sets. Then the cut size is

m(r+q)-2t = mr+b = B.

The required choices of S can be made with extra reserved zero-neighborhoods when needed:

- If delta=0, no reservation is needed. For q=2 choose e_1=000000... and e_2=111100...; their neighborhoods are disjoint.
- If delta>0, then m is even, q=1, and m>=12. Choose e_1=000000..., w_1=111100..., w_2=110011.... These three even vertices have mutual distance 4. Require S to avoid all 2m neighbors of w_1,w_2, while still containing exactly t neighbors of e_1. Let h be the indicator of S union {e_1}. Then h(w_1)=h(w_2)=0 and h is zero on every neighbor of either w_i.

Here are sufficient exact size bounds for these selections. For m>=9, H>=12m (base m=9 and induction by doubling). From |C-2M/3|<=1 and 0<=delta<=2m-2,

((2m-1)/3)H - m + 1/2 <= B <= ((2m-1)/3)H + 1/2.

Consequently H/2+1 <= B/m < 3H/4, hence

r >= H/2 >= 6m,     H-r >= H/4 >= 3m.

For the lower bound on B/m, subtract H/2+1 and use H>=12m: the difference is at least 2m-6+1/(2m)>0. The upper bound is immediate. Thus there are enough odd vertices to choose t in the specified neighbor union and r-t outside it. In the reserved case the specified union and the forbidden union contain m and 2m disjoint vertices, respectively; r-t <= H-3m follows from H-r>=3m. Without reservations, the weaker inequality r-t<=H-qm follows from H-r>=3m>=qm.

Now label Q_d = {0,1} x Q_m by

f(a,v) = a XOR h(v).

This is exactly balanced, independently of the size of h's support. Its crossing-edge count is 2^m + 2B = C-delta: all coordinate-a edges cross, and each Q_m crossing appears in both layers.

If delta=0 we are done. If delta>0, toggle the labels at x=(0,w_1) and y=(1,w_2). These vertices have opposite labels and are nonadjacent (their distance is 5), so balance is preserved. Each initially has exactly one crossing incident edge: its coordinate-a edge. Flipping each changes the crossing count by d-2; their nonadjacency means these changes add without correction. Hence the new crossing count is C-delta+2(d-2)=C.

The number of equal-label edges is now z. Orient exactly C/2 crossing edges from 0 to 1 and the other C/2 from 1 to 0; orient equal-label edges arbitrarily. The induced arc counts are precisely (z,C/2,C/2), proving cordiality.

Remaining work: adversarial ordinary proof review, classical cut-spectrum/subsumption search, and a full literal Lean endpoint. The arithmetic can be checked with a small integer script, and the set-selection construction can be explicitly materialized for dimensions 10 and 13; those checks are diagnostics, not a replacement for the general argument. This route uses a parity-class reservoir and a two-vertex repair, rather than the source's eight-copy induction, but that alone does not establish mathematical significance or novelty. No additional credit is claimed.
