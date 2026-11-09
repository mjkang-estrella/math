# PROOF.md - independent reconstruction for MathDB 352303

Reviewer: Claude Opus 5.5, high effort. Written BEFORE opening inputs/author-candidate.md and
inputs/author-formal-plan.md. The only pre-disclosure was the one-line mechanism in TASK.txt
("BH(T)=N(T)/n with N an explicit sum over edge pairs from the inverse edge Laplacian; both bounds; the
upper one by a pendant-path shift"). All algebra below is by hand; no CAS, program or enumeration was
used, as the task requires.

## Statement proved

For every tree T on n>=3 vertices (in particular every n>=5, the literal's range),

    BH(K_{1,n-1}) <= BH(T) <= BH(P_n),

with equality on the left iff T is a star and on the right iff T is a path (isomorphism).
Here BH(G) = n * sum_{i=2}^n lambda_i(G)^{-2}, as printed in source abstract and p.2. That printed form
agrees with (1/2) sum_u sum_v d_B^2(u,v) when d_B^2(u,v) = (e_u-e_v)^T (L^+)^2 (e_u-e_v): the double sum is
2n tr((L^+)^2) because 1 is in the kernel of L^+.

## 1. The edge-pair formula

Let T be a tree, n>=2, B the oriented vertex-edge incidence matrix, L=BB^T, M=B^T B. B has independent
columns (no cycles), so M is invertible of size n-1, and the nonzero eigenvalues of L are exactly the
eigenvalues of M. Hence sum_{i>=2} lambda_i^{-2} = tr(M^{-2}) = sum_{e,f} (M^{-1})_{ef}^2.

For an edge e let A_e be the component of T-e containing the head of e, a_e=|A_e|, and
x_e = 1_{A_e} - (a_e/n) 1. Then 1^T x_e = 0, and (B^T x_e)_f = x_e(head f)-x_e(tail f) is 0 for f != e (f lies
on one side of e) and 1 for f=e. With X the matrix of columns x_e: B^T X = I. The columns of X lie in
1^perp = range(B), so X = B Y for some Y, whence I = B^T B Y = M Y, Y = M^{-1}, X = B M^{-1}, and

    X^T X = M^{-1} B^T B M^{-1} = M^{-1}.

So (M^{-1})_{ef} = <x_e,x_f> = |A_e cap A_f| - a_e a_f / n. For e=f this is a_e(n-a_e)/n. For e != f the forest
T-e-f has three components: C_e (meeting only e), C_f (meeting only f) and a middle one. Reversing an edge
negates its x, so up to sign we may take A_e=C_e, A_f=C_f, giving |<x_e,x_f>| = |C_e||C_f|/n.

Define w(e,e)=a_e(n-a_e) and w(e,f)=|C_e||C_f| for e != f. Then, summing over ordered pairs of edges,

    BH(T) = N(T)/n,   N(T) := sum_{(e,f)} w(e,f)^2 = sum_e [a_e(n-a_e)]^2 + 2 sum_{ {e,f} } (|C_e||C_f|)^2.     (1)

Remark 1. w(e,f) is the number of unordered vertex pairs whose T-path uses both e and f. Thus
N(T) = sum over ordered pairs of vertex pairs of (number of edges common to the two paths)^2.

Remark 2 (an equivalent classical derivation). With Kelmans' forest formula for trees, c_{n-1}... in the
coefficient notation c_2=W(T)=sum_e a(n-a) and c_3=sum_{ {e,f} } |C_e| m |C_f| (m the middle size), Vieta gives
sum lambda^{-2} = (c_2/n)^2 - 2 c_3/n, i.e. BH = W^2/n - 2 c_3. The elementary identity
a(n-a) d(n-d) - n a m d = a^2 d^2 (with n=a+m+d) converts that into (1). So (1) needs no new idea.

### Checks of (1) against the source, by hand
* Star: every edge pendant, N=(n-1)^3+(n-1)(n-2)=n^3-2n^2+1, so BH=n^2-2n+1/n, as in source Thm 5.5(1) and p.10.
* Double star S(a,b), a+b=n-2, P=ab: central edge w=(a+1)(b+1)=P+n-1; pendant diag (n-1); pendant-pendant
  w=1 (all C(n-2,2) pairs, including across the centre); pendant at u with centre: w=b+1 (at v: a+1).
  N = (n-2)(n-1)^2 + (P+n-1)^2 + (n-2)(n-3) + 2[a(b+1)^2+b(a+1)^2]. With a(b+1)^2+b(a+1)^2 = P(n+2)+n-2 this is
  N = n^3-2n^2+1+P^2+4Pn+2P, so BH = n^2-2n+4P+(P+1)^2/n. This is exactly source Thm 5.1 (rendered p.9, viewed).
* Firefly F_{0,t,n-2t-1} (t legs of length 2, l=n-2t-1 leaves, one centre):
  N=4t(n-2)^2+(t+l)(n-1)^2+2[25 C(t,2)+t(n-2)^2+5lt+C(l,2)] = n^3+(5t-2)n^2-16tn+9t^2-6t+1, so
  BH=n^2-2n+[9t^2+(5n^2-16n-6)t+1]/n, exactly the source's second display in the proof of Thm 5.5(3) (p.13).
* P_4: N=52, BH=13; P_5: N=190, BH=38; both agree with the explicit spectra 2-2cos(k pi/n).

## 2. Lower bound and its equality case

In (1), a_e(n-a_e) >= n-1 with equality iff e is pendant, and |C_e||C_f| >= 1. Hence
N(T) >= (n-1)(n-1)^2+(n-1)(n-2) = N(K_{1,n-1}), with equality iff every edge is pendant. For n>=3 a tree
with every edge pendant is a star: a path with three edges would have a non-pendant middle edge. QED.

## 3. Upper bound

Shift. Let T be a non-path tree. Fix a root and take a vertex w of degree >=3 at maximum distance from the
root. Every child subtree of w is a path, and w has at least two children, so w carries two pendant paths with
p>=1 and q>=1 edges. Let R be T minus the non-w vertices of those two paths; R is a subtree containing w, on r
vertices, and r>=2 because deg w>=3. So n=r+p+q. Let T' be T with the q-path re-attached at the far end of
the p-path, so w carries a single pendant path of p+q edges. T' is a tree with exactly one fewer leaf.

Claim. N(T')-N(T) > 0. Precisely, with S := sum_{e in E(R)} s(e)^2, where s(e) is the size of the side of e in R not
containing w,

    N(T')-N(T) = (r-1) (pq/3) [ r(2p^2+2q^2+3pq+3p+3q+2) + 2pq(p+q) + 3pq + p + q ] + 2S pq(p+q+1).     (2)

Since r>=2, p,q>=1 and S>=1, (2) is strictly positive. No relation between p and q is used, and (2) is symmetric in
p and q, as it must be.

Derivation. For a path edge g let j(g) be the number of vertices on its leaf side. Write Q(l)=sum_{j=1}^l j^2.
(i) R-R pairs and R diagonals: every component size of T-e-f (e,f in R) is unchanged, since all path vertices sit in
    the component of w in both trees. Contribution to N(T')-N(T): 0.
(ii) e in R and path edge g: C_g has j(g) vertices and C_e has s(e) vertices (the side of e away from w), so w=s(e)j(g).
    j ranges over [p] disjoint-union [q] in T and over [p+q] in T'. Contribution 2S(Q(p+q)-Q(p)-Q(q)) = 2S pq(p+q+1),
    using Q(p+q)-Q(p)-Q(q) = sum_{k=1}^q ((p+k)^2-k^2) = sum_{k=1}^q (p^2+2pk) = pq(p+q+1).
(iii) Two edges on one path with j-values i<j: w=i(n-j); a diagonal is j(n-j). So the total over a path of length l is
    F_n(l) = sum_{j=1}^l (n-j)^2 a(j), where a(j) = j^2+2Q(j-1) = j(2j^2+1)/3.
(iv) One edge on each of the two paths in T: w = i j', with total 2Q(p)Q(q). No such pairs in T'.

Thus N(T')-N(T) = D(n) + 2S pq(p+q+1), where D(n) = F_n(p+q)-F_n(p)-F_n(q)-2Q(p)Q(q).

Cancellation. If r=1 then T and T' are both the path on n0=p+q+1 vertices, S=0 and N(T)=N(T'), so D(n0)=0. Only
F_n depends on n, and F_n(p+q)-F_n(p)-F_n(q) = sum_{k=1}^q [(n-p-k)^2 a(p+k) - (n-k)^2 a(k)]. With
n=n0+(r-1) and (n-j)^2-(n0-j)^2=(r-1)(2p+2q+1+r-2j),

    D(n) = (r-1) sum_{k=1}^q [ (c+2q-2k) a(p+k) - (c+2p+2q-2k) a(k) ],   c := r+1.

Using a(p+k)-a(k) = p(2p^2+6pk+6k^2+1)/3 and 2p a(k) = (p/3) 2k(2k^2+1), the bracket equals (p/3)[(c+2q-2k)(A+6pk+6k^2) - 2k(2k^2+1)]
with A=2p^2+1. Put B = sum_{k=1}^q (A+6pk+6k^2) = qA+3pq(q+1)+q(q+1)(2q+1). Then, with sum k = q(q+1)/2, sum k^2 = q(q+1)(2q+1)/6 and
sum k^3 = q^2(q+1)^2/4,

    G := sum_k [...] = (c+2q)B - A q(q+1) - 2pq(q+1)(2q+1) - 4q^2(q+1)^2 - q(q+1)
       = cB + A q(q-1) + 2pq(q+1)(q-1) - q(q+1)(2q+1)
       = rB + A q^2 + pq(q+1)(2q+1)
       = q [ r(2p^2+2q^2+3pq+3p+3q+2) + 2pq(p+q) + 3pq + p + q ].

Therefore D(n)=(r-1)(p/3)G, which is (2).

Hand checks of (2), computing both sides directly from (1):
* K_{1,3} -> P_4 (r=2,p=q=1,S=1): (1/3)39+6 = 19 = 52-33.
* S(2,1) -> P_5 (r=2,p=2,q=1,S=1): (2/3)75+16 = 66 = 190-124, where 124=5*24.8 by source Thm 5.1.
* Spider (2,2,1) -> P_6 (r=2,p=q=2,S=1): direct N=337 and 553; (2/3)264+40 = 216 = 553-337.

Conclusion. Each shift lowers the number of leaves by exactly one and strictly raises N. A tree with two leaves is a path,
so after finitely many shifts we reach P_n, and N(T)<N(P_n) for every non-path T. By (1), BH(T)<BH(P_n). QED.

## 4. Scope

The proof pays both inequalities, both equality characterizations and all n>=5 of the literal (and n>=3 throughout). No
hypothesis on diameter, degrees or p versus q appears. Status: an independent ordinary proof; it is not a certificate and no
formal tool was run. Nothing here addresses novelty or significance.
