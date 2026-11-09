# PART B. MathDB 352303: extremal biharmonic index of trees, full conjecture

Source: Z. Lin, The biharmonic index of connected graphs, arXiv 2110.09931v1 (only version listed), Conjecture 5.3,
with BH(G)=n sum_{i>=2} 1/lambda_i^2. Literal matches source: n>=5, both bounds, both equality clauses.

## B1. Exact formula

For an edge e of a tree T let a_e,b_e be the sizes of the two components of T-e. For distinct edges e,f let alpha(e;f)
be the number of vertices of the component of T-e not containing f. Define
    N(T) = sum_e (a_e b_e)^2 + 2 sum_{unordered e != f} (alpha(e;f) alpha(f;e))^2.

Theorem 1. BH(T) = N(T)/n.

Proof. Let B be the oriented vertex-edge incidence matrix; L=BB^T and M=B^TB is positive definite on R^{E} because B has
full column rank for a tree. The nonzero eigenvalues of L are those of M, so sum 1/lambda_i^2 = trace(M^{-2}) = ||M^{-1}||_F^2.
For each e let x_e equal b_e/n on the a_e-side and -a_e/n on the other side, signs chosen so x_e differs by exactly 1 across e
in the orientation of e and is constant across all other edges. Then B^T X = I. Each x_e has zero coordinate sum, so X=BY and
Y=M^{-1}, hence X^TX=M^{-1}. Direct calculation: <x_e,x_e>=a_e b_e/n. For e != f, with outer sizes a=alpha(e;f), b=alpha(f;e) and
middle c=n-a-b, <x_e,x_f>=+-(ab/n^2)(-(n-a)-(n-b)+c)=-+ab/n. Square and sum. QED
Check against source Theorem 5.1: for S(a,b) with P=ab this gives N/n = n^2-2n+4P+(P+1)^2/n, the printed value.

## B2. Theorem

For every tree T on n>=3 vertices, BH(K_{1,n-1}) <= BH(T) <= BH(P_n), with equality on the left iff T is the star and on the
right iff T is the path.

Lower bound. a_e b_e>=n-1 with equality iff e is pendant, and alpha(e;f)alpha(f;e)>=1. So N(T)>=(n-1)^3+(n-1)(n-2), which is N
of the star, and equality forces every edge pendant, i.e. the star.

Upper bound. Let T be a non-path. Root T at a leaf and take a vertex v of degree >=3 at maximum depth. Then v has at least two
descending pendant paths of lengths p>=q>=1, and the rest R (containing v and its parent) has r>=2 vertices. Let T' be T with the
last vertex of the q-path moved to the end of the p-path, so (p,q) becomes (P,q-1), P=p+1>q. Put t=r-1>=1, so n=P+q+t.
Let Phi(m)=1^2+...+m^2, S=sum_{e in E(R)} s_e^2 where s_e is the size of the component of T-e not containing v.

Decompose N. R-R pairs: if an outer side avoids v it is inside R, otherwise it contains both paths and has size depending only on
R and p+q. So the R-R part is unchanged. Pairs (e in R, A_i): (s_e i)^2, giving S Phi(p) and similarly S Phi(q). Path edges with
outer size i: diagonal (i(n-i))^2; within a path i<i' gives (i(n-i'))^2; across paths (ij)^2. Hence
    N = C_R + 2S(Phi(p)+Phi(q)) + F(p)+F(q) + 2 Phi(p)Phi(q),
F(m)=sum_{k=1}^m (n-k)^2 U(k), U(k)=k^2+2Phi(k-1)=k(2k^2+1)/3.

Then N(T')-N(T) = 2S(P^2-q^2) + (n-P)^2U(P) - (n-q)^2U(q) + 2[P^2 Phi(q-1) - q^2 Phi(P-1)]. With n-P=q+t, n-q=P+t,
the t-free terms cancel identically (this is the fact that for t=0 the two shapes are the same path), leaving
    N(T')-N(T) = (P^2-q^2)(2S + (4/3) t P q) + t^2 (U(P)-U(q)) > 0.
Thus no non-path maximizes N among the finitely many n-vertex trees, so the path is the unique maximizer. QED

## B3. Attempt to find a generic proof or a reduction, and what happened

1. Laplacian coefficient monotonicity (Mohar 2007; Csikvari tree shift, recalled from memory, bodies not read here): sum 1/lambda^2 =
   (W/n)^2 - 2 c_{n-3}/n is a DIFFERENCE of two quantities that both increase toward the path, so coefficient monotonicity does not imply
   the result. I could not derive it from them.
2. Majorization: the path spectrum does not majorize that of the star; Schur-convexity goes the wrong way at the small eigenvalues.
3. One-parameter family: the same shift calculation appears to extend to the abstract sums sum (alpha alpha)^k, but only k=2 is spectral
   for the entrywise squares, so there is no spectral family containing the target. I did not prove the abstract family and I do not claim it.
4. The inverse edge-Laplacian entries are classical (Merris-type edge versions of the Laplacian, recalled from memory, body not read), and
   pendant-path shifting is the standard chemical-graph-theory tool. STRONGEST OBJECTION: a one-page combination of an old formula and an
   old transformation. No complete prior result-to-target bridge was found in the one search made, which returned no proof.

## B4. Limits on B
One search only, with excerpts; no novelty claim. Published final of Lin's paper, if any, unread; arXiv listing shows v1 only, no journal
reference. Companion Wei-Li-Yang arXiv 2110.02656 (Problem 6.3) not read.

---------------------------------------------------------------------------------------------------
