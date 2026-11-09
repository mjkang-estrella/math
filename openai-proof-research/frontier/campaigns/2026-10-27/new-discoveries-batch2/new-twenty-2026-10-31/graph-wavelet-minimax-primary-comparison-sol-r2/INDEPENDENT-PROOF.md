# Independent ordinary proof, original-v1 endpoint only

This is personal ordinary mathematics, with no mathematical execution. The author and r1 arguments were proposals to inspect; no theorem from them is assumed. Scientific priority and successor fidelity are separate.

Let V={1,...,8}, A={1,2,3}, B={4,...,8}. Join all distinct pairs within each of A and B and add only the edge {3,4} between them. This is a finite simple connected unweighted undirected graph. Delta has exactly one oriented row per undirected edge, with entries -1,+1. K=1 is allowed by Definition9. Set P={x in R^8: support(Delta x)<=1}. For an orthonormal 8-column real basis Q define M(Q)=max over P of support(Q^T x). The maximum exists because its values form a nonempty subset of the finite integer set {0,...,8}.

If two vertices u,v of either clique have different signal values, uv is inconsistent. For a third clique vertex w, at least one of uw,vw is inconsistent, or equality through w contradicts x_u != x_v. Thus there are at least two inconsistent edges. Consequently every x in P is constant on each clique. Conversely a1_A+b1_B has only the bridge possibly inconsistent. Therefore P={a1_A+b1_B: a,b real}, including all zero, constant, signed and cancellation cases.

Use m=1_V/sqrt8 and h=(5 1_A-3 1_B)/sqrt120. They have norm one and inner product zero, since 3*25+5*9=120 and 3*5-5*3=0. For each ordered clique v_1,...,v_s add its s-1 contrasts H_j=(sum_{i<=j} e_{v_i}-j e_{v_{j+1}})/sqrt(j(j+1)). Each has coordinate sum zero and norm one. For j<k, H_k is constant on the support of H_j, so their inner product vanishes. Contrasts from different cliques have disjoint supports. All are orthogonal to m,h. These eight orthonormal vectors are linearly independent by inner products and hence span R^8. Call this full basis F. It even contains the mandatory source mean, although the competitor constraint only requires orthonormality.

For every real a,b, F^T(a1_A+b1_B) has at most the two coordinates (3a+5b)/sqrt8 and 15(a-b)/sqrt120. With a=1,b=0 both are nonzero. Hence M(F)=2. For any full basis Q, signals of support at most one in Q lie in the union of its eight coordinate lines. Distinct vectors 1_A+t1_B are linearly independent in pairs, since the A coefficient is one and their B coefficients differ. Thus each line contains at most one such vector, whereas real t is infinite. Some member has Q-support at least two. Therefore M(Q)>=2 for all Q and min_Q M(Q)=2.

The explicit even hierarchy has root {1,2,3,4}|{5,6,7,8}, next children {1,2}|{3,4} and {5,6}|{7,8}, and then singleton children for each pair. Every child induces a connected graph; {3,4} uses the bridge. Each split has nonempty equal cardinalities, is disjoint and covers its parent. Process nonsingletons while any remain. Algorithm1 then gives columns
m;
r=(1,1,1,1,-1,-1,-1,-1)/sqrt8;
l=(1,1,-1,-1,0,0,0,0)/2;
t=(0,0,0,0,1,1,-1,-1)/2;
p12=(e1-e2)/sqrt2; p34=(e3-e4)/sqrt2; p56=(e5-e6)/sqrt2; p78=(e7-e8)/sqrt2.
Every contrast sums to zero, has norm one, and has disjoint or nested support with every other contrast. In the nested case the larger is constant on the smaller's support, so their inner product is zero. Thus these eight vectors independently form an orthonormal basis W.

For every x=a1_A+b1_B its ordered W-coordinates are
((3a+5b)/sqrt8, 3(a-b)/sqrt8, (a-b)/2, 0, 0, (a-b)/sqrt2, 0, 0).
So M(W)<=4. At x=1_A exactly four coordinates are nonzero, since all displayed denominators are positive. Hence M(W)=4>2=M(F), a strict actual worst-case comparison on the entire literal class. W cannot belong to the argmin, regardless of whether the printed equality to argmin was meant as uniqueness or minimizer membership.

Every perfectly even hierarchy fails, not just this one: on x=1_A the mean is nonzero; a 4|4 root contrast is (2q-3)/sqrt8 for an integer q, so is nonzero. Some root child contains both A and B vertices. The restricted indicator is nonconstant there. Its complete descendant orthonormal contrasts span the orthogonal complement of its constant vector, by the same nested/disjoint support proof. If every descendant coefficient vanished, the restriction would be constant, contradiction. Thus some third coefficient is nonzero and every even hierarchy has M(W)>=3>2.

Exact source bridge: original-v1 pp14-18, Definitions9/10, Eq7 discussion, Algorithm1, Theorem8 and complete proof, Theorem9 and proof, Corollary2, Conjecture1 and community caveat were inspected, with material PDF pages visually read. The actual admissible class is full R^N with unnormalized incidence support, and the basis contains the mean. Optional signal sparsity exclusions are not premises. Eq7 is explicitly ideal, followed by relaxed partition methods and permission to use other partition algorithms; Algorithm1 demands connected children, not exact Eq7 minimization. The example is not claimed to solve Eq7: its root has four crossing K5 edges and objective2, whereas the community cut has objective8/15. Adding exact Eq7 optimality would change the statement and invalidate this example for that changed class. It is absent from the actual conjecture.

Theorem9 and Corollary2 are not inputs. Their printed full-basis bounds miss the mean term: a nonzero constant has zero Delta support but one mean coefficient. This is distinct from the strict minimax refutation, which persists even if one imposes a shared mean. If the problem instead restricted both signals and coordinates to the mean-zero subspace, a=5,b=-3 spans P intersect mean-perp; F then has worst support1 and this W has support3. This is robustness only, not another family or credit.

No ordinary gap remains for the copied literal and original v1. No claim that the inaccessible successor thesis has the same definitions, theorem conclusions, proof or conjecture is made.
