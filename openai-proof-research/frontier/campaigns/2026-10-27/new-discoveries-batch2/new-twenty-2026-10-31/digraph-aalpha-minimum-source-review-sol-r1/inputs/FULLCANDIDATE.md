# 350767 — author ordinary full-scope proposal, SCIENTIFIC HOLD

No independent PASS, novelty/significance clearance, formal execution, acceptance or credit. This is the author's complete ordinary argument for the cached literal, not a qualified discovery. No dispatch. The final original work is now closed after the guard failure documented in NETWORK-STOP.md. All original receipts remain unchanged.

## Exact endpoint and source
For every integer n>=5 and every real 0<=alpha<1, among finite simple strongly connected digraphs of order n, the second, third and fourth smallest A_alpha spectral radii are attained uniquely up to isomorphism by theta(0,1,n-3), theta(1,1,n-4), theta(0,2,n-4), respectively. A_alpha=alpha D_out+(1-alpha)A. The smallest is the directed cycle. This matches cached MathDB 350767 and Xi-Wang 2105.10903v1 Conjecture 3.7, p11. A theta(a,b,c) has two internally disjoint paths from w to v with a,b internal vertices and one return path with c internal vertices; a<=b, a+b+c+2=n. Simplicity excludes a=b=0. Opposite arcs are permitted, loops and repeated arcs are not.

Actual acquired PDF SHA256 2405275e406ea88ab7b65ff7c8a4078900fe3940db97fb53bdded9fa8b598b98; URL https://arxiv.org/pdf/2105.10903. Definitions pp1-3, equations/Lemmas 2.1-2.9 and Theorems2.10/2.12 pp4-8, complete proof of Theorem3.4 pp8-11 and Conjecture3.7 read as extracted text. Figures and exact final glyphs have NOT been visually inspected. Original paper pp12 onward read only partially, not a whole-body audit. The final DOI was identified by live search as 10.7153/OAM-2022-16-67; no final body acquired. This proposal cannot establish final-version equivalence.

## Scalar coordinates and all bicyclic cases
Put d=1-alpha>0, a=alpha/d, and t=(lambda-alpha)/d. Every noncycle strongly connected graph has 1<lambda<Delta_out unless all row sums equal; in the graphs below the maximum is 2 and the minimum is 1, so 1<lambda<2. The Perron equation at the degree-two branch also gives s=t-a=(lambda-2alpha)/d>0. Along a degree-one directed path, consecutive Perron coordinates satisfy t x_i=x_next.

For a theta(A,B,C) of order m, elimination therefore gives
  s = t^{-(A+C+1)}+t^{-(B+C+1)}
    = (t^A+t^B)/t^{m-1}.
For an infinity(k,l), two cycles of lengths k+1,l+1 sharing only their branch, order m=k+l+1, it gives
  s = t^{-k}+t^{-l} = (t^k+t^l)/t^{m-1}.
Each right side is strictly decreasing for t>1; the left side t-a is strictly increasing. Thus pointwise comparisons of these right sides give strict comparisons of their unique Perron roots. Existence is supplied by the positive Perron vector; no arbitrary polynomial-root selection is assumed.

For theta graphs on n>=5 vertices the three smallest numerators, strictly in order, are 1+t, 2t, 1+t^2. Indeed B>=1; if B=1 then A is 0 or1, and all remaining pairs have B>=2, A>=0, giving numerator>=1+t^2 with equality only A=0,B=2. The differences are t-1 and (t-1)^2. Every infinity graph lies strictly above the third: k+l=n-1>=4. If min(k,l)=1 then the numerator is at least t+t^3>1+t^2; otherwise it is at least 2t^2>1+t^2. These prove the bicyclic ordering directly, without importing the source's separate rank-order theorem.

For any order m>=3 the minimum bicyclic radius is that of theta(0,1,m-3): every infinity numerator is >=2t>t+1, and every theta numerator >=t+1. Increasing m decreases this minimum. At order n-1 its right side exceeds the right side of theta(0,2,n-4) of order n, because, on the common denominator t^{n-1},
  t(t+1)-(t^2+1)=t-1>0.
Consequently ANY strongly connected bicyclic subdigraph of order m<n already certifies a radius above the proposed fourth graph. A proper subdigraph has strictly smaller radius than the original strongly connected graph: extend its nonnegative matrix by zero rows/columns; it is entrywise dominated by A_alpha(G), and irreducibility plus a strict entry gives strict Perron monotonicity. This also handles extra vertices and alpha=0.

## Parameter-free structural reduction
Every noncycle strongly connected simple digraph contains a strongly connected bicyclic subdigraph. Take a shortest directed cycle C. If it used all vertices and there were an extra arc, that arc and a segment of C would produce a shorter cycle. Hence unless G=C_n there are vertices off C. Strong connectivity provides a directed ear leaving and returning to C with all internal vertices outside C (choose a shortest such excursion). Its union with C is an infinity graph if its endpoints coincide and a theta graph otherwise.

If such a subgraph has order less than n, the preceding comparison settles G. If it spans, an infinity or any theta other than the first two candidates likewise settles G. It remains to consider a spanning exceptional theta with extra arcs. Here is the elementary arc reduction in the source proof of Theorem3.4, restated with corrected parameter-independent use; its arc/path assertions do not use alpha<=1/2.

First exceptional theta: vertices w,u,v,z_1,...,z_m, m=n-3>=2; arcs wv,wu,uv,vz_1,z_1z_2,...,z_mw. Any additional arc other than u z_1 or z_m u produces either a bicyclic subgraph on fewer vertices or a spanning theta outside the first two types. To check the exhaustive list of possible nonarcs, group them as follows:
* vw, vu, uw: use the new shortcut as one of the parallel paths; vw omits u, and vu/uw produce theta(0,n-2,0).
* u z_j (j>=2), or z_i u (i<=m-1): use the new arc as a direct parallel path. The other parallel path runs through v or w, respectively. Their internal counts are (0,j,m-j+1), or (0,m-i+1,i); each has its longer forward path at least2.
* w z_j, or z_i v: the same shortcut construction omits u, hence has order<n.
* z_i w (i<m), or v z_j (j>=2): shorten the return chain of the original theta, giving a bicyclic graph of smaller order.
* z_j z_i with j>i: the new backward arc and the original return route through w,v produce a theta omitting u. An extra forward arc z_i z_j with j>=i+2 shortens the return chain.
These groups exhaust all ordered distinct pairs not already arcs, apart from u z_1,z_m u. If both exceptions are present, the theta with branch u and terminal z_1 uses u z_1 and u v z_1, returning via the chain to z_m u; it omits w. If exactly one is present, it is G'_n or an isomorphic/reversed version with the same equations below. Extra arcs that already fall in another group settle the graph by monotonicity, so only the single-exception graph needs comparison.

Second exceptional theta: vertices u,w,b,v,z_1,...,z_m, m=n-4>=1; arcs uw,wv,ub,bv,vz_1,...,z_mu. Apart from wb and bw, all additional arcs give a smaller-order bicyclic graph or a spanning nonexceptional theta:
* wu,vw,bu,vb give a direct parallel path with the long route through the return chain; vu shortens the original theta to four vertices; uv omits one of w,b.
* w z_j or b z_j: use the new shortcut as the direct path, the old route through v as the other path, and return through the z-chain and u. This produces theta(0,j,m-j+1), omitting the other branch vertex and having order n-1. The cases z_i w or z_i b likewise use the shortcut and the return route and omit the other branch vertex.
* v z_j for j>=2, u z_j for all j, z_i v for all i, z_i u for i<m, and nonconsecutive forward/backward arcs on the z-chain all give a theta on fewer vertices, by shortcutting a chain or omitting one branch vertex.
Every remaining ordered pair is either an existing arc or wb,bw. Both wb and bw give theta(0,n-2,0). One alone is G'_n: for wb, relabel (w_first,u_first,v_first,z_1_first)=(u,w,b,v) in the first exceptional model; bw is symmetric. This verifies the structural reduction without a small-instance computation. For m=1 the empty index ranges are simply absent.

## The new all-alpha comparison
G'_n has the first exceptional theta's arcs plus u z_1. Let L be its Perron root and use t=(L-alpha)/d, s=(L-2alpha)/d. Its degree-one chain gives x_v=x_w/t^{n-2} and x_{z_1}=x_w/t^{n-3}. The two degree-two equations are
  s x_u=x_v+x_{z_1},  s x_w=x_v+x_u.
Eliminating the positive x_w yields
  s^2 t^{n-2}=s+t+1.                     (E)
Here t>1 and 0<s<=t, since alpha>=0. The fourth theta's root equation is q(t)=s t^{n-1}-t^2-1=0. Evaluated at G'_n, (E) gives exactly
  q(t)=t(t+1)/s-(t^2-t+1).
If 1<t<2, use s<=t to obtain q(t)>=2t-t^2>0.
If t>=2, then n-2>=3 and (E) imply
  s^2 <=(s+t+1)/t^3 <=(2t+1)/t^3<1,
since t^3>2t+1 for t>=2. Thus s<1 and q(t)>t(t+1)-(t^2-t+1)=2t-1>0.
Finally q(t)/t^{n-1}=(t-a)-t^{-(n-3)}-t^{-(n-1)} is strictly increasing on t>1. Hence positivity means L is strictly greater than the fourth theta's Perron root. This covers every alpha<1, both t regimes, and n=5. The proof does not infer root order merely from polynomial sign without monotonicity.

Combining the structural reduction, this comparison and bicyclic ordering proves the claimed endpoint. The directed cycle's radius is1; every other strongly connected graph has radius>1 by irreducible row sums (if regular outdegree>=2 its radius is that degree). This completes the minimum-to-fourth ordering. Equality in each bicyclic numerator comparison gives precisely the stated theta isomorphism types, and every nonbicyclic graph was strictly larger than the fourth.

## Checks, limitations, strongest objections
All mathematics here was done personally, no program, numerical experiment, enumeration engine, CAS, solver or Lean. A provisional incorrect factorization of q in internal reasoning was discarded before this write; the displayed exact identity follows directly from (E) and has been re-expanded by hand. The structural arc table, characteristic equations, and source hypothesis alignment need independent adversarial checking, including every short-chain boundary. No independent proof review is claimed.

Significance positive case: a deliberately universal source conjecture is resolved over its full remaining real parameter interval, with exact graph minimizers, no endpoint or domain alteration. Contrary case: the entire source graph reduction is reused and only one source polynomial comparison is sharpened by a two-regime elementary estimate. This is a concrete routine-adaptation objection, not an objection from shortness alone. Root must adjudicate it; there is no self-credit. Current prior searches were bounded and returned no authenticated applicable proof for this exact conjecture; no-hits do not clear novelty. Final-source and current proof-registry actual-body checks remain unpaid after STOP. Full 96-family comparison is unpaid. Nothing here establishes a new-to-literature theorem or permits formal dispatch.
