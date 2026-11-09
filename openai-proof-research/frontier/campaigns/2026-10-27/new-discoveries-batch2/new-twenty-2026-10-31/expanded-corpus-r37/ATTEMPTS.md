# Sustained mechanisms and stopping points

All three routes below are source-scope investigations. None is nominated. No Lean theorem or certificate was made. Primary-source hashes/dated successful HTTP receipts are in sources/{receipts,more-receipts,final-receipts}.json. Review of selected proof bodies is distinguished from an independent audit of every supporting theorem.

## 345398: full ordinary proof, excluded as a routine explicit bridge

Source: Mynhardt–Ogden, arXiv2002.01347, Conjecture1 (final section); journal version AJC78(3),413–433. Graphs are finite simple, without isolated vertices; edge-supercritical requires a nonempty complement and every missing edge lowers the optimum by at least2. A TRD function has values0,1,2, every zero adjacent to a2, and every positive vertex adjacent to a positive vertex. Weight is the sum.

First derive the repair rather than presume positivity from the numerical sensitivity bound. Fix a missing edge uv and a minimum TRD function h on G+uv. Cases (0,0),(0,1),(1,0) cannot use the new edge for either condition and would already be valid on G, contradicting strict decrease. If both endpoints are positive, removing uv leaves Roman domination intact; only u and v can lose positive support. For each endpoint that does, raise one of its old neighbors (necessarily zero) to1. This costs at most2, keeps both endpoints positive, and all newly positive vertices have their endpoint as positive neighbor. It cannot destroy any old domination/support condition. If labels are2,0, raise the zero endpoint to1 and, if it lacks positive support, raise an old neighbor to1. The2 endpoint already had an old positive neighbor because the added neighbor had value0. The only zero that could lose domination is now positive. Again cost<=2 and both endpoints become positive. The reversed case is symmetric. These constructions do not lower any label2.

Let k=gamma_tR(G), h have weight k'. Supercriticality gives k'<=k-2; the repaired function g has k<=weight(g)<=k'+2<=k. Equality throughout makes g minimum and positive at both endpoints. Every nonuniversal vertex is an endpoint of some missing edge, proving the desired support assertion there.

For completeness, any universal vertex v also has a positive optimum: if a chosen minimum already labels v positively, done. Otherwise Roman domination gives another vertex u labeled2. Swap labels at u and v. All zeros now see v; all remaining positive vertices see v; v sees another positive vertex, which exists because u previously needed positive support. Thus the weight is unchanged and v becomes positive. This handles the universal-vertex possibility without a vacuous supercritical convention.

**Prior-body check is decisive:** Lampman–Mynhardt–Ogden, Involve12(8)(2019),1423–1439, Proposition2.3 proof (saved roman2019.txt lines160–184) already gives precisely the two repairs, including the zero-to-one change and the positive endpoints. The new deduction is equality of two inequalities at a supercritical edge, then choosing an incident nonedge. This is a routine explicit bridge from an existing proof, excluded by campaign policy even though the2020 paper lists the support assertion as conjectural. No significance/novelty credit, no formalization investment. A short proof is not the reason for exclusion; the matching earlier repair is.

## 345029: cyclotomic root-count route, unresolved

Source Hong–Sommese1912.12253, Conjecture3 has THREE clauses: 2k-1<=N_n<=2^k-1; equality2k-1 for the first k odd primes; and monotonicity N_np<=N_np' for any primes p<p' not dividing n. All must remain in view; neither the first bound nor a parameter instance alone is a new full solution.

Read the squarefree/odd reduction, parity proposition, proxy Definition7 and Lemmas8–11, recurrence theorem and its geometric proof sketch. For odd squarefree n>1, Phi_n has no real roots and Phi'_n(0) is nonzero. Thus away from the artificial x=0 zero, D_n(x)=x Phi'_n(x)/Phi_n(x) detects exactly the desired roots. Taking the logarithmic derivative of Phi_np(x)=Phi_n(x^p)/Phi_n(x) gives

D_np(x)=p D_n(x^p)-D_n(x).

The source's sufficiently-large-p recurrence doubles the old number plus1; it does not supply the bound at small primes, equality at the smallest primes, or monotonicity between all primes. The transformed graph sends (x,y) to (x^(1/p),py); it preserves individual graph shape but does not preserve relative intersections with the original D_n graph. Pointwise order is not available: differentiating p D_n(x^p) with respect to real p on x>0 gives D_n(x^p)+p x^p log(x)D'_n(x^p), whose sign is uncontrolled on the relevant oscillation intervals. On negative x one must use the odd-power continuation -|x|^p; an ordinary real-power continuation would change scope.

Second route: use the Mobius product Phi_n(x)=prod_{d|n}(1-x^d)^{mu(n/d)}. Logarithmic differentiation expresses D_n as a rational function with denominator nonzero on (-1,1), except removable endpoint conventions. A Sturm certificate for its numerator could certify an exact finite counterexample with rational arithmetic. It would still need a Lean bridge identifying the numerator, excluding poles/artificial zeros and certifying the complete real root count (Gauss–Lucas or a separate exterior argument). General coefficient signs do not give the conjectured upper bound, because Mobius terms have both signs. No universal variation-diminishing lemma was obtained.

Finite diagnostic: exact SymPy cyclotomic polynomials, derivative gcd and exact real-root counts completed for n=3,5,15,21,33,39,51,57,105,165,195,231. Counts respectively1,1,3,3,3,3,3,3,5,5,5,5, all derivatives squarefree. Case231 completed at40.64CPU seconds; the next pre-case budget check stopped further cases normally, within the45CPU/55wall caps. Full stdout is retained. Completed rows are separately reconstructed, not extrapolated. These are12 finite diagnostic cases, not a proof/novelty screen or complete monotonicity sweep. No larger sweep was launched.

Remaining decisive mathematics: a uniform control of intersections of D_n and pD_n(x^p) under all odd prime additions, or a specific certified violating pair. Current recurrence requires a separation hypothesis and cannot be promoted to all primes. Lean would additionally require source cyclotomic semantics, all real-root-count bridges and an exact literal endpoint, none supplied. Park as hard, zero credit.

## 345435: continuous four-dimensional box mechanism, unresolved

Source Averkov–Borger–Soprunov2002.03065 Conjecture1.5 uses normalized volume (d! times ordinary volume) and its associated mixed volume. It asks for every d and1<=ell<=d, with Vol(K_i)>=1 and mixed volume m, the sharp maximum (m+ell-1)^d. Read the conjecture and Proposition6.1 proof: at an optimum all but possibly one participating volume can be normalized to1, and the outside bodies can coincide. This does not reduce arbitrary bodies to boxes. Known ell1 and d<=3 are uncredited.

Test the first potentially new d4,ell2 setting with four determinant-one boxes. Work initially in ordinary volume with sides
A=(t,t^-1,1,1), B=(t^-1,t,1,1), C=D=(c,c,c^-1,c^-1), t,c>0.
To match the source normalized convention, scale EVERY box by (1/24)^(1/4). The source normalized volume and normalized mixed volume of these scaled boxes equal the ordinary volume/mixed volume calculated below; homogeneity supplies the bridge in ordinary mathematics, not Lean.

Write s=t+t^-1>=2. The mixed-volume permanent formula gives
m=((s^2-2)/c^2+4s+2c^2)/12,
Vol(A+B)=4s^2.
The exact symbolic permutation expansion is checked in scripts/verify.py and box-diagnostic.json. By AM–GM in c^2,
m>=q(s)=(sqrt(2s^2-4)+2s)/6,
with equality c^4=(s^2-2)/2. This optimizes the entire continuous c-family, rather than only a finite grid.

There is no counterexample in this family. For s>=2, q(2)=1 and
q'(s)=(2s/sqrt(2s^2-4)+2)/6 >=(sqrt2+2)/6>1/2,
whereas the derivative of sqrt(2s)-1 is1/sqrt(2s)<=1/2. Hence q(s)+1>=sqrt(2s), and (m+1)^4>=4s^2. This exact family-wide inequality survives arbitrary anisotropy and explains why the first box shortcut fails. It proves no conjectured upper bound for general bodies, nor even all box matrices.

Remaining decisive lemma: for arbitrary d4 bodies A,B,C with normalized Vol(A)>=1,Vol(B)=Vol(C)=1, bound Vol(A+B) by (V(A,B,C,C)+1)^4. A permanent inequality would at best handle boxes; the Aleksandrov–Fenchel inequalities in the source are explicitly insufficient in general for sharp higher-dimensional control. Need a genuine mixed-volume inequality or non-box witness. No full-scope proof/counterexample and no Lean semantic library/endpoint. Park rather than certify a surrogate restricted-family theorem.
