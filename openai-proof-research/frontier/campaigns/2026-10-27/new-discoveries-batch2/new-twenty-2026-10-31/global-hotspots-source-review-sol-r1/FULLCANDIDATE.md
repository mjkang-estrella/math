# Full ordinary candidate: MathDB346033
Status: independently checked ordinary proof relative to the verified v4 source model and Marker Theorem 3.5. NOT an accepted or fully qualified campaign candidate. Final-journal-body, bounded prior, substantive-credit and Lean gates remain open. Included as a complete reviewable mathematical candidate, with a dormant plan, without dispatch or credit.

## Exact scope and dependencies
For every compact connected finite metric graph Gamma with finitely many positive finite length edges, including loops and parallel edges, take the standard continuity-Kirchhoff Laplacian of Kennedy-Rohleder Section 2.2. For its smallest positive eigenvalue mu_2, let E be the entire REAL eigenspace and set
M = {x in Gamma : exists u in E, u != 0, forall y in Gamma, u(y) <= u(x)}.
The source's Section 2.3 identifies this with the union of both global maxima and minima of all second eigenfunctions, since E is closed under negation. The conclusion is that M has finitely many connected components and is finite or uncountable. No simplicity, genericity, algebraicity of lengths, uniform graph-size bound, or assertion about all local maxima is assumed.

Primary bodies: input/primary-hot.pdf, arXiv:2003.14335v4 (4 May 2021), Sections 2.1-2.3 pp4-8, Assumption 4.1 p10, Proposition 4.4 p11 and its proof p16, Conjecture 8.1 and following discussion p24. Finite multiplicity, positive mu_2, real eigenbasis, continuity, differential expression and vertex conditions are explicit in Section 2.2. Auxiliary: David Marker, Introduction to Model Theory, MSRI Publications 39 (2000), sources/marker.pdf, unnumbered definition of definability after Proposition 1.2 and parameter discussion pp17-18, Section 3 pp21-25, Theorem 3.5 and Corollary 3.7 pp24-25. This is a different author/work from unavailable Coste SAG; Coste is not used.

## Independent proof

1. **Finite real coordinates and the edge ODE.**
Fix Gamma. Write lambda=mu_2>0 and k=sqrt(lambda)>0. Its real eigenspace has finite dimension m>=1, so choose a real basis u_1,...,u_m. Source finite multiplicity justifies this directly. Alternatively, the map sending u to the pairs (u_e(0),u'_e(0)) on all edges is linear and injective, so dim(E)<=2|edges|: the differential equation determines each edge restriction from these initial values.

For precision the domain gives u_e in H^2 and u_e''=-lambda u_e almost everywhere; in one dimension u_e and u'_e have continuous representatives on the closed interval. The weak second derivative equals a continuous function, so integrating it shows u_e is C^2 up to each one-sided endpoint and satisfies the ODE there. Set a_ie=u_i,e(0), b_ie=u'_i,e(0)/k. Then
u_i,e(x)=a_ie cos(kx)+b_ie sin(kx).
One can verify uniqueness without assuming a spectral ODE black box: the difference w between the two sides solves w''+k^2 w=0 with w(0)=w'(0)=0; the derivative of (w')^2+k^2 w^2 is zero, hence w=0. Continuity at vertices makes all incident endpoint values agree. A loop's two endpoint evaluations therefore agree too; different edges remain separate intervals in the construction. Orientation affects only coordinate choices.

Every nonzero u in E is uniquely sum_i c_i u_i with c!=0. Divide c by its strictly positive Euclidean norm. Positive scaling preserves all global comparisons. Thus existential c may be restricted exactly to sum_i c_i^2=1. This is coefficient normalization; it is not necessary to assert that the basis is L^2-orthonormal. Conversely every such c is nonzero and represents a nonzero eigenfunction by linear independence. Negation of c includes minima. No zero function enters M.

2. **Finite closed charts with no poles.**
On an edge of length L>0 choose an integer N>=1 with kL/N<pi, and divide [0,L] into N equal closed subintervals. This is an ordinary Archimedean existence choice, not a numerical computation. For a subinterval [a,b] let z=(a+b)/2 and theta=k(x-z). Then |theta|<=k(b-a)/2<pi/2, which is strictly inside (-pi,pi). The map
t=tan(k(x-z)/2)
is a strictly increasing continuous bijection from [a,b] to [ell,r], with inverse x=z+2 arctan(t)/k, and is a homeomorphism. ell,r are finite real constants. All subdivision endpoints and all original edge endpoints are included. There are finitely many charts j overall, and their graph maps q_j:I_j -> Gamma are continuous and jointly surjective. At vertices these maps need not be injective across different charts, which is harmless.

For each chart define vectors A_j=(u_i,e(z))_i and B_j=(u'_i,e(z)/k)_i. The shifted ODE identity gives the evaluation vector
v_j(t) = (u_i(q_j(t)))_i = [A_j(1-t^2)+2B_j t]/(1+t^2).
This follows from cos(theta)=(1-t^2)/(1+t^2), sin(theta)=2t/(1+t^2). Define the vector polynomial N_j(t)=A_j(1-t^2)+2B_j t and D(t)=1+t^2>0. Every coefficient and interval endpoint is an arbitrary fixed real number. We never require these constants to be algebraic or to have a finite effective encoding as rational numerals.

3. **An exact polynomial formula for global M.**
For each j let S_j be defined by the following first-order formula over the ordered real field:
ell_j<=t<=r_j AND
exists c_1,...,c_m [
  sum_i c_i^2=1 AND
  conjunction over ALL charts h of
    forall s (
      (ell_h<=s AND s<=r_h) implies
      sum_i c_i [N_ji(t) D(s)-N_hi(s) D(t)] >= 0
    )
].
Finite conjunctions, finite sums and the displayed polynomials form an ordinary finite first-order formula, with real parameters. Chart labels are external finite indexes, not extra quantification over a variable number of functions or charts.

For t in I_j, this formula is equivalent to q_j(t) in M. In the forward direction its witness c defines one nonzero global eigenfunction. For an arbitrary y in Gamma, joint chart surjectivity supplies h,s with y=q_h(s), and division by D(t)D(s)>0 gives u(y)<=u(q_j(t)). Thus it is a GLOBAL maximizer. In the reverse direction write a witnessing eigenfunction in the basis and normalize its coefficients positively; all inequalities on all charts follow. Endpoints, isolated vertex maxima, remote tied maxima, and eigenfunctions vanishing identically on some edges are included. The witness c is chosen before the universal comparisons, so it is the same eigenfunction everywhere. Therefore
M = union_j q_j(S_j).
In fact S_j=q_j^{-1}(M) on I_j, including repeated endpoint representatives.

4. **Elimination with arbitrary real parameters.**
Place all of the finitely many A,B,ell,r constants into a tuple p. Regard the displayed formula initially as phi(t,p), in the usual ordered-ring language, with p as free variables. Marker Theorem 3.5 provides an equivalent quantifier-free formula psi(t,p) for every real tuple p. Specialize to the actual tuple p of this graph. No algebraic-number restriction occurs: this is specialization of free variables in R, not invoking decidability of arbitrary real constants. Marker explicitly defines sets with parameters and discusses real-parameter formulas; Proposition 1.3(viii) gives sections at arbitrary tuples. Thus S_j is semialgebraic over R.

5. **One-dimensional finiteness, independently unpacked.**
A quantifier-free formula contains finitely many univariate real polynomials after specializing p. Discard identically zero polynomials from its root list, evaluating their atomic statements as constant truth values. Every remaining polynomial has finitely many roots (by the factor theorem and induction on degree). The union R_j of their real roots is finite. On each interval component of R minus R_j, each polynomial is continuous and never zero; the intermediate value theorem makes its sign constant. Hence the whole Boolean formula is constant on that interval. At roots it independently selects or rejects individual points. Consequently S_j is a finite union of intervals and singletons, with endpoint choices included. Since it is restricted to [ell_j,r_j], there are no points outside that interval. This also follows directly from Marker Corollary 3.7. No multivariable finite-component theorem or root enumeration is needed.

6. **Transfer and gluing.**
For each of the finitely many connected intervals or singletons C in this decomposition, q_j(C) is connected, by continuity of the inverse coordinate map followed by the edge inclusion. Their finite union is exactly M. Any nonempty connected piece is contained in one connected component of M; each component contains a point and hence at least one such piece. Thus the number of components is at most the finite number of pieces. Intersections at chart subdivisions or vertices can only merge pieces into components. Closedness of the intervals is unnecessary, and topology at a loop endpoint or higher-degree vertex causes no exception. This proves Conjecture 8.1.

7. **Finite or uncountable.**
If all finitely many connected components are singletons, M is finite. Otherwise a component C contains distinct points x,y. The continuous real function z -> dist(x,z) has connected image on C containing 0 and d=dist(x,y)>0. Its image therefore contains [0,d], which is uncountable. Thus C, and hence M, is uncountable. This argument does not assume path-connectedness of arbitrary components or closedness of M.

As an optional check, the global-maximizer relation is closed in the compact product of the coefficient unit sphere and Gamma: joint evaluation is continuous, so each comparison u_c(x)>=u_c(y) defines a closed set. Intersection over y stays closed. Projection to Gamma is compact, so M is compact. This optional conclusion is not used to manufacture the finite-component property.

## Objections and scope limits
Finite components for M_loc cannot imply the result for its subset M; step 3 supplies the missing global control. Restricted analytic sinusoids are not claimed to be semialgebraic in the original length coordinate. The rational chart and its homeomorphic inverse are all that is needed. The proof is for each fixed graph separately; no uniform chart count or degree bound across graphs is asserted. No numerical eigenvalue calculation or algorithm for arbitrary real parameters is claimed. The proof does not settle Question 8.2 (finite or whole graph), bridge finiteness, or geometric location conjectures.

The only non-elementary general external theorem used after the source spectral setup is real-closed-field quantifier elimination, now supported by an actual lawful primary body. The reduction itself is supplied in full rather than presumed from that theorem. Formal certification remains completely unpaid.

