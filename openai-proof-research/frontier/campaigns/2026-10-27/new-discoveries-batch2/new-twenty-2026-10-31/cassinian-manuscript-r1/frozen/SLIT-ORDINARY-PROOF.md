# MathDB 331705: a planar slit-domain refutation

Status: full ordinary proof and full Lean endpoint; ZERO accepted credit. Root review and journal-version comparison remain outstanding. Counts stay 12/20 beyond 39.

Source: Klén–Mohapatra–Sahoo, arXiv:1511.01298v1, Section 1 definition and Conjecture 4.7. A proper domain G starlike with respect to x is conjectured to have every Cassinian ball B_cG(x,r), r>0, starlike about x. The Cassinian distance is sup over boundary points p of |x-y|/(|x-p||y-p|). Source topological compactification includes infinity, whose contribution is zero. The Lean lemma infinity_contribution proves insertion of this zero leaves the supremum unchanged whenever the nonempty finite-boundary values are bounded above. The concrete values used below satisfy those conditions. Complex numbers carry the ordinary Euclidean-plane norm, not the product supremum norm; norm_sq proves the coordinate identity.

Let G = C \ [1,infinity), x=0, y=4+i, z=y/2=2+i/2 and r=7/4. The slit is closed, G is open, contains zero, is proper and is star-convex about zero. Indeed multiplying a point outside the slit by t in [0,1] cannot put it on the slit: a nonzero imaginary part stays nonzero when t>0; a real point less than 1 stays less than 1. A nonempty star-convex set is path-connected and hence connected. G is dense (points on the slit can be perturbed by arbitrarily small positive imaginary increments), so its boundary is exactly the slit. These facts are all kernel-checked.

For p=s>=1 on the boundary, the squared denominator for y is

    P(s)=s^2((s-4)^2+1).

For every s>=1, P(s)>68/9. One elementary certificate splits [1,infinity) at 5/4,2,3. The four intervals give respectively P(s)>=137/16, P(s)>=125/16, P(s)>=8, P(s)>=9. Each exceeds 68/9. Since |y|^2=17, every boundary ratio is at most 3/2. Thus their supremum is at most 3/2<7/4, proving y is in the ball. Using the uniform 3/2 bound, rather than pointwise strict inequalities at r, avoids an unjustified strict-supremum inference.

For z, the single boundary point p=2 gives ratio |z|/(2*(1/2))=sqrt(17)/2>7/4. All boundary ratios for z are bounded above by 2|z|, since |p|>=1 and |z-p|>=1/2. Therefore the real supremum is well-defined and at least the p=2 value. Hence z is outside the ball. The ball contains y but excludes y/2, so is not star-convex about its center. This is a counterexample to the universally quantified source conjecture in dimension 2; it is neither an endpoint/radius correction nor an adjacent convexity question.

Lean: formal/Cassinian.lean, Cassinian331705.counterexample and Cassinian331705.source_refutation. SourceClaim writes the planar source assertion directly using IsOpen, IsConnected, properness, positive radius, StarConvex and the actual boundary supremum. Refuting this dimension-2 assertion refutes the source assertion for arbitrary n. The certificate includes the semantic topology and supremum bridges; the numerical script is not used by Lean.

Bounded prior-art work: original body; arXiv:1412.4035, 1504.01923, 1603.00590 (especially Section 7 and Section 11), 1511.05673; live author catalogue search; exact conjecture/phrase searches; live GitHub HEAD and complete scoped Omega D5/Problems path screens. The source author's 1603.00590 Theorem 7.1 controls local radial growth and its Section 11 discusses monotonicity for several other metrics; it does not supply this Cassinian refutation. No inspected theorem implies the slit counterexample as an immediate stated special case. This is bounded evidence, not a worldwide priority claim.

Material limit: the 2017 Math. Nachr. version DOI 10.1002/mana.201600117 returned HTTP 403 and was not read. The author catalogue was available through the web-search connector but direct HTTP returned 503. No denied route was retried or bypassed. A monograph (Hariri–Klén–Vuorinen, Conformally Invariant Metrics and Quasiconformal Mappings) is an additional unread framework lead. These are explicit root-review issues; no novelty acceptance is asserted.
