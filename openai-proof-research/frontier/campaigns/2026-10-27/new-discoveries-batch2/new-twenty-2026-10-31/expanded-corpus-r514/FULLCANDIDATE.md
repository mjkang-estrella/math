# 323531: author ordinary full-literal negation, scientific HOLD

No independent PASS, qualified discovery, formal execution, acceptance, or credit is claimed. This is one prospective family. The claim concerns the deliberate arbitrary-hsop Strong Conjecture, not the Intermediate or Generic Strong Conjectures.

## Exact binding and source

The complete original record is originals/323531.jsonl; corpus-provenance.json binds original chunk/hash/one-based line/newline, raw line, raw JSON string token, and decoded UTF8 statement. Original primary acquired before denial: sources/parking.pdf, arXiv1205.4293v2 (15 September2012). Read Definition3.4 and surrounding multiplicity definition pp14–17, Strong Conjecture p17, Proposition4.4 and proof pp20–22, and dihedral coordinate convention Section5.1 p22. The literal requires for EVERY equivariant hsop of degree kh+1 exactly (kh+1)^rank distinct multiplicity-one points.

The official current abs record was acquired and inspected: v1/v2 listed, no journal reference observed in that record. This does not establish absence of a final. Search navigation identifies Journal of Algebraic Combinatorics40(2)(2014)417–473. The observed author fpark.pdf request failed TLS; this ENTIRE work1205.4293/allversions/2014final is closed to ALL NEW deliveries, including metadata/query/author/mirror/API/DOI/cache. No retry or bypass. The saved pre-denial v2 remains readable, not final-equivalence evidence.

Distinct primary sources/evidence.pdf is arXiv1504.06869v2 (15May2015), Evidence for parking conjectures. Read pp1–6 and full Section5 pp18–23: definition of hsop, explicit distinction between general hsops and the unique Cherednik-produced hsop, Theorem2.3, statements of Generic Strong versus Strong, and the actual reducedness Jacobian criterion and generic-path proof. Its generic proof assumes reducedness and does not exclude exceptional parameters. Table1 p2 nevertheless prints Strong for A2 at all k. This is a concrete contrary public claim requiring reconciliation, not a proof of novelty or a theorem-level exclusion. The final2017companion proof and original2014final remain unpaid. No current registry root can be refreshed because all four exact root artifacts have inherited504closures; searches are bounded navigation, not chronology or worldwide novelty clearance.

## Witness satisfying every printed standing hypothesis

Take W of irreducible real type A2=I2(3), rank2, Coxeter number h=3; take k=3. Use the primary Section5.1 complex coordinates x,y on the complexified real reflection representation. Write zeta for a primitive cube root. On V* the generators act by c.x=zeta*x, c.y=zeta^(-1)*y and s.x=y,s.y=x. The relations c^3=s^2=1, scs=c^(-1) give the order-six dihedral group. On the real locus y=conjugate(x), c is a nontrivial120-degree rotation and s a reflection, so this is a real irreducible reflection representation with Coxeter number3, not an arbitrary unrelated complex representation.

Define
 theta1=(x^10+3*x^4*y^6)/4,
 theta2=(y^10+3*x^6*y^4)/4.
Both are homogeneous of degree10=kh+1. Their respective rotation weights are1 and minus1 modulo3: 10=1 and4-6=-2=1 mod3; the other two weights are negatives. Reflection swaps them. Therefore x->theta1,y->theta2 extends linearly to a W-equivariant injection V*->C[V]_10: linear independence follows from their different pure monomials x^10,y^10. Their span is exactly a copy of V*.

Check the hsop condition over the WHOLE complex affine space. If theta1=theta2=0 and x=0, then y^10=0 and y=0; likewise if y=0. If xy!=0, divide the first equation by x^4 and the second by y^4:
 x^6+3*y^6=0 and y^6+3*x^6=0.
Substitution gives -8*y^6=0, impossible with y!=0 in characteristic0. Thus the common homogeneous zero locus is exactly the origin, the hsop condition in the actual primary definition (Evidence Section2.3). No positivity, Dunkl-annihilation, minimality, reality-of-all-complex-points or genericity hypothesis is printed. The witness even has paired real coefficients and respects the real structure. It is a genuine allowed hsop, not a singular common-zero degeneration that ceases to be an hsop.

## Full fixed-locus count: 46 rather than100

Let Z={(x,y) in C^2:theta1=x and theta2=y}. For every fixed point,
 0=y*theta1-x*theta2=xy*(x^3-y^3)^3/4.
The identity follows by the binomial cube expansion, without computation or an enumeration program.

There is exactly one origin. On the x-axis the nonzero fixed points satisfy x^9=4; on the y-axis they satisfy y^9=4. Each polynomial has nine distinct roots over C, since it splits, its derivative is9*t^8, and0 is not a root. Thus the two axes contribute18 nonzero points, disjointly.

Every remaining point has xy!=0 and x^3=y^3, hence x=zeta^j*y for exactly one j in{0,1,2}. Substitution gives theta1=x*y^9 and theta2=y*y^9. Both fixed equations are therefore equivalent to y^9=1. There are nine distinct nonzero roots y for each of the three distinct ratios, giving27 points. Conversely all these27 points satisfy the equations. The cases are exhaustive and pairwise disjoint; |Z|=1+18+27=46<100=(3*3+1)^2. Even the upper bound46 alone refutes the literal100-point assertion, so no local multiplicity theorem is needed for the negation.

## Second check: nonreduced point without algebraic root choice

The point (1,1) is fixed. Its Jacobian for Theta is
 [[11/2,9/2],[9/2,11/2]].
The radial vector(1,1) has eigenvalue10; the transverse vector(1,-1) has eigenvalue1. Consequently J(Theta)-I is singular. The fixed locus is finite by the exhaustive algebraic classification above, so the actual primary Jacobian criterion in Evidence Section5 applies: the isolated point is not simple. Alternatively its nonzero tangent vector immediately contradicts multiplicity-one in the local finite algebra. This check is independent of the root counts, though not an independent-agent review.

The source Proposition4.4 claim about points on reflecting flats is a substantive conflict: (1,1) lies on x=y. The printed proof restricts Theta-x to a one-dimensional flat and observes simple zeros THERE. That only proves nonzero tangential derivative along the flat. Our transverse derivative equals0 for Theta-I. Simplicity of a restriction does not imply ambient simplicity. This identifies a precise apparent failure, rather than treating the proposition as an unexamined subsumer. It does not authenticate a correction/final version or declare every later claimed result false.

## Sustained construction mechanism and failed shortcut

At degree7 (k2), a symmetric equivariant ansatz theta1=x*(a*x^6+b*x^3*y^3+c*y^6), with theta2 its swap, gives directional fixed equation (a-c)*xy*(x^6-y^6). Forcing a transverse repeated direction at x=y requires a=c; this produces a common scalar factor, destroying the hsop property. That tempting shortcut is invalid.

Degree10 has the larger ansatz theta1=x*(a*x^9+b*x^6*y^3+c*x^3*y^6+d*y^9), theta2 its swap. The directional factor is xy*(u-v)*[(a-d)*(u^2+u*v+v^2)+(b-c)*u*v], where u=x^3,v=y^3. Choose a=1,d=0,b=0,c=3 to get xy*(u-v)^3 without introducing a common homogeneous zero. Scaling by1/4 makes(1,1) fixed. This pays the failed-hsop objection explicitly. No polynomial program, solver, numerical test or finite enumeration was run.

## Scientific qualification and strongest opposing positions

Positive case: the printed universal conjecture deliberately quantifies over all hsops; a valid irreducible A2 witness with interior positive k is a full negation. The later companion itself calls general reducedness the outstanding purely algebraic obstacle. This is not repairing a missing odd-characteristic condition, graph endpoint, basis normalization or a vacuous small-n range. A special exceptional parameter is permitted by the very distinction between Strong and Generic Strong.

Opposing case: a conventional discriminant-collision construction may already be known, and the2015table specifically claims the A2 all-k case. A source correction or a fully applicable earlier result may settle its significance. No complete primary prior-result-to-this-witness bridge has been authenticated. Smallness, elementary algebra, or genericity alone is not a supported routine-adaptation exclusion. Conversely this packet does not assert that no public witness exists, that this witness was not printed earlier, or that source-final fidelity is cleared. The final2014closed source, the exact A2 assertion's actual earlier proof/correction, current public proof chronology and all96 accepted-family comparisons remain scientific HOLDs. Historical exact-key/scalar/sourceURL reconciliation found only the separate source-neighbor notes listed in history-matches.json; none settles this target.

Ordinary endpoint: author proposed complete cached-literal negation. Source-final: HOLD. Prior/novelty/significance: HOLD. Formal: not run, dormant only. Independent adversarial fidelity/proof/significance: not done. Acceptance/credit:0. Request for root consideration is for a separate clean independent ordinary/source review only; no automatic formal dispatch or acceptance.
