# MathDB 374488: a source-theorem consequence, recommended zero credit

Primary body: arXiv:2604.27868, Section 5.2, display (11), Proposition 5.25 and its proof, and Section 5.3 Conjecture 5.28. The downloaded PDF and receipt are in sources/. This is an ordinary mathematical deduction, not a formal endpoint.

Put k=d-2. The source gives a linear isomorphism from P_d to
L = {(x,y,z) >= 0 : x_i+y_i+2z_i-z_{i-1}-z_{i+1}=2 for 1<=i<=k},
with z_0=z_{k+1}=0. Proposition 5.25 proves that its vertices correspond bijectively to choices of one nonzero coordinate in each triple (x_i,y_i,z_i), with every one of the 3^k choices realized and all chosen coordinates strictly positive.

No point of L can have an entire triple zero: the corresponding equation would say -z_{i-1}-z_{i+1}=2. Conversely a prescribed set Z of coordinates can vanish at a point of L whenever Z does not contain an entire triple: extend Z in each triple to two zero coordinates and use the vertex supplied by Proposition 5.25.

Every nonempty face of a bounded polyhedron given by nonnegative coordinates and affine equalities is the intersection with a set of coordinate hyperplanes. This follows by taking a relative-interior point of a face and its active inequalities. The intersection with any allowed set Z has precisely those coordinates identically zero: for a coordinate c outside Z, choose a vertex obeying Z with c the nonzero coordinate in its triple. The vertices so obtained also show that distinct allowed Z define distinct faces. Inclusion of faces reverses inclusion of Z.

For a product of k triangles the same description holds: each triangle has three barycentric coordinates; a nonempty face sets an arbitrary proper subset of those three coordinates to zero. The two face lattices, with the empty face adjoined, are therefore isomorphic. This proves the printed combinatorial-equivalence assertion from the source's own vertex theorem and the elementary active-inequality description of faces.

The diagnostic script ferrers.py independently constructs all 3^k vertices for 1<=k<=10 (d<=12), checking strict support and every equation. It does not enumerate a face lattice; its displayed f-vectors are predicted coefficients of (3+3t+t^2)^k, not independently computed face counts.

Recommendation: exclude as a routine consequence with this explicit bridge. Root decides eligibility. No new significant discovery or Lean packet is claimed.
