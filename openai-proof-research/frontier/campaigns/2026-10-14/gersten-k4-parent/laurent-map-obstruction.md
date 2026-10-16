# A boundary for the local Laurent-symbol construction

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Supporting
ring calculation for the active G4 search, not a result-count nomination.

Let A be a local integral domain with maximal ideal m and choose
0 != a in m. Write B=A[z]_(m A[z]). The polynomial z+a is outside
m A[z], because its coefficient of z is one. It is therefore a unit
in B. However z+a is not a unit in the ordinary Laurent-series ring
A((z))=A[[z]][z^{-1}]. Consequently the natural inclusion of A[z]
in A((z)) does not extend to a homomorphism B -> A((z)).

Proof: if g=sum_{j>=N} b_j z^j is a nonzero Laurent series, choose its
least nonzero index N. Since A is a domain and a != 0, the least nonzero
term of (z+a)g is a b_N z^N. If this product equals one, then N=0 and
a b_0=1, contradicting a in m. This proves noninvertibility. A unital
homomorphism extending the inclusion would send a unit to this nonunit,
which is impossible.

This applies to the source-ring model in the structural agent's frozen
G4 scope whenever a is a nonzero nonunit (in particular one may use 5
in its mixed-characteristic domain). It prevents obtaining local survival
of c*[z] merely by mapping B into ordinary Laurent series and applying
the familiar z-residue. The nonlocal Bass summand does not supply that map.

No assertion is made about suitable completed Laurent rings, a different
residue/detector construction, another local model, or the truth of G4.
The target remains existence of a nonzero integral K4 generic kernel on
some two-dimensional ramified regular local mixed-(0,5) domain. This
obstruction is neither a refutation nor a narrowed replacement result.
The argument was sent to the active structural agent for coordination;
no edit was made to its candidate or scope. Campaign remains5/10.
