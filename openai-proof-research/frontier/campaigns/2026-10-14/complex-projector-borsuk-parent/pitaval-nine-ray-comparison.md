# A further explicit nine-ray antecedent does not give the B8C cover

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
Parent contribution evidence only; B8C contribution remains UNRESOLVED.

Read Renaud-Alexandre Pitaval, Coding on Flag Manifolds for Limited Feedback
MIMO Systems, author thesis, Chapter 5 sections 5.1-5.2 (printed pp31-37),
including Table5.5 and the definitions of the equal-power restriction.
Primary body URL:
https://aaltodoc.aalto.fi/server/api/core/bitstreams/b7fedf6a-3a95-4c71-9880-10e090003246/content
Local extraction lines1985-2440, plus publication list lines275-335 and
section5.3 lines2440-2535. No full-thesis or full-publication-IV reading
is claimed. The separate ICC2011 paper's web retrieval returned403.

This is a more specific comparison than excluding packing in general.
Table5.5 explicitly lists n_t=3,n_s=1,n_cb=9, squared minimum chordal
distance2/3, with equal-power optimality. The adjacent12-ray entry has
the same packing distance without the equal-power restriction. The
construction uses abelian subgroups of an extraspecial group and their
orthogonal eigenspace decompositions. General projective orbit generation
is explained in section5.1, with displayed optimized examples in complex
dimensions2 and4. These are antecedents to orbit-code generation, not a
claim of a sufficient three-dimensional minimax covering theorem.

For normalized single-stream equal-power codewords s in C^3, each coordinate
has squared modulus1/3. Therefore at each coordinate ray e_i,

    max_s |<e_i,s>|^2 = 1/3.

Consequently the explicit nine-ray EP row cannot have the B8C requirement
inf_u max_s |<u,s>|^2 > 1/2. Its optimal minimum pairwise distance cannot
repair this universal-cover failure. This implication is exact and needs
no numerical testing or assertion about the full unknown covering optimum.
It remains valid after a common unitary change, using the rotated basis.

A related general check: for four mutually unbiased orthonormal bases in
C^3, any proper subcollection of their twelve rays has score at most1/3.
Choose an omitted ray u. Its inner products with retained rays in its own
basis are zero; those with rays in other bases have squared modulus1/3.
Thus simply taking nine rays from that twelve-ray arrangement cannot pay
the desired strict threshold. This elementary observation is supporting
comparison, not a new result nomination.

The comparison excludes the displayed EP nine-ray construction and this
specified MUB-subset operation. It does NOT exclude arbitrary non-EP
nine-ray orbits, all choices of group initial points, or all earlier
covering constructions. No missing-search-hit novelty claim is made.
The previously passing full B8C proof is unchanged, and no contribution
PASS, manuscript or count increment follows from this note.
