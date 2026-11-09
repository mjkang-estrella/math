# Author's scope reconciliation (not an independent review)

The frozen SCOPE.md hash remains 9b96245518d383432e770924856a44463c118ca68289eb7d85950acf1f872e09. No frozen wording was revised.

The proof treats the required quantifiers as follows. Section 2 establishes antipodal bijectivity from exact surjectivity rather than assuming it. Sections 3--4 construct a continuous sign lift without assuming f continuous; the infinite-dimensional argument uses only finite polygonal loops. Section 4.2 handles circle monodromy explicitly, and section 4.4 handles one dimension. Section 4.3 uses target connectedness to rule out an even lift and proves onto rather than assuming every sign selection is onto. Section 5 allows flat faces and nonempty equality plateaus. Section 6 handles both strict regions and the equality locus. Section 7 invokes the stipulated Banach-space source only after obtaining an ordinary sphere isometry and proves evenness, uniqueness modulo simultaneous sign, and the converse.

A potentially confusing coefficient in the strict-region proof was independently rederived: if c_t=((1-t)x+t y)/n_t, then y=(n_t/t)c_t+((1-t)/t)(-x). Both coefficients are positive for 0<t<1. Thus the second monotonicity application has exactly the required angular order. The crossing-segments inequality is the sum of lengths on [0,b] and [a,c], so it remains valid when p=b lies on a flat face.

The loop homotopy may move its base point; the proof explicitly tracks endpoint signs through a lifted square, so it never assumes a based contraction that has not been built. The sign of two lifts, and the parity of h(-x) relative to h(x), are constant by continuity on a connected sphere. The source dimension-two construction does not assume the target is also two-dimensional.

No numerical experiment is a premise. No extra test suite was used to stand in for the proof. There is no author-identified unresolved mathematical obligation inside the frozen statement. That is an author assertion, not an independent correctness result. Independent correctness review and separate primary-literature contribution review are outstanding; no grade or count is assigned.
