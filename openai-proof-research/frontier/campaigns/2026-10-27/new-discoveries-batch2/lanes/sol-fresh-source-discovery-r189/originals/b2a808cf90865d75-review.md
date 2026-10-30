# Independent TS132 scoped formal review

**Verdict: PASS_SCOPED_SUPPORT. Full TS132 formalized: false.** This verdict binds implementation output-manifest SHA256 55c87693245c7812a3097667d098c987c2f91bc8b861b16e84bc56eb3a42b93e, TSLocal.lean SHA256 24e24c0b5e920f04b7a8fc25b0a0d0002c107bd0a9fd540326ed5693d3a2e6bc and Controls.lean SHA256 3da297c0cd4d2a575b00b122e7f0d4a413931a74cf487fe69cd0c3b56ee51010. No required repair was found within the declared scope.

The reviewer authored the previous TS132 human proof review, but did not author TS132, its contribution report, this implementation or its manuscript. This is an independent review of those implementation bytes, not a new independent review of the reviewer's own earlier report. It is an internal scoped formal gate, not full-theorem formal verification, external peer review, acceptance, contribution approval or publication.

## Identity and fresh execution

Both the author's read-only verifier and separate reviewer inventory/hash checks authenticated the author, proof, contribution, formal and manuscript packets. The formal verifier checks all 72 sealed payloads and 18 selected input snapshots; its wrong-anchor run rejected before content checking. Seven actual pinned source blobs matched the complete, nontruncated preprints tree, including complete same-family non-PDF membership. Source truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated, not audited.

A new owned work copy received the current four Lean source/check files and five build/control helpers, without alteration. The complete helpers were read before execution; helper-provenance.json retains their original identities. A fresh temporary build compiled TSLocal and Controls, then printed every exact public declaration type and its transitive axioms. No existing task object was reused. All 22 support theorems, six definitions, one instance, 13 control theorems and one control definition compiled: 43 public declarations total. All successful compiler logs are free of warnings and errors. The copied helper's field independent_audit=false remains its original author-level metadata; this independent verdict is supplied by the present review, not by changing that field.

Lean is version 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52; mathlib is d13f23b723b8a846827a245b89c10fc7d3f11612. All declared dependency revisions and tracked tree cleanliness were checked read-only. The trusted Lean executable and cached dependency objects were not rebuilt from first principles; the compiler binary hash and exact cache path are recorded in work/logs/fresh-build/receipt.json. This is an explicit trust boundary, not a claim that hashing a source tree authenticates every dependency object.

## Semantic audit

The tournament theorem proves cardinality at most three from an irreflexive relation total on distinct points and at most one predecessor at each vertex of the finite set. It handles the empty set. Although asymmetry is not explicitly assumed, the proof needs no stronger hypothesis: fixing a vertex bounds its incoming and outgoing subsets by one, using totality and predecessor uniqueness for the latter. This is a real finite combinatorial conclusion, not a restatement of the bound in a hypothesis.

Word is an actual recursive product type with singleton depth zero. edgeLabel recurses when first coordinates agree and otherwise returns the oriented first difference or none. HeadConstant gives a common incoming label at each head. It is not an arbitrary assumed bound. The fiber theorem inherits the actual labels; the image-indegree theorem cancels two differences at one head. The recursive theorem uses the finite image/fiber count and injectivity of the tail projection inside one fiber to obtain card<=3^h. The depth-four theorem consequently gives card<82. Additive-group hypotheses and the assumed irreflexive total relation remain explicit. The construction does not silently assume a finite field or an already formalized Paley relation.

The affine declarations act on genuine function vectors over a field. The coordinate equality equivalence requires a nonzero scalar; the first-difference theorem assumes earlier coordinates agree and the designated coordinate differs. The row-position action uses an actual subgroup of field units, maps (v,c) to (av+b,ac), and proves injectivity, moves between any two pairs, composition, identity and the displayed left inverse. This is full row-position transitivity in that separate model. No theorem identifies these function vectors with Word or transports the labels across that identification; the manuscript states that limitation.

The coupled-profile theorem is conditional on two finite-depth scalar recurrences, initial upper bounds, L>=0, epsilon>=0 and epsilon*3^(d+1)<=2. It proves the stated explicit envelope, v_n<=epsilon L(3^n-1) and u_n<=2L for every n<=d. Its induction uses the already obtained u_n<=2L to bound epsilon*u_n; the envelope difference absorbs the next ordinary term. It does not assume the conclusion for the next index. The side-normalization lemmas expose the pre-normalized scalar inequalities and needed positivity. The zero-side lemma need not assume M>0 because it is a pure ordered-real implication from t/M<=epsilon; positivity of the actual manuscript M is discharged outside Lean. The strict seed theorem genuinely derives (44M^21)^2<M^2*k^20 from M>0 and 3M^2<=2k using the exact depth20 inequality.

All 43 generated type/axiom reports were inspected, with bounded rereads recovering a truncated combined display. Only propext, Classical.choice and Quot.sound occur. There is no sorry/admit, unsafe/native_decide shortcut, or new axiom importing the human theorem. Full source reading, compiled types and concrete nonvacuity controls agree with coverage.json.

## Adversarial controls

The 13 control theorems include the empty tournament, a three-cycle, an actual three-element head-constant set, depth zero, zero-scalar collapse, inability of translations alone to change the position label, zero and positive epsilon, the strict integer-parameter seed and failure at depth18. These exercise boundaries rather than merely repeat successful claims.

All six current-source theorem mutants were independently compiled and rejected at proof goals. The mutation implementation was read and the resulting logs inspected; no rejection relies on missing imports, parsing, unknown names or type/application mismatch. The false variants and mathematical reasons are:

- Tournament bound two: a directed three-cycle satisfies the hypotheses.
- Zero-scalar equality reflection: distinct vectors collapse to the same constant affine image.
- Strict depth-four bound below 81: over ZMod3 with oriented difference one, all 3^4 words are head-constant.
- Reversed affine difference: already false over Q at a=1, v=0, w=1.
- Envelope at most 3L/2: L=1, n=d=3, epsilon=2/81 gives envelope 17/9 while epsilon*3^(d+1)=2.
- Depth18 strict seed ratio: 3^18<2^18*4*20^2.

The last arithmetic check and the depth20 seed use exact integers, not floating point. A separate actual subprocess printed SOME FAIL and exited zero. The production checked_run wrapper exited one, retained that output, and reported rejection with exit=0. This verifies the real execution path, beyond testing its predicate in isolation.

## Exact outside interfaces

Not formalized: the actual Paley square subgroup/number theory and degree count; Word/function-vector equivalence and actual gate-label covariance; nested Boolean predicates and their common all-index raw-bit automorphism group; sensitivity/joint-profile definitions and all four Boolean recurrences; their conversion into the scalar hypotheses; prime existence and rounding; disjoint zero blocks; OR balancing; Boolean composition; logarithmic alpha, divergence and either full quantified theorem endpoint. These remain the human proof. Nothing in the scoped PASS removes these interfaces or weakens the original every-C and fixed-alpha target.

The manuscript's formal-support section and both coverage records preserve this boundary accurately. No mathematical repair or coverage correction is required. Original review prose is CC BY4.0, original review code MIT, author Myeongjin Kang with no affiliation; third-party inputs retain their rights.
