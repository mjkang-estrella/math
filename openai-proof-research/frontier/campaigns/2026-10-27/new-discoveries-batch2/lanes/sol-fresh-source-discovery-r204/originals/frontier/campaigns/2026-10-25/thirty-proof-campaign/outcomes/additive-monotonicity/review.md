# Independent review: additive monotonicity, MathDB 334772

**Verdict: PASS for the expressly claimed literal corpus correction, under the solution-count reading of “number of functions ... determined by the relation.” Recommend counting one distinct literal MathDB outcome, with that qualification retained. This is not a verified resolution of a conjecture in Park's manuscript, and not an interpretation-independent resolution of the word “determined.”**

Reviewed candidate: `outcomes/additive-monotonicity`. Reviewer work was isolated in `extension-matrix-lane/review-additivity/`; the candidate was not modified. No agents, git operations, shared indexes, or external posting were used.

## Exact reviewed hashes

- `formal/AdditiveMonotonicity.lean`: `8b87d9e3b6060d5e9cc5e74282ca1be52070488122538544c1fc073df1a175ee`
- `main.tex`: `1ed2b967a79b3a579fee4169d45f300fdd55211db3d6d13834b431a9160ff049`
- `source.json`: `97f4b1e6fc27b919f436a93cde6e2b69cdef693c57c376fb173063b5f03978f8`
- `outcome.json`: `5a590446b9f5fb83cc46276886a4158452c2e882db63a157675e28a7eb8ca6ea`

## Fresh formal verification

Copied only the formal source and manifest to `extension-matrix-lane/review-additivity/fresh/` and invoked the thirty-proof campaign's pinned `verify_outcome.py` on that fresh copy. The isolated replay passed all 12 local declarations with Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`, and the checked pinned dependency revisions. The source SHA256 in the fresh receipt matches the reviewed hash above. The only transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`; no holes, custom axioms, unsafe evaluation, or `native_decide` are present. Fresh audit: `extension-matrix-lane/review-additivity/fresh/build/audit.json`.

I independently checked the full theorem and cardinality reasoning. `KAdditive` quantifies over every ordered `Fin k` tuple in E and uses its actual sums, rather than a surrogate scalar condition. `count` is the cardinality of the filtered finite set of actual functions. The two functions differ at 2, so the family really has two members. The identity is additive for all E and k. Every tuple in the singleton E={1} is constant, so the exceptional function fails at k=2 because 0≠2, and holds at k=3 because 3=3. The filtered family has exactly one and two elements respectively. These exact cardinalities, not assumed membership labels, are proved before the final strict increase. Numeric arities 2 and 3 are positive and ordered. A finite family is a legitimate instance of an unrestricted arbitrary family; no infinite-cardinality convention is involved.

This is a complete finite counterexample to the universal assertion **when n counts satisfying functions**, rather than a bounded verification of the conjecture or a supporting lemma counted separately. The positive-input example is unaffected by whether arithmetic functions are presented on positive naturals or naturals including zero. The paper expressly restricts its precise target to real-valued arithmetic functions; these are an admissible conventional class for the unrestricted wording.

## Primary-source and literal-statement audit

I fetched the live MathDB API post `518dfe77-1500-4689-8141-83ffb843b249` with User-Agent `Mozilla/5.0`. Its full statement still says “number of functions in S determined by the relation” and gives the displayed k-summand identity, with no multiplicativity, infinitude, or closure hypothesis on E or S. The fresh full API response is saved in the unique reviewer scratch.

I also fetched and read the **entire actual primary manuscript** arXiv:1612.00897v1, not a catalogue summary or the candidate's source-audit assertion. Its raw HTML SHA256 is `0b4407913c0c25cbc08d49314b7a58777c82d8dd6cc4015c93f4d27979d7d17b`, exactly matching `primary-reference.json`. It proves k-additive uniqueness of positive squares for multiplicative functions for k≥3. It does not define n(E,S,k), state the claimed unrestricted monotonicity conjecture, or supply the generalized statement attributed to it by MathDB. This attribution defect is real. The candidate correctly exposes it, does not attribute the refuted assertion to Park, and does not claim to disprove his theorem or a conjecture restricted to multiplicative functions.

The semantic caveat is material. “Determined” can mean “satisfying the relation,” as the candidate explicitly chooses, but in additive-uniqueness literature it can also refer to a uniqueness/identifiability property. The primary manuscript uses “determined uniquely to be the identity” in that latter sense. Under a different uniqueness-based definition of n, the supplied `count` is not a formalization of n, and the certificate would not settle that different assertion. Neither the original reference nor the terse MathDB wording proves that all conceivable readings coincide.

Nevertheless the target here is explicitly the **literal unrestricted MathDB count conjecture under the ordinary solution-count interpretation**, and that interpretation is plausible for “number of functions in S ... by the relation.” It is not contradicted by an explicit extra condition in the live post. The supplied paper states the interpretation, the primary-source mismatch, and the exclusion of additional restrictions prominently. Under a campaign that already admits literal corpus corrections, this meets the claimed scope and can count once as such a correction. It must not be described later as an established source-author conjecture resolved without qualification. If a tally were instead limited to well-attributed, unambiguous primary-literature conjectures, this entry should be excluded from that different tally.

## Paper and counting assessment

The written proof matches the formal definitions and all cases. It gives the complete construction and cardinality argument, explains why the all-tuples condition reduces to one tuple, and accurately reports the absence of the alleged general conjecture in the cited manuscript. The source-audit statement is correctly documentary, not purportedly a Lean theorem. No unsupported discovery or worldwide-priority claim appears. I reviewed TeX content; PDF rendering is a separate parent-managed production step.

MathDB ID 334772 is outside the inherited twenty verified IDs. Its mathematical target is distinct from the matrix and other inherited outcomes; none of its supporting declarations should count separately. Recommendation: count **one literal corpus-statement correction**, retaining the outcome manifest's attribution and interpretation limitations in the ledger and release summary. No mathematical correction is required for the explicitly chosen count definition.
