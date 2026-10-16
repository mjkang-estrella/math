# Source contracts, actual reading, and byte identities

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
All third-party copies remain private and retain their original rights.

Upstream source truth is stipulated at openai/math commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; no truth audit was undertaken.
`sources/upstream.json` and relevant catalogue entries were read. The
COMPLETE `sources/preprints-tree.json` was parsed: truncated=false,
13223 entries. Exact selected paths were matched, not merely searched in
the ignored truncated root-tree cache. The full catalogue/tree are fixed
read-only external references with hashes in `inputs/fixed-before.json`;
the selected exact tree entries are retained in `inputs/tree-membership.json`.
This is not a semantic reading of every manuscript or a new family survey.

## Exact pinned interfaces

`inputs/pinned-records.json` gives EACH retained full repository path,
local path, size, SHA256 and Git blob SHA1. Before copying, r15 was fully
authenticated against the supplied external anchor. For each retained
blob this round independently computed SHA1 of
`blob <byte-length> NUL <bytes>` and matched it to the complete source
tree. Source URLs are the pinned raw prefix
`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/`
followed by its exact repository path. No mutable branch URL supplies a
mathematical dependency.

Let B denote
`preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/build/`
and E denote
`preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/build/`.

* B/paper.tex, blob `93b277615495c01754b4575b045cba89a95f82a1`,
  retained as `inputs/pinned/06-paper.tex`: complete 354 lines read.
  `thm:main` gives sufficiently-large PRIME orders, balance, nonisolation,
  intersection and tau=q+1. It supplies no exact-pair condition.
  `cor:tree-cover` and its proof already make the standard graph transfer.
  Full introduction, overview and assembly proof read to identify the
  operation, without auditing the underlying probabilistic theorems.
* B/construction.tex, blob `a66cc581bb62ee628d006a1fd87b59b94fe0c61e`,
  retained under its basename: complete 341 lines read. Definitions,
  compatibility, `eq:det-core`, `eq:det-split-intersection`, all deterministic
  hypotheses, `eq:det-size-condition` and the complete proof of
  `prop:deterministic-reduction` were read. Its partitions merge constituents
  and split retained four-cycles; its core/pencil/local budget proof rules
  out all q-label covers for THAT input. This lower bound is not applied to
  the altered K_4 construction. The previously proved forced-connectivity
  obstruction is retained; its excluded refinement was not attempted again.
* E/paper.tex, blob `141ed64572de469c899d6d12d21790ee066128fa`,
  retained as `inputs/pinned/00-paper.tex`: complete 301 lines read.
  `thm:main` has s sufficiently large prime, s=2 modulo 3, and every
  sufficiently large odd n with threshold n_0(s), q=s^n. No balance or
  linearity is asserted. Its `cor:tree-cover` and full proof, field
  thresholds and full overview were read. The included incidence,
  linecover, selection and construction section bodies were not read or
  retained in this round; no new proof depends on their uninspected details.

The three new mathematical proofs use only elementary field/line facts and
explicitly supplied design ingredients, not an uninspected upstream lemma.

## Primary papers and actual operation-level reading

`inputs/primary-records.json` binds versioned URLs, retained bytes/hashes
and actual extents. Rendered line numbers below are those exposed by the
web reader; this is distinct from HTML source lines. None of the research
code from these papers was executed.

* [Francetic--Herke--McKay--Wanless, arXiv:1508.00951v3](https://arxiv.org/html/1508.00951v3):
  lines 34-186, Theorem 2.8 statement, 277-307 and 356-394 read. This
  includes Lemmas 2.1-2.2, Theorem 2.3 and proofs; the small-r theorem's
  exact range; and complete constructions/proofs in Sections 3.1, 3.3,
  3.4. The Latin-square operation replaces selected zero labels and adds
  two coordinates; the actual explicit cover is read, not inferred from
  degree conditions. Computational enumeration was not rerun or audited.
* [Bahmanian, arXiv:1710.05804v1](https://arxiv.org/html/1710.05804v1):
  lines 44-149 read: precise hinges and detachment definitions, all of
  Theorem 4.1(A1)-(A4), Lemma 4.2 and the Section 5.1 splitting operation.
  The remaining proof was not read. Its simple condition concerns
  repeated hinges within an edge; fairness of degrees and full-edge
  multiplicities does not assert preservation of every pair intersection.
* [Vazquez-Avila, arXiv:2108.01108v1](https://arxiv.org/html/2108.01108v1):
  lines 18-122 read for the explicitly named linear intersecting assertion
  and limited 2-packing interfaces. Their cited antecedent proofs were not
  read separately. None of those bounds is used in the new deductions;
  descriptive language about the conjecture is not a universal theorem.
* [Stinson, arXiv:2403.17602v1](https://arxiv.org/html/2403.17602v1):
  lines 31-203 read, including precise GDD/PBD/TD definitions, Construction
  1.1, Theorems 2.1/2.4 and proofs, and Lemma 2.5's actual counting proof.
  The substituted ingredients and chosen disjoint blocks construct a
  particular parallel class. A full resolution and all-small-covers lower
  bound are additional operations. The synchronized attempt in
  `design-checkpoint.md` proves its own stronger ingredient-to-resolution
  statement and finds an explicit upper cover; it does not attribute that
  statement to Stinson. Results cited there about general existence of
  ingredients were not independently read or invoked.

This is a bounded primary comparison, not an exhaustive trade/hyperoval
literature review or a priority certificate. No identity with a named
classical trade is assumed from the six-point picture. The normal form
and obstruction are proved explicitly instead.

## Historical reading and snapshots

`inputs/r15-authentication.json` binds exact external r15 file AND directory
membership against external seal
`87339b6771c8e4e08a05f3a346baeb6d0199459618a8a0b46550564e2ed8f482`.
After authenticating, full `candidate.md`, both checkpoints,
`source-contracts.md`, `primary-comparison.md`, and the copied scope were
read from that package; the parent's full disposition was read separately.
Other r15 payloads were authenticated, not all semantically read. No
historical verifier was run and no primary reading was inherited by claim.

The mandatory historical FT2 `r2-brief.txt` was read completely, lines
1-1078, hash `75a14a439cc976031cb23db6e41a2f301c1bad0843de43420dd9bc5831362843`.
This is history only, not a new FT2 attempt. Current parent brief/disposition,
AGENTS, upstream identity and mutable ledger were snapshotted internally;
exact originals and hashes are recorded. The live ledger is never a future
verification dependency. `inputs/reading-records.json` separates these
reading extents from authentication and from full-tree structural parsing.

The only new mathematical executable is the small F_4 normal-form check.
Its whole source was inspected and its SHA256
`dbc0955622f197645b89f1acb45002fcd724e047d1d16de6ef0ed4198a33358e`
was checked before running. It verifies one stated calculation, not a
search or a universal cover assertion. The independent symbolic proofs
remain necessary. The other executable is the read-only integrity verifier,
likewise inspected/authenticated before execution; integrity is not
mathematical or contribution acceptance.
