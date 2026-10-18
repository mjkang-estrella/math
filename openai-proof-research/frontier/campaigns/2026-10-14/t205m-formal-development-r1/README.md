# T205M provisional finite-poset support

Myeongjin Kang, no affiliation. Original prose CC BY4.0; original code MIT.
This is parent author-side development while the independent full-proof and
contribution gates run. It is not an independent review, accepted result,
frozen formal release, or formalization of the full T205M theorem.

The candidate is the unchanged sharp staircase-square multiplicity statement
in `../fresh-arithmetic-discovery-r38/candidate205m.md`, SHA256
`17b2b35c42ef10fd0600e0a7b4b5897f0b80cd57cfb1e12587b722294a3e20c5`.
The supported argument is the unique-rank step in the included parent
high-capacity proof, SHA256
`fc155c9ac03d70b8a68f501541daf0fb5c02bf9caf6734f61757065a6e796430`.

`T205M.lean` defines a finite order ideal by downward closure in an arbitrary
partial order. It proves that an ideal contained in another ideal can be
extended to every intermediate cardinality, by inserting a minimal missing
element. For a finite ambient poset it then proves that uniqueness of an
ideal of a fixed cardinality forces every element inside it below every
element outside it. The contrapositive constructs a second ideal of the
same size. A final theorem gives two distinct ideals of a prescribed size
when every such ideal admits an incomparable inside/outside pair.

The Lean proof of cross-comparability uses the principal ideal below the
outside element. If this principal ideal is small enough, extend it to the
specified rank. Otherwise truncate it to that rank. Uniqueness contradicts
the respective exclusion or inclusion. This replaces the prose proof's
linear-extension argument, with the same conclusion. No linear extension
or cross-comparability conclusion is assumed. The ideal assumption on the
specified set is explicitly retained in the interface, although uniqueness
and the rank-existence lemma already force it.

The scoped support does not encode partitions, skew diagrams, bottom-four
column geometry, exception exclusion, Kostka configurations, representation
theory, source-module maps, LR/Pieri, finite character calculations, or the
full uniform induction. In particular, the hypothesis excluding an ordered
cut in `two_ideals_of_no_cut` must still be proved from the skew geometry in
the mathematical argument. It is not supplied by this formal development.

`Controls.lean` applies the theorems to a four-element chain and a product
poset, and proves counterexamples to deleting uniqueness or the rank upper
bound. The antichain example invokes the second-ideal theorem. These are
kernel-checked mathematical examples, not numerical evidence for T205M.

`rebuild.py` derives from the original T027O support builder, with module
names adapted. It checks Lean4.34.1 and all nine dependency Git revisions
against the copied lockfile, checks tracked dependency cleanliness, compiles
fresh local objects outside this directory, prints declaration types and
audits their axioms. Only the standard `propext`, `Classical.choice` and
`Quot.sound` are allowed. The pinned dependency object cache remains trusted
and is not rebuilt. The builder is not an independent correctness review.

Run from any directory:

```text
python3 -B rebuild.py --output /var/tmp/NEW-UNUSED-T205M-BUILD
```

The output path must be new and outside this directory. `--cache` and
`--lean` can override local paths, with the same pin/version checks.
Compilation logs and source hashes are retained under `validation/` after
a successful build. No original candidate or prior frozen packet is edited.
