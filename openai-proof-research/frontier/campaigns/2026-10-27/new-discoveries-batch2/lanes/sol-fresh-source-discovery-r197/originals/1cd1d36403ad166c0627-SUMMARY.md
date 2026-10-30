# Fair cascade summability component

**Component formal PASS; formal investment only, not acceptance.** Classical
supporting fact, credit 0; counts stay 3/30 additional and 33/60 total. Solo
GPT-6.1 Sol high/default. No children, git, shared edits, other-lane writes,
browser, contact, upload or publication. No changing selected-family lane or
other active proof was read.

## Integration

Import `KraftSummability` from `formal/`. Namespace `CascadeRate`. The three
frozen mathematical sources and `run_lean.py` are byte-identical copies from
`sol-cascade-source-tree-formal-r1/formal/`; before/after hashes match.

Closed endpoints, with **no residual Kraft, finite-partial-bound or positivity
premises**:

```lean
fair_one_series (T : SourceContextTree) :
  Summable (kappa T (fairAssignment T) [true]) ∧
    (∑' n, kappa T (fairAssignment T) [true] n) ≤ 2

sourceTree_fair_one_series :
  Summable (kappa sourceTree (fairAssignment sourceTree) [true]) ∧
    (∑' n, kappa sourceTree (fairAssignment sourceTree) [true] n) ≤ 2
```

Individual endpoints: `kappa_fair_one_summable`,
`kappa_fair_one_tsum_le_two`. Supporting theorems:

* `finiteContexts_prefixFree`, `finiteContext_ne_nil`,
  `selectedContexts_prefixFree`: actual finite leaves are prefix free, never
  empty; selecting actual alpha-LIS `[true]` preserves prefix freeness.
* `selected_cascade`: each selected actual leaf has its actual fair cascade
  equal to `2 * (1/2)^w.length`, using the frozen product identity.
* `word_enumerated_once`: every word has a unique sigma pair consisting of a
  length and a binary `Fin` tuple whose `List.ofFn` is that word.
* `kappa_eq_sum_selectedWeight`: literal Eq.(5) κ is exactly the length-n
  tuple sum; includes n=0, with no index offset or arbitrary enumeration.
* `kappa_fair_one_tsum_eq`: exact equality of the literal κ total with the
  sum of actual cascades over the subtype of actual selected finite contexts.
* `kappa_fair_one_nonneg`: nonnegativity for fair q at every n.
* `kappa_one_zero`: κ(0)=0 for every probability assignment q.

## Proof and source scope

The frozen `context_prefix_unique` gives leaf prefix freeness; the internal-root
hypothesis excludes the empty context. Apply the actual pinned bodies
`InformationTheory.IsPrefixFree.summable_one_div_card_pow_length` and
`InformationTheory.IsPrefixFree.tsum_one_div_card_pow_length_le_one` from
`Mathlib/InformationTheory/Coding/Kraft.lean`, with Bool cardinality 2. Scaling
by 2 gives a summable weight on the actual selected subtype. The subtype
indicator embeds it into all finite words. The actual `List.equivSigmaTuple`
(body inspected in `Mathlib/Data/List/OfFn.lean`) reindexes those words exactly
by length and binary tuples; summable sigma regrouping yields the literal κ
series and its total. All source-tree hypotheses remain in `SourceContextTree`;
no stability, particular bush family, or depth-growth assumption is used.

Read the full candidate PROOF (especially §4), root ADOPTION, both requested
reviews, frozen SUMMARY and frozen mathematical sources. Earlier source review
holds are superseded only as described by the supplied second review and root
investment decision. No fresh literature or registry clearance is attempted for
this explicitly classical, uncredited component. Ancestor instructions, campaign
counts/context and immutable upstream metadata were inspected. The very large
catalogue/combined initial output was truncated; it supplies no mathematical
premise here.

This component makes **no nongeometric or source-refutation claim**. It does not
prove the remaining universal convergence conjecture for arbitrary q. Optional
κ≤1 and generic tail-transfer lemmas were not implemented. No novelty, finished
paper, final independent review or candidate acceptance is asserted.

## Validation, audit and limits

Pinned Lean binary SHA256 exactly
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612` is supplied metadata;
no git operation was used to re-establish revision identity. Actual imported
artifacts and available source files are hashed in `dependency-hashes.json`:
4,146 imported modules and 16,572 source/olean/private/server artifacts.

Fresh replay `replay/` was initialized from only `.lean` sources and the runner,
with no inherited own-module oleans. `initial-source-only.json` records that
state. The serial command was:

```
python replay/check.py DepthDefs SourceDefs TreeConstruction KraftSummability Inventory Audit
```

Every Lean invocation uses `-DautoImplicit=false -DwarningAsError=true`, a
120-second wall deadline and sampled **sum of process-group RSS** capped below
3 GiB. Peak fresh sampled RSS was **2,914,959,360 bytes**. All six modules
passed. `replay/verification/receipt-*.json` records commands, paths, times,
exit status and RSS; empty mathematical-module logs indicate no warnings.
Sampling cannot rule out an unsampled transient peak.

`Audit.lean` enumerates every actual declaration in all four mathematical
module origins, including generated/private declarations and instances. Its
206 entries comprise 12 DepthDefs, 107 SourceDefs, 61 TreeConstruction, 26
KraftSummability declarations. Every actual type and transitive axiom list was
personally read in full, in four untruncated chunks. The fresh audit output is
byte-identical to that read output. Only `propext`, `Classical.choice` and
`Quot.sound` occur. No custom axiom or unsafe declaration appears. The frozen
recursive depth definition has Lean's generated `depth._unsafe_rec` helper:
its actual flags are unsafe=false, partial=true, and its axiom list is empty;
it is disclosed rather than omitted. No authored partial/unsafe implementation
or native decision is introduced. The audit/inventory display modules are
outside mathematical origins.

All six failed development compiles are retained with exact logs/receipts in
`verification/` and listed in `provenance.json`. They concern dependent-index
rewriting, decidable-if simplification, deprecated names, and audit option/type
inference; all were corrected without raising limits. Two early read commands
used a nonexistent runner location and a malformed rg path; corrected reads
were used. No mathematical numerical diagnostic was run. Hash/provenance
bookkeeping ran with hard 512 MiB AS, 30 CPU seconds, 45 seconds wall timeout,
and BLAS/OMP/MKL/NumExpr=1. `provenance.py` records its results. Input hashes,
frozen before/after hashes, source hashes and the fresh audit hash are retained.
