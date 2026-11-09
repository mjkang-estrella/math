# Round 7c handback — root decides acceptance

The assigned counting identity is proved without premises:

    ChanLevine.Round7C.matchingCountConvolution : ChanLevine.Round6.MatchingCountConvolution

This is the original frozen Prop from CountR6Bridge.lean, with every n ≥ 3, every frequency and every coefficient m ≥ 0. No alternate counting semantics or replacement endpoint is introduced. There are no remaining Props in this lane. MatchingTraceExpansion belongs to the sibling r7t lane and is neither assumed in this theorem nor proved here. The full MathDB endpoint is not assembled here. No self-acceptance or credit is requested.

## Proof

CountR7CWeights factors the character of the frozen chipWeight into the chip character and the full rotor product. It separates selected empty-facing conditions into empty endpoint and forced rotor conditions.

CountR7CExpansion applies the inherited level equivalence and forced_rotor_sum to literal configurations, discards nonmatchings with nonmatching_indicator, and proves the positive-level Fourier matching expansion. chipSum retains bounded chip functions of exactly the required total; the wrap edge is retained throughout.

CountR7CZero proves that a rotor function without a facing pair is constant: a true rotor propagates around the cycle using natural translations in ZMod; if none is true, all are false. Thus precisely the two empty constant rotors survive at zero. Their character sum is 1 + z^n = 2 for the frozen frequency root. The original positive-level count continues to exclude these zero-chip states. completed_matching establishes the matching expansion for completedFourier at every level, with no positivity hypothesis.

CountR7CGeometric identifies bounded chip functions with the finite finsupp antidiagonal and proves chipSum is the coefficient of a product of geometric power series, with factors 1 at selected endpoints. Rescaled geometric-series cancellation clears each free-vertex factor. denominator_prod identifies the original ordered denominator with the ZMod-indexed product; chip_convolution gives the exact finite coefficient identity. CountR7CFinal then interchanges finite sums and applies this identity term by term.

## Verification and limits

The inherited exact checker passed its 104 positive-level cases through n = 10, m ≤ 2n, before formalization. A new isolated integer checker verifies 28,535 individual geometric coefficient identities for all cyclic matchings through n = 10 at five integer values of z, and 30 comparisons with literal chip/rotor enumeration, including zero. These are diagnostics, not proofs. The first new checker run compared an unpadded constant polynomial with a padded coefficient array; that script bug was corrected and its failed log retained.

All 36 input modules from chanlevine-round6a-source.zip (SHA-256 844b066f28b9c97b43e41ce54c77813c1b41b6334994d2f1ebb406390d7ec9e0) are byte-identical. Seven new modules use only CountR7C names. Development reused immutable inherited compiled files inside this lane. The delivered replay extracts source only into an empty directory and rebuilds all 43 modules serially. It runs strict warning-as-error Lean and leanchecker on every module, audits all generated declarations in the final/control local import closure and their full reachable dependency closure, verifies closure equality independently, and runs seven expected-failure controls. results.json records the actual replay outcome and LOCAL versus UPSTREAM metadata separately. The audit instrumentation module itself is excluded from theorem seeds. Upstream executable annotations are reported, not treated as new lane declarations; only propext, Classical.choice and Quot.sound may occur as reachable axioms.

All writes, caches, temporary files, archives and logs are lane-local. No child agents, git operations, shared edits, network, external messages, uploads or browser tabs were used. Processes use the inherited two-CPU, CPU 120 s, wall 140 s, approximately 6 GiB RSS cap, MALLOC_ARENA_MAX=2 and Lean -j1 -M3500. Every compilation has a unique retained log. No process is left running at handback.

## Root integration

Import CountR7CFinal and pass Round7C.matchingCountConvolution to the frozen Round6.transferCountEvaluation, together with the sibling lane's independently validated MatchingTraceExpansion. Then use the existing frozen bridge chain. This lane does not certify the sibling work or accept MathDB 338887.
