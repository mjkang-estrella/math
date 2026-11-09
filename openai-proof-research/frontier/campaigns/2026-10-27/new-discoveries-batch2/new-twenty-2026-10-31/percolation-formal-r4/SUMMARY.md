# Round 4: normalization closed; 12,500 normalized additions checked

Endpoint: `Percolation.NReplay.not_conjecture20_normalized_after12500 : Percolation.NReplay.NormalizedFrontierUnsat5 → ¬ Percolation.Conjecture20`.

Status: conditional. `NoMinimalTwoRound5` and `not_conjecture20_unconditional` remain unproved. Root alone decides acceptance. No novelty or campaign credit is claimed.

Exactly one remaining hypothesis:

```lean
¬ ∃ v : SatVar → Bool,
  (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
  (∀ c ∈ prefix024, CNF.Holds (v ∘ decodeVar) c)
```

`prefix024` is exactly the first 12,500 retained additions of normalized-trimmed.json. Last checked LRAT ID: **37643**. Continue at **zero-based steps[12500]**, retained addition **12501**, LRAT ID **37644**. Exactly **117,171** additions remain. The frontier-refutation hypothesis is explicit; no formal replay of the remaining suffix is claimed.

Normalization is fully proved. Arbitrary incidence-preserving point/line bijections preserve step, every natural round, percolation, TimeIs and Minimal. Every percolating threshold-5 infection contains a noncollinear triple. A family of 86 kernel-checked collineations transports it to 0, 25, 30. The transported witness satisfies the unchanged CNF plus those three positive units. The complete Lean DIMACS export matches normalized.cnf byte for byte, including clause order and numbering.

All 92 inherited Lean source files remain byte-identical. All 11,294 input-clause theorems selected by the complete normalized certificate are checked. Twenty-five chained replay modules each close 500 additions. For NReplay024, six helper modules separate the literal definitions and finite RUP checks from the 500 soundness proofs. This resolves the original aggregate module's CPU-cap failure without increasing a limit. Unverified later source drafts and the unconditional endpoint draft are outside source-only.zip.

Final extracted, strict, resumable verification passed **443/443 compiler calls** and **443/443 explicit-module leanchecker calls**. Successful compiler wall total: **2507.80 s**. Checker wall total: **1131.37 s**. Combined successful verification: **3639.17 s**. Normalized replay and its helpers took 436.76 compiler seconds and 109.14 checker seconds. module-times.json gives all measurements.

The final 443-file source scan, all 443 source hashes, and metadata audit of **59,394** local declarations passed. The endpoint's axioms are only propext, Classical.choice, Quot.sound. The source replay was resumed after the direct-clause simplification correction and helper factorization; earlier unchanged module bytes and their dependency stamps remain validated.

The original unfactored NReplay024 hit the fixed 120 CPU-second limit (111.28 wall seconds, 2,185,064 KiB sampled RSS). Its receipt remains in fresh-replay.log and checkpoint-12000/results.json; its compiler-log name was later reused by the verified replacement. An earlier combined finite geometry check hit the RSS watchdog and was replaced by an argument from the plane axioms. Some initial development labels were reused; available failures and exact observed failure receipts are disclosed in results.json. All final successful fresh logs are retained. No resource limit was raised and no lane-started job remains.

Files: source-only.zip; results.json; module-times.json; PROOF.md; STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; normalized-progress.json; certificate-sha256.txt and .json; generator-correspondence.json; inherited-source-comparison.json; source-manifest-check.log; fresh-replay.log; fresh-extracted/logs/; packet/src/; check-factoring/; and unreplayed-generated/README.md.

Archive SHA256: `9d25c3347aad2ca49799def30fb28e3fac171c6b680369f7f23046e0db38731e`.
