# Round 4: normalization closed; 12,000 normalized additions checked

Endpoint: `Percolation.NReplay.not_conjecture20_normalized_after12000 : Percolation.NReplay.NormalizedFrontierUnsat5 → ¬ Percolation.Conjecture20`.

Status: conditional. Neither `NoMinimalTwoRound5` nor `not_conjecture20_unconditional` is proved. No acceptance, novelty, or campaign credit is claimed; root alone decides.

The exactly one remaining hypothesis is:

```lean
¬ ∃ v : SatVar → Bool,
  (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
  (∀ c ∈ prefix023, CNF.Holds (v ∘ decodeVar) c)
```

`prefix023` is exactly the first 12,000 retained additions of the normalized trimmed certificate. The last checked LRAT ID is **35872**. Continue at **zero-based steps[12000]**, retained addition **12001**, LRAT ID **35873**. Exactly **117,671** additions remain. The hypothesis is a frontier-refutation Prop, not a claim that those additions were replayed.

Normalization is fully kernel checked: arbitrary incidence-preserving point/line bijections of PG5 preserve step, every natural round, percolation, TimeIs, and Minimal. Every threshold-5 percolating infection contains a noncollinear triple. An explicit family of 86 checked collineations transports such a triple to 0, 25, 30. The transported witness satisfies the unchanged CNF and the three positive units. Lean's normalized export matches normalized.cnf byte for byte, including clause order and variable numbering.

The packet retains all 92 inherited Lean source modules byte-identically. It adds all 11,294 selected input-clause proofs needed by the complete normalized certificate, plus 24 chained modules of 500 verified normalized additions each. Later generated sources are clearly labeled unverified under unreplayed-generated/, outside the source archive.

Fresh extracted, strict, resumable verification passed for **436/436 compiler calls** and **436/436 explicit-module kernel checks** for the final packet. Compiler wall total: **2409.38 s**. Checker wall total: **1079.01 s**. Combined successful verification: **3488.39 s**. The 12,000 normalized additions alone took 335.36 compiler seconds and 56.08 checker seconds. Per-module measurements are in module-times.json. The final 436-file source scan and metadata audit of 57,890 declarations passed; all 436 final source hashes passed. The endpoint's transitive axioms are only propext, Classical.choice, Quot.sound.

Replay was resumed after correcting a direct-clause simplification proof in NInputs206; the failure log is retained. The next replay module, NReplay024, hit the fixed 120 CPU-second limit (111.28 wall seconds, 2,185,064 KiB sampled RSS). None of its additions is counted. No resource limit was raised. This measured bottleneck is the immediate continuation issue: factor the expensive checks across helper modules or otherwise reduce their cost while keeping the fixed caps.

An earlier combined finite geometry check hit the RSS watchdog and was replaced by the argument from the plane axioms. Some initial development log labels were reused; available failures and the exact observed watchdog receipt are disclosed in results.json. All final fresh compiler/checker logs are retained. No lane-started job remains at handback.

Files: source-only.zip; results.json; module-times.json; PROOF.md; STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; normalized-progress.json; certificate-sha256.txt and .json; generator-correspondence.json; inherited-source-comparison.json; source-manifest-check.log; fresh-replay.log; fresh-extracted/logs/; packet/src/; and unreplayed-generated/README.md.

Source archive SHA256: `77e80668b5ba04a8796abadd7e09fec3f3965f514c0449914b981be545329a47`.
