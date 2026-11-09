# Round 5: 13,561 normalized additions freshly verified

Endpoint: `Percolation.NReplay.not_conjecture20_normalized_after13561 : RemainingSuffixUnsatR5 → ¬ Conjecture20`.

Status: **conditional**. The unconditional endpoint and NoMinimalTwoRound5 remain unproved. This lane makes no acceptance, novelty or campaign credit claim.

The single remaining hypothesis is exactly:

```lean
¬ ∃ v : SatVar → Bool,
  (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
  (∀ c ∈ prefixR5_0004, CNF.Holds (v ∘ decodeVar) c)
```

The accumulated prefix contains exactly the first **13,561** retained additions. Round 5 adds **1,061** newly verified additions beyond round 4. Last checked LRAT ID: **38,725**. Continue at **zero-based steps[13561]**, LRAT ID **38,726**. Exactly **116,110** additions remain. No replay beyond this frontier is claimed.

All **443 inherited Lean source files remain byte-identical**. Five new adaptive replay chunks each have a definitions module, four finite-check helpers and a soundness module. A new conditional endpoint and metadata audit bring the delivered total to **475 modules**. The original generation target was 17,500 additions; later generated drafts were not replayed and are excluded from source-only.zip and module-order.txt. They are retained only in unreplayed-generated/. The checkpoint driver stopped intentionally with status 75 after ReplayR5_0004; this was not a Lean or checker failure.

Fresh strict extracted replay passed **475/475 compiler calls** and **475/475 explicit-module leanchecker calls**. Successful compiler wall total: **2,887.39 s**. Successful checker wall total: **1,568.29 s**. Combined successful replay: **4,455.68 s**. These totals come from individual GNU time logs; they exclude generation, shell overhead and reporting. There were no failed Lean or checker calls in this round. Every such process used the fixed CPU, wall, RSS and two-CPU limits; no limit was increased.

The independently written source scan passed all 475 modules. The metadata audit passed **62,597 local declarations**. Fresh normalized DIMACS export matches normalized.cnf byte for byte. The endpoint prints exactly propext, Classical.choice and Quot.sound as its axioms. Logs, receipts, hashes and per-module times are retained.

Fresh replay began with a safely extracted source archive and resumed in budget chunks using rolling source and compiled-output hashes. The final checkpoint archive was re-extracted into that same fresh tree; unchanged verified source bytes retained valid stamps, and the new endpoint and audit were then compiled and checked. The final manifest and an independent archive-to-extraction comparison cover every delivered source file. No compiled objects were copied from round 4.

Principal files: source-only.zip; normalized-progress.json; results.json; module-times.json; PROOF.md; STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; module-order.txt; inherited-source-comparison.json; source-manifest-check.log; generator-correspondence.json; axioms.txt; metadata-audit.txt; fresh-replay.log; fresh-extracted/logs/; packet/src/; and the resource-bounded replay.sh and guard.sh drivers. No lane-started background job remains.

Archive SHA256: `9add6cc761e26a70637ea9a8555199187c705f121a3a25b1159ce2f22ec7637c`.
