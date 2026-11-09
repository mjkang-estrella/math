# Development trials (scratch dev-trial/, since deleted; superseded by the fresh-extraction replay)

1. t1: the first replay guarded on total VmRSS. `build-Yip355956` was killed at 1.8 s (peak 6.46 GB) during `import Mathlib`. A probe showed RssFile ≈ 5.97 GB and RssAnon ≈ 0.19 GB at the kill. The guard was changed to private RSS (RssAnon+RssShmem) at 6 GiB, total VmRSS is still reported, and the systemd MemoryMax=6G scope was added.
2. t2: the audit took 97 s wall, because it enumerated every environment constant. `ReviewSanity` failed on a linter (`haveI` → `have`) and now uses a local `Fact` instance.
3. t3: profiling showed the slowness came from the enumeration, not from `collectAxioms` or printing. The audit was switched to the module's own `constNames` (the same module-origin set, re-checked with `getModuleIdxFor?`) and now takes 3 s. The expected message for the wrong-certificate control was changed to the actual "ring failed".
4. t4: the expected message for the wrong-endpoint control was made case-insensitive ("Type mismatch").
5. t5: full PASS (36 s). The final replay is the fresh extraction of `source-only-proof.zip` in `fresh-extraction/`.

Every trial call ran under the same per-call caps. No author file or cache was modified; the oleans were written only inside the scratch directories.
