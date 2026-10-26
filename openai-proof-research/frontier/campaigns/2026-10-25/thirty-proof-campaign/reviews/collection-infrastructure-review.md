# Collection infrastructure review

**Verdict: PASS for the current 28 accepted package inventories and canonical acceptance bindings, with the path/extraction hardening below verified. This is not approval of a finished thirty-package collection.** Final collection remains gated on exactly 30 accepted entries and matching final replay receipts, including the pending Nim and Rust packages. I did not run final collection or rebuild/re-audit the original twenty proofs.

Reviewed hardened script hashes:

- `collect_release.py`: `abdfc48e405182f4241818b75d5839b3626ce2418ef2a214aa605fc03091651b`
- `verify_archives.py`: `a216841b6534dcb632ae9f15ac4c617bd9089de706933ccf06f9bacaad6d40f8`
- `package_outcome.py`: `34ad2e2d39af07eb06bbc68b5122f0f7268685604cf4694e427412176db04b27`
- `verify_outcome.py`: `68e13b6cded4dbb850d4724978f2d138f08e53b484518ff585423013e620f844`
- `build_paper.py`: `9cb9446edb25e579fba3cb841dd98424751dadc6444651bfa8df35981ffb5354`
- `pins.json`: `1513106d9aea9df4f384be3fc0409a546bc63482cd5671c4d931520e07da7aae`

Reproducible read-only checks and detailed results are in `extension-nim-counter/review-collection/check_infrastructure.py` and `checks.json`. Only this report and unique reviewer scratch were authored; no shared source/index edits, agents, git operations, PDF production, or final-collection attempts were made.

## Verified gates and preservation

- Actual target/count/entry-length state was 30/28/28. Both the original twenty ledger and current 28 ledger are rejected by `validate_ledger`. Artificially advertising 30 with only 28 entries, and advertising 28 with 30 entries, also reject. Duplicate source IDs, invalid ordinals, failed replay status, traversal package paths, and traversal archive paths reject.
- All original twenty IDs, their order, and archive SHA256 values match the prior campaign ledger exactly. All 28 actual archive bytes match their current explicit ledger archive paths and hashes. No filename-discovery fallback substitutes a different archive.
- Invoked `validate_members` and `validate_acceptance` individually on every current accepted archive without invoking final `main()`: **28/28 PASS**. This includes old canonical metadata/proof/TeX/PDF bindings, the premagic legacy acceptance branch, source hash/declaration receipts, and matching extracted-archive replay records. Every available non-premagic archived `review.md` also equals its canonical counterpart, checked independently of the collector. All archive pins equal current pinned revisions.
- Some preserved older ZIPs contain older verifier-script bytes, as expected from byte-for-byte preservation. All eight current extension archives contain the current verifier bytes. This is not an archive-preservation defect.
- The collector reads tracked `archive-replays.json` and the intended old/current build receipt fallback. A replay record must bind both the archive hash and proof hash. Source/paper metadata cannot silently substitute different canonical proof or TeX bytes.

## Path/extraction finding fixed and retested

Initial synthetic tests found that `root/a.txt` and `root/./a.txt` (also `root//a.txt`) could coexist in a hash-valid archive yet collapse on extraction. Parent hardened `validate_members` to reject noncanonical raw paths and made `verify_archives` reuse that validator.

After the change, synthetic dot aliases, doubled-slash aliases, parent traversal, backslashes, and symlinks all reject; an ordinary canonical ZIP passes. Every actual accepted archive still passes, and no actual archive has a noncanonical member. The replay helper now uses a fresh `tempfile.mkdtemp` directory per archive/run, checks archive-root/stem agreement, and uses explicit CRC failure checks rather than optimization-removable assertions. These changes address the observed alias and stale-extraction issues.

## Remaining small hardening suggestions

These do not show a mismatch in the 28 actual accepted artifacts checked above.

1. **Fresh packaging and atomic publication.** `package_outcome.py` still reuses an existing staging directory (`mkdir(exist_ok=True)`) and manifests every remaining file. Removed files from an earlier packaging attempt can survive a later run. Use a fresh staging directory or require an empty destination. The collector writes the final ZIP before readback validation; a failed readback can leave a partial/invalid release path beside an older receipt. Validate a temporary ZIP, then atomically replace the final path and receipt.
2. **Make preservation and evidence bindings executable.** Current old-20 hashes are correct, but the collector does not compare those entries against the old acceptance ledger itself. Add that comparison to protect the “original twenty preserved” promise against future index mistakes. For ordinary packages, also compare archived `review.md` with canonical review bytes (premagic already does this). A PDF SHA256 in `paper-build.json` would bind the compiled PDF to its receipt, rather than relying only on equality to the current canonical PDF.
3. **Tighten replay receipt semantics.** `verify_archives.py` labels a successful subprocess/JSON result PASS without explicitly requiring `result['status']=='PASS'`; add that check and the expected theorem/declaration metadata. It executes the archived verifier by design, so it should not be treated as a safe verifier for arbitrary untrusted ZIPs. The actual current extension scripts/pins were checked, and preserved old script variants should be anchored to their accepted historical hashes rather than forcibly replaced with the latest bytes.

## Count and qualification labeling

No current duplicate-source inflation was found: there are 28 distinct positive integer MathDB IDs, and the count gate cannot produce a thirty-outcome collection from that state. The collection README explicitly includes known results and literal-source corrections and disclaims thirty discoveries. Its notice about the two arithmetic questions sharing one proof module is accurate infrastructure labeling. The current ledger/metadata retain the additive-count interpretation limitation, Fibonacci sampling-law limitation, printed-sign correction, known prior proofs, and symplectic-form transcription correction. I found no new infrastructure-level qualification mislabel. Semantic source fidelity remains the individual independent reviews' responsibility; this review does not re-audit those proofs.


## Parent final acceptance addendum

All thirty outcomes are now accepted and the final collector/readback passed. The ten new standalone archives were rebuilt from extracted sources; the last pair used the hardened fresh-directory extraction and exact replay status/theorem/declaration/source-hash checks. The collector now also anchors the original twenty IDs, package paths and archive hashes to their unchanged original ledger, compares archived reviews to canonical accepted bytes, and writes/readback-validates a temporary aggregate before atomic replacement. These are small hardening changes implementing the review's recommendations; no proof, paper, or accepted individual archive changed. The final count/duplicate/original-anchor mutation gates were tested and reject.

Original twenty aggregate SHA256 remains072f1ba954e4d31c5a9e3a5c82193bcfc4ab46828b425bb87296decc10a594b6. The final thirty aggregate SHA256 isd03b86529b036f4a2340ff213bbd51b2eb0170bfa444190001c5d9365fce63e1. All30 nested package bytes exactly match their accepted individual releases; final ZIP CRC and all manifest hashes pass.

The suggested future fresh individual staging/PDF-receipt hash enhancements are not needed to validate this release: each new outcome was packaged once into its own initially empty stage, and each PDF was independently rendered/inspected and byte-compared with its accepted canonical build. This acceptance concerns the present exact bytes and does not claim safety for arbitrary third-party ZIP execution.
