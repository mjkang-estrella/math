# Reading, search and execution limits

## Read in full

* `AGENTS.md` and `VALIDATION.md`
* The acceptance rules at the start of `frontier/NEW-TEN-2026-10-14.md` (lines 1–60)
* From `t205m-parent/`:
  * `formal-r1-dispatch.txt`
  * `formal-review-dispatch-r1.json`
  * `formal-v1-anchor.json`
  * `review-common-prepared.txt`
  * the first 30 lines of `formal-v1-integrity-controls.json`, plus a byte comparison of the whole file
* From the frozen packet `t205m-formal-v1/`:
  * `T205M.lean`, `Controls.lean` and `README.md`
  * `provenance.json` and `manifest.json`
  * `rebuild.py`, `verify.py` and `integrity_controls.py`
  * `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`
  * `validation/Checks.lean`, `validation/types-axioms.log` and `validation/receipt.json`
  * `inputs/parent-high-capacity.md`
* The diff of `t027o-formal-v1/rebuild.py` against the packet builder
* `agm063-formal-review-r1/seal.py`, read only as a format precedent

## Read in part

* `inputs/candidate205m.md`: lines 1–200 and 296–335, plus a keyword search for Lean and formal.
* `inputs/contribution-credit-addendum.md`: keyword search only.

## Not read

These were not read and were not re-adjudicated:

* `kostka-low-capacity-proof.md`
* the finite certificate and scripts of `fresh-arithmetic-discovery-r38`
* the `t205m-proof-r1` review body (only its manifest SHA256 was checked against `4b41e5dd…4343`)
* the `t205m-contribution-r1` review body
* the pinned upstream source manuscripts

No parallel reviewer draft was read. No web or literature search was made, and no network access was used.

## Execution limits

* Lean 4.34.1 (commit `5045d005…`), binary at `dlp-research/.tools/lean-4.34.1-linux/bin/lean`, SHA256 `e8baaa71…5550`.
* The shared dependency cache `frontier/campaigns/2026-10-14/formal/.lake/packages` was checked for its nine Git pins and tracked cleanliness. Its `.olean` objects are trusted, not rebuilt and not hashed.
* Kernel acceptance is relative to those objects.
* All writes were confined to this directory and to new `/var/tmp` directories. The main work directory was `/var/tmp/t205m-formal-review-r1-dwsl7i5c`.
* `run_review.py` regenerates `execution.json`, `builder-run/`, `independent-logs/` and `packet-integrity-controls.json`. Running it in place after sealing would break the seal, so rerun it on a copy.
