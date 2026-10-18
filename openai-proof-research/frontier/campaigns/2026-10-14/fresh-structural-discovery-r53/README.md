# r53 read-only handoff

Read report.md, buc-mechanism.md and reading-limits.md. No nominee.
The unchanged full BUC scope is original-scope.txt, copied from r17.

Run `python -B verify.py --expected-manifest-sha256 EXTERNAL_HASH` with the
hash supplied independently by the author/parent. The verifier checks exact
files/directories, regular single-link files, payload hashes and recorded
source identities. It rejects links, nonregular nodes and unknown inventory.
It does not certify mathematics or novelty. private/ is ignored and must not
be staged or published. Checks may be rerun read-only with `python -B`.
