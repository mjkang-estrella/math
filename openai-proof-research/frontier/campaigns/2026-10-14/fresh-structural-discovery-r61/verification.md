# Read-only verification and exact scope

The final MANIFEST.json inventories every payload file and every directory, including private retained bodies. Its SHA256 is supplied externally to the parent after sealing; it is deliberately not embedded as an authority inside the packet. Run:

    python3 -B verify.py --expected-manifest-sha256 EXTERNAL_SHA256

The verifier rejects an incorrect caller anchor, changed/missing/extra payloads, an extra empty directory, root/payload symlinks, any nonregular node (including FIFO), multiply linked regular files, and nested MANIFEST.json files. It checks exact scope bytes, all31 retained canonical Git blobs against the selected complete-tree entries, pinned raw URLs, and two primary PDF/text identities. It is read-only. It authenticates a packet, not mathematical truth, semantic reading, novelty, independence, acceptance or full formalization.

checks/integrity-controls.json contains13 copied intermediate-packet controls, with expected rejection reasons checked. The scratch copies were deleted. This receipt was added only after those copied tests; the final manifest was regenerated afterward. A final positive and wrong-anchor run against the final exact inventory is performed before handing its hash externally to parent. Thus the copied controls do not pretend to contain their own final self-referential seal.

checks/extraction-replays.json records exact pdftotext -layout replays for both retained PDFs. checks/finite_diagnostics.py uses only the standard library, and its saved result records4096 alternation cases, a nonzero below-threshold control,2032 word/automaton cases with duplicate labels and prefix ambiguity, and six illustrative recurrence budgets. Replay with python3 -B checks/finite_diagnostics.py; compare JSON content. These finite checks prove none of the full compiler or theorem.

New source/compiler construction and coefficient filtration are proved in candidate.md, not by the integrity verifier. Original-scope.txt is frozen at SHA25619e05d71ce3cf0478d81ddbf1cf3aacc2f089f07fc5ddbdb6ae8a9dbc1b930c3. No scoped Lean implementation is included.
