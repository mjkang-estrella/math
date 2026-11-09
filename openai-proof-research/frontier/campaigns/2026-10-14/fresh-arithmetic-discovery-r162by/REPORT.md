# R162BY detached artifact report

Author status: PREFREEZE/no nominee. No mathematical review gate or count.

FINAL SHA256: 7857b2433819fadab49d88ed3b9c2630966ee00cd9988718b4610e1ae2a0af52
MANIFEST SHA256: d8c635fc08abb4a849ad9ffde5a0f8cb453d97cfd4000a746cacf78bba2e36d7

Manifest path: private/MANIFEST.json. REPORT is outside the manifest payload and inside the exclusive root. Its own SHA256 is supplied in the external final handoff. All payload records are sorted and unique, with full file/directory modes.

The same read-only verifier logic was preflighted with these exact detached bytes before their one-time writes. Tiny copied controls rejected changed bytes, changed full mode, and extra membership; the fixture was restored before recording the payload. Five completed originals/copies retain their original bytes and permission bits; full st_mode was observed later at preseal and is not backdated.

Run from the authorized project workdir: python -B frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162by/verify.py --final <FINAL_SHA256> --manifest <MANIFEST_SHA256> --report <REPORT_SHA256>

The verifier checks exact safe membership, hashes,lengths,full modes,all pinned source blobs/reconstructed trees,5 completed original/copy pairs and5 primary PDFs. It performs no writes and assigns no mathematical verdict. No sealed payload may be changed to fit it.
