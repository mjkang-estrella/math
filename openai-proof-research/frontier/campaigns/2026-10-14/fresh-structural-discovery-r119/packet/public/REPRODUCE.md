# Read-only authentication and bounded checks

Supply the detached SHA256 of FINAL.json from the handoff, not a value inferred from a copied packet:

    python3 -B packet/public/verify.py --root . --finalhash DETACHED_FINAL_SHA256

The verifier reads the outer FINAL.json, MANIFEST.json and REPORT.md, checks exact packet files/directories and byte identities, validates selected canonical Git blobs and pinned URLs, and rechecks the seven primary PDF/text pairs. It never writes or reseals. The complete upstream tree is represented by an authenticated selected-entry receipt and tree SHA256; online upstream authentication is not performed by this program.

Run the optional bounded rational diagnostic with:

    python3 -B packet/public/finite_checks.py

Its stdout should equal public/finite-results.json. It checks108 rational matrix pairs in dimensions3-5, including18 singular I+U cases and60 noncommuting pairs, for1080 displayed identities. It is not a proof of the tensor-ring statements or the Ramsey consequence.

The copied integrity control program is invoked after sealing:

    python3 -B packet/public/run_copied_controls.py --root . --finalhash DETACHED_FINAL_SHA256

It writes only temporary copies and receipts under controls/, outside packet. Thirteen scenarios cover an intact copy, missing/wrong anchor, changed/missing/extra payload, extra directory, file/directory symlinks, changed report/manifest/verifier, and coherent resealing against the old anchor. It compares the original packet and three anchors before and after. Integrity controls do not decide mathematical correctness, contribution or acceptance.
