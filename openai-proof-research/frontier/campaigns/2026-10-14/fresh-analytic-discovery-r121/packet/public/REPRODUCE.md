# Integrity reproduction

Use Python3 with -B. Supply the FINAL SHA256 and report SHA256 from the detached HANDOFF or parent message, not values computed from a possibly altered packet:

    python -B packet/public/verify.py . --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256 --tree /home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json

MANIFEST.json and FINAL.json are outside packet. The manifest enumerates all packet files and directories exactly, including the verifier itself. FINAL binds the manifest and report. The verifier rejects symlinks/special files/hard links, checks exact membership, and authenticates source blobs against the fixed hash of the complete tree. Its runtime audit hook rejects write opens, filesystem mutations, network and subprocess operations. It performs no writes or downloads. Private source rights are unchanged.

`controls.py` is a separate mutation harness: it writes only copies under a specified directory inside the owned r121 work area, runs the COPIED verifier with detached anchors, and records receipts outside the sealed packet. The original packet/manifest/FINAL contents must remain identical. Work and postseal control receipts are not part of the sealed packet. They are supplementary evidence, not mathematical gates.
