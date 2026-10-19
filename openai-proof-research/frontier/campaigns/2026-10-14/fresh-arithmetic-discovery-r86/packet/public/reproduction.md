# Read-only authentication

Obtain FINAL.json and REPORT.md SHA256 anchors from the detached handoff, not by trusting values inside this packet. Run from any directory:

    python -B /absolute/r86/verify.py --root /absolute/r86 --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256 --tree /absolute/repository/sources/preprints-tree.json

The verifier does not generate or update a manifest. It checks exact packet file AND directory membership, regular singly linked files, the externally anchored FINAL, report and control-program bindings, complete canonical tree, pinned raw URL/blob identities and retained primary/history byte identities. It checks identity, not mathematical truth, rights grants or semantic completeness. The four operative primary originals have twelve derived/original artifact entries in total; all private material remains under original rights.

    python -B /absolute/r86/run_controls.py --root /absolute/r86 --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256 --tree /absolute/repository/sources/preprints-tree.json

Controls run on disposable copies inside the owned directory. They require rejection of missing/extraneous/changed payloads and directories, links and FIFO, wrong detached anchors, manifest/verifier/control/report mutations, coherent internal resealing under an unchanged external anchor, and a wrong canonical tree. They compare the whole original root before/after excluding only their temporary work directory, then delete that directory. The final receipt is outside packet and is not bound by FINAL; its hash is separately reported in FINAL-ANCHORS.json. No control establishes a mathematical gate.
