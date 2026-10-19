# Byte verification only

The outside-packet MANIFEST.json records exact file membership, SHA256, byte lengths, file modes, directory membership and directory modes. FINAL.json binds the manifest, report, pin, full-tree SHA256 and prefreeze/no-nominee status. The FINAL hash and report hash must come from the external handoff; the verifier never discovers a trusted anchor from the packet itself.

Run the inspected original verifier with Python3 and explicit arguments:

    python packet/public/verify.py --root /absolute/r117-directory \
      --tree /absolute/repository/sources/preprints-tree.json \
      --finalhash EXTERNALLY_SUPPLIED_FINAL_SHA256 \
      --reporthash EXTERNALLY_SUPPLIED_REPORT_SHA256

It reads only; it never writes, fetches, executes source material, or accepts mathematical assertions. It checks the actual complete tree bytes, all canonical source paths/raw URLs/Git blobs/SHA256, the primary PDF/text hashes and the recorded access failure. It rejects nonregular payloads, symlinks, hard links, missing/extra files or directories, and mode/hash mismatches. Context references identify other local files but are not recursively reverified or included as a giant historical snapshot. SHA256 authenticity depends on the caller retaining the trusted detached anchor and inspecting the verifier, rather than executing an arbitrary replacement program.

control_runner.py invokes that inspected original verifier against disposable copies contained in this owned directory's controls/working-copy. Each copy is removed after its case. It checks expected rejection reasons and compares the original packet and seals before/after. Cases cover absent/malformed/wrong anchors, modified or missing payloads, extra files/empty directories, links, modes, manifest/FINAL tampering, coherent resealing under an old external anchor, altered tree bytes, source/primary/verifier-copy mutations and clean positives. Actual results are outside the sealed packet in controls/results.json and their SHA256 is reported in the external handoff. The verifier is read-only; the control runner intentionally mutates disposable copies.

No integrity result certifies a theorem, a reading extent, originality, eligibility, contribution, correctness or campaign count. No numerical mathematical tests were used to make a gate decision.
