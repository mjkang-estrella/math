# Read-only packet verification

Use the detached FINAL/MANIFEST/REPORT SHA256 values from the terminal handoff, not hashes freshly calculated from an untrusted packet. From the project root run:

    python -B frontier/campaigns/2026-10-14/fresh-analytic-discovery-r144/verify.py \
      frontier/campaigns/2026-10-14/fresh-analytic-discovery-r144 \
      --final DETACHED_FINAL_SHA256 \
      --manifest DETACHED_MANIFEST_SHA256 \
      --report DETACHED_REPORT_SHA256

The root MANIFEST.json enumerates every actual payload file, excluding exactly the root FINAL.md, MANIFEST.json and REPORT.md. These three outside envelopes are independently anchored in the handoff. Nested fixture envelopes are ordinary payload. The checker reads only; no downloads, extraction, writes, git or mathematical tests. It rejects a changed/missing payload, extra file, symlink and wrong envelope anchor. Empty directories, modes and hardlinks are outside its claims.

CONTROL-RESULTS.json records six preseal controls on a separately manifested one-file selection of original r144 prose: baseline/restored accept; changed/missing payload, hidden extra and wrong detached manifest reject. Each invocation preserved its fixture bytes. No protected source body was used for this fixture and no inherited original manifest was reused.

AUTH-RECHECK.json records separate source/copy authentication: canonical pinned sizes and Git blobs against the complete tree; primary incoming archive hashes; actual selected members matched to their archive bytes; selected local originals matched their earlier metadata records. Hash authentication is not proof reading.

Do not replay the acquisition, scan, control or sealing writers on the sealed root. They are saved as historical reproducibility code, not verification entrypoints. Artifact integrity is not a mathematical gate.
